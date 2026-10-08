import NativeGraph
import NativeEntropy
import NativeSubset
import NativeReplay

/- Source-only interface draft. No compilation or theorem acceptance is claimed.
Accepted core definitions are called directly; Mathlib proofs are never linked.
Every output remains outside scientific/TV assurance until full law composition. -/
namespace CurveballNativeSampling
open CurveballNative

structure Request where
  n : Nat
  p : Nat
  q : Nat
  k : Nat
  trades : Nat
  b : Nat
  cap : Nat
  etaNum : Nat
  etaDen : Nat
  alphaNum : Nat
  alphaDen : Nat
  edges : Edges
deriving Repr

def encodeEdges (es : Edges) : String :=
  if es.isEmpty then "_" else String.intercalate "," (es.map fun e => s!"{e.1}:{e.2}")

def encode (r : Request) : String :=
  s!"CBSAMPLE1 sample {r.n} {r.p} {r.q} {r.k} {r.trades} {r.b} {r.cap} {r.etaNum} {r.etaDen} {r.alphaNum} {r.alphaDen} {encodeEdges r.edges}\n"

def parseEdge (s : String) : Option (Nat × Nat) := do
  match s.splitOn ":" with
  | [u,v] => pure (← u.toNat?, ← v.toNat?)
  | _ => none

def parseEdges (s : String) : Option Edges :=
  if s = "_" then some [] else (s.splitOn ",").mapM parseEdge

-- A bounded linear width search avoids a division/recursion theorem in the draft.
-- n<=26 makes every pair/subset bound strictly below 2^32.
def wordWidth (bound : Nat) : Nat :=
  ((List.range 33).find? fun w => decide (bound ≤ 2^w)).getD 33

def pairReserve (r : Request) : Nat :=
  8 * ((wordWidth (choose r.n 2) * r.cap + 7) / 8)

def subsetReserve (r : Request) : Nat :=
  8 * ((wordWidth (choose (r.n-2) ((r.n-2)/2)) * r.cap + 7) / 8)

def entropyBytes (r : Request) : Nat :=
  r.b * r.trades * ((pairReserve r + subsetReserve r) / 8)

def withinLimits (r : Request) : Bool :=
  decide (4 ≤ r.n ∧ r.n ≤ 26 ∧ 0 < r.b ∧ r.b ≤ 32 ∧
    0 < r.trades ∧ r.trades ≤ 1024 ∧ r.k ≤ 4096 ∧
    0 < r.cap ∧ r.cap ≤ 128 ∧ r.p ≤ 1000000000000 ∧ r.q ≤ 1000000000000 ∧
    r.etaNum ≤ 1000000000000 ∧ r.etaDen ≤ 1000000000000 ∧
    r.alphaNum ≤ 1000000000000 ∧ r.alphaDen ≤ 1000000000000 ∧
    entropyBytes r ≤ 262144) && graphValid r.n r.edges

def decodeCandidate (wire : String) : Option Request := do
  match wire.trimAscii.toString.splitOn " " with
  | ["CBSAMPLE1","sample",n,p,q,k,t,b,c,en,ed,an,ad,es] =>
    pure ⟨← n.toNat?, ← p.toNat?, ← q.toNat?, ← k.toNat?, ← t.toNat?,
      ← b.toNat?, ← c.toNat?, ← en.toNat?, ← ed.toNat?, ← an.toNat?,
      ← ad.toNat?, ← parseEdges es⟩
  | _ => none

def parse (wire : String) : Option Request := do
  if wire.length > 4096 then none else pure ()
  let r ← decodeCandidate wire
  if encode r = wire ∧ wire.length ≤ 4096 ∧ withinLimits r = true then some r else none

def arithmeticPlan (r : Request) : Bool :=
  budgetCheck r.n r.edges.length r.p r.q r.k r.trades &&
  decide (0 < r.etaDen ∧ 0 < r.alphaDen ∧ 0 < r.alphaNum ∧
    r.alphaNum < r.alphaDen ∧ r.etaNum*r.alphaDen < r.alphaNum*r.etaDen ∧
    r.b*r.p*r.etaDen ≤ r.etaNum*r.q)

def bytesBits (bytes : ByteArray) : List Bool :=
  bytes.toList.flatMap fun byte =>
    (List.range 8).map fun bit => decide ((byte.toNat / 2^bit) % 2 = 1)

-- State-dependent subset width uses a globally fixed reservation. Rejected
-- words and padding are discarded by the accepted drawBelowReserved definition.
def draw (r : Request) (es : Edges) (bits : List Bool) :
    Option (Draw × List Bool) := do
  let (pairRank,rest) ← drawBelowReserved (choose r.n 2)
    (wordWidth (choose r.n 2)) r.cap (pairReserve r) bits
  let (i,j) ← unrankPair r.n pairRank
  let pool := exclusive r.n es i j
  let wanted := (left r.n es i j).length
  let bound := choose pool.length wanted
  let (subsetRank,rest') ← drawBelowReserved bound (wordWidth bound)
    r.cap (subsetReserve r) rest
  let chosen ← unrankSubset pool wanted subsetRank
  pure (⟨i,j,chosen⟩,rest')

-- Generation executes the accepted trade to obtain the next state's pool.
-- Returning the complete draw trace permits the accepted replay to be executed
-- separately below. No attempted trade is filtered out when it changes no edge.
def generateTrace (r : Request) : Nat → Edges → List Bool →
    Option (List Draw × Edges × List Bool)
  | 0, es, bits => some ([],es,bits)
  | t+1, es, bits => do
    let (d,rest) ← draw r es bits
    let next ← trade r.n es d.first d.second d.chosen
    let (ds,last,unused) ← generateTrace r t next rest
    pure (d::ds,last,unused)

def oneChain (r : Request) (bits : List Bool) : Option (Edges × Nat × List Bool) := do
  let (draws,generated,rest) ← generateTrace r r.trades r.edges bits
  let (out,count) ← replay r.n r.edges draws
  if out = generated ∧ count = r.trades then some (out,count,rest) else none

def batch (r : Request) : Nat → List Bool → Option (List Edges × Nat × List Bool)
  | 0, bits => some ([],0,bits)
  | b+1, bits => do
    let (out,count,rest) ← oneChain r bits
    let (outs,total,unused) ← batch r b rest
    pure (out::outs,count+total,unused)

def render (r : Request) (outs : List Edges) (count : Nat) : String :=
  let observed := triangles r.n r.edges
  let stats := outs.map (triangles r.n)
  let exceed := (stats.filter fun s => decide (observed ≤ s)).length
  let budget := budgetCheck r.n r.edges.length r.p r.q r.k r.trades
  let rank := rankCheck r.b exceed r.etaNum r.etaDen r.alphaNum r.alphaDen
  let statsWire := String.intercalate "," (stats.map toString)
  let graphsWire := String.intercalate ";" (outs.map encodeEdges)
  s!"CBSAMPLE1 result {r.n} {r.edges.length} {r.trades} {r.b} {count} {observed} {exceed} {if budget then "true" else "false"} {if rank then "true" else "false"} {statsWire} {graphsWire}\n"

end CurveballNativeSampling

def main (args : List String) : IO UInt32 := do
  let stdout ← IO.getStdout
  match args with
  | [wire,entropyPath] =>
    match CurveballNativeSampling.parse wire with
    | none => stdout.putStr "CBSAMPLE1 error malformed-request\n"; return 2
    | some r =>
      if !CurveballNativeSampling.arithmeticPlan r then
        stdout.putStr "CBSAMPLE1 error invalid-arithmetic-plan\n"; return 2
      try
        -- Regular private files only by launcher contract. Bounded read loops
        -- handle short reads without treating them as successful full entropy.
        let bytes ← IO.FS.withFile entropyPath .read fun h => do
          let rec loop : Nat → ByteArray → IO ByteArray
            | 0, acc => pure acc
            | fuel+1, acc => do
              let chunk ← h.read (262145-acc.size).toUSize
              if chunk.isEmpty || acc.size+chunk.size ≥ 262145 then pure (acc ++ chunk)
              else loop fuel (acc ++ chunk)
          loop 262145 ByteArray.empty
        if bytes.size != CurveballNativeSampling.entropyBytes r then
          stdout.putStr "CBSAMPLE1 error entropy-size\n"; return 3
        match CurveballNativeSampling.batch r r.b (CurveballNativeSampling.bytesBits bytes) with
        | none => stdout.putStr "CBSAMPLE1 error entropy-or-draw\n"; return 3
        | some (outs,count,rest) =>
          if !rest.isEmpty || outs.length != r.b || count != r.b*r.trades then
            stdout.putStr "CBSAMPLE1 error incomplete-batch\n"; return 3
          stdout.putStr (CurveballNativeSampling.render r outs count)
          return 0
      catch _ => stdout.putStr "CBSAMPLE1 error io-failure\n"; return 4
  | _ => stdout.putStr "CBSAMPLE1 error argument-count\n"; return 2
