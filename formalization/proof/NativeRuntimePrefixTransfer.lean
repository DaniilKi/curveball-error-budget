import NativeEntropyPrefixTransfer
import NativeSamplingBoundary

/- Proof-only affected runtime definitions with the exact optimized reserved
   decoder inserted. Request/parser/guards/statistic/replay remain the frozen
   imported definitions. The unchanged actual generated IO read loop is reused.
   This is not a native build. SOURCE ONLY until accepted receipts exist. -/
namespace CurveballNativeSamplingPrefix
open CurveballNative CurveballNativeSampling CurveballNativeSamplingBoundary

def draw (r : Request) (es : Edges) (bits : List Bool) :
    Option (Draw × List Bool) := do
  let (pairRank,rest) ← CurveballNativePrefixModel.drawBelowReserved (choose r.n 2)
    (wordWidth (choose r.n 2)) r.cap (pairReserve r) bits
  let (i,j) ← unrankPair r.n pairRank
  let pool := exclusive r.n es i j
  let wanted := (left r.n es i j).length
  let bound := choose pool.length wanted
  let (subsetRank,rest') ← CurveballNativePrefixModel.drawBelowReserved bound (wordWidth bound)
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


theorem draw_eq_frozen (r : Request) (es : Edges) (bits : List Bool) :
    draw r es bits = CurveballNativeSampling.draw r es bits := by
  simp only [draw, CurveballNativeSampling.draw,
    CurveballNativePrefixModel.drawBelowReserved_eq_frozen]

theorem generateTrace_eq_frozen (r : Request) (t : Nat) (es : Edges) (bits : List Bool) :
    generateTrace r t es bits = CurveballNativeSampling.generateTrace r t es bits := by
  induction t generalizing es bits with
  | zero => rfl
  | succ t ih =>
    simp only [generateTrace, CurveballNativeSampling.generateTrace, draw_eq_frozen, ih]

theorem oneChain_eq_frozen (r : Request) (bits : List Bool) :
    oneChain r bits = CurveballNativeSampling.oneChain r bits := by
  simp only [oneChain, CurveballNativeSampling.oneChain, generateTrace_eq_frozen]

theorem batch_eq_frozen (r : Request) (b : Nat) (bits : List Bool) :
    batch r b bits = CurveballNativeSampling.batch r b bits := by
  induction b generalizing bits with
  | zero => rfl
  | succ b ih =>
    simp only [batch, CurveballNativeSampling.batch, oneChain_eq_frozen, ih]

def mainOptimized (args : List String) : IO UInt32 := do
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
        let bytes ← IO.FS.withFile entropyPath .read fun h =>
          _root_.main.loop h 262145 ByteArray.empty
        if bytes.size != CurveballNativeSampling.entropyBytes r then
          stdout.putStr "CBSAMPLE1 error entropy-size\n"; return 3
        match CurveballNativeSamplingPrefix.batch r r.b (CurveballNativeSampling.bytesBits bytes) with
        | none => stdout.putStr "CBSAMPLE1 error entropy-or-draw\n"; return 3
        | some (outs,count,rest) =>
          if !rest.isEmpty || outs.length != r.b || count != r.b*r.trades then
            stdout.putStr "CBSAMPLE1 error incomplete-batch\n"; return 3
          stdout.putStr (CurveballNativeSampling.render r outs count)
          return 0
      catch _ => stdout.putStr "CBSAMPLE1 error io-failure\n"; return 4
  | _ => stdout.putStr "CBSAMPLE1 error argument-count\n"; return 2

/-- Equality of complete IO expressions, retaining parser/read/write/error paths.
    It is not a theorem of physical OS behavior or compiler correctness. -/
theorem mainOptimized_eq_frozen (args : List String) :
    mainOptimized args = _root_.main args := by
  unfold mainOptimized _root_.main
  simp only [batch_eq_frozen] <;> rfl

def tapeReplyPrefix (r : Request) (bytes : ByteArray) : Reply :=
  if bytes.size != entropyBytes r then failureReply .entropySize
  else match batch r r.b (bytesBits bytes) with
  | none => failureReply .draw
  | some (outs,count,rest) => completionReply r outs count rest

theorem tapeReplyPrefix_eq_frozen (r : Request) (bytes : ByteArray) :
    tapeReplyPrefix r bytes = tapeReply r bytes := by
  simp only [tapeReplyPrefix, tapeReply, batch_eq_frozen] <;> rfl

#print axioms draw_eq_frozen
#print axioms generateTrace_eq_frozen
#print axioms oneChain_eq_frozen
#print axioms batch_eq_frozen
#print axioms mainOptimized_eq_frozen
#print axioms tapeReplyPrefix_eq_frozen
end CurveballNativeSamplingPrefix
