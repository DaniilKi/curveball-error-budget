import NativeSamplingProtocol
import NativeChecks

/- Exact frozen CBSAMPLE1 entry-point boundary proof candidate.
   No declaration below changes the runtime or assumes a sampling law.
   Compilation is pending a coordinated slot. IO expression equalities preserve
   IO failures; they do not assert successful stdout writes or OS byte capture. -/
namespace CurveballNativeSamplingBoundary
open CurveballNative CurveballNativeSampling

/-- Acceptance of the actual permissive decoder is guarded by exact re-encoding,
    actual resource limits and graph validation. This is a decoded String claim. -/
theorem parse_success {wire : String} {r : Request}
    (hp : parse wire = some r) :
    decodeCandidate wire = some r ∧ encode r = wire ∧
      wire.length ≤ 4096 ∧ withinLimits r = true := by
  by_cases hl : wire.length > 4096
  · simp [parse, hl] at hp
  · cases hd : decodeCandidate wire with
    | none => simp [parse, hl, hd] at hp
    | some c =>
      by_cases hg : encode c = wire ∧ wire.length ≤ 4096 ∧ withinLimits c = true
      · have hs : some c = some r := by simpa [parse, hl, hd, hg] using hp
        have he : c = r := Option.some.inj hs
        exact ⟨by simpa [he] using hd, by simpa [he] using hg⟩
      · simp [parse, hl, hd, hg] at hp

/-- Byte canonicality for the UTF-8 representation of the accepted decoded
    String. The OS/argv decoder bridge remains a separate explicit premise. -/
theorem parse_success_utf8 {wire : String} {r : Request}
    (hp : parse wire = some r) : wire.toUTF8 = (encode r).toUTF8 := by
  exact congrArg String.toUTF8 (parse_success hp).2.1.symm

theorem parse_rejects_noncanonical {wire : String}
    (h : ∀ r : Request, encode r ≠ wire) : parse wire = none := by
  cases hp : parse wire with
  | none => rfl
  | some r => exact False.elim (h r (parse_success hp).2.1)

def RequestCaps (r : Request) : Prop :=
  4 ≤ r.n ∧ r.n ≤ 26 ∧ 0 < r.b ∧ r.b ≤ 32 ∧
    0 < r.trades ∧ r.trades ≤ 1024 ∧ r.k ≤ 4096 ∧
    0 < r.cap ∧ r.cap ≤ 128 ∧ r.p ≤ 1000000000000 ∧ r.q ≤ 1000000000000 ∧
    r.etaNum ≤ 1000000000000 ∧ r.etaDen ≤ 1000000000000 ∧
    r.alphaNum ≤ 1000000000000 ∧ r.alphaDen ≤ 1000000000000 ∧
    entropyBytes r ≤ 262144

theorem withinLimits_success {r : Request} (h : withinLimits r = true) :
    RequestCaps r ∧ graphValid r.n r.edges = true := by
  simpa [withinLimits, RequestCaps] using h

theorem parse_validates_graph {wire : String} {r : Request}
    (hp : parse wire = some r) :
    RequestCaps r ∧ r.edges.Nodup ∧
      (∀ e ∈ r.edges, e.1 < e.2 ∧ e.2 < r.n) := by
  have hv := withinLimits_success (parse_success hp).2.2.2
  have hg := (graphValid_iff r.n r.edges).mp hv.2
  exact ⟨hv.1, hg.2.1, hg.2.2⟩

theorem parse_rejects_invalid_graph {wire : String}
    (h : ∀ r : Request, decodeCandidate wire = some r → graphValid r.n r.edges = false) :
    parse wire = none := by
  cases hp : parse wire with
  | none => rfl
  | some r =>
    have hs := parse_success hp
    have hv := (withinLimits_success hs.2.2.2).2
    have hf := h r hs.1
    simp [hf] at hv

def ArithmeticConstraints (r : Request) : Prop :=
  0 < r.etaDen ∧ 0 < r.alphaDen ∧ 0 < r.alphaNum ∧
    r.alphaNum < r.alphaDen ∧ r.etaNum*r.alphaDen < r.alphaNum*r.etaDen ∧
    r.b*r.p*r.etaDen ≤ r.etaNum*r.q

theorem arithmeticPlan_success {r : Request} (h : arithmeticPlan r = true) :
    budgetCheck r.n r.edges.length r.p r.q r.k r.trades = true ∧
      ArithmeticConstraints r := by
  simpa [arithmeticPlan, ArithmeticConstraints] using h

/-- The exact native integer checker is exposed, not a translated budget model. -/
theorem arithmeticPlan_native_budget {r : Request} (h : arithmeticPlan r = true) :
    0 < r.p ∧ 2*r.p < r.q ∧ r.edges.length ≤ choose r.n 2 ∧
    r.trades = choose r.n 2*r.k ∧
    choose (choose r.n 2) r.edges.length*r.q^2 ≤ 4*r.p^2*2^(2*r.k) := by
  simpa [budgetCheck] using (arithmeticPlan_success h).1

structure ResultFields where
  n : Nat
  m : Nat
  trades : Nat
  replicates : Nat
  attempted : Nat
  observed : Nat
  exceed : Nat
  budget : Bool
  rank : Bool
  stats : List Nat
  graphs : List Edges

def computedFields (r : Request) (outs : List Edges) (count : Nat) : ResultFields :=
  let observed := triangles r.n r.edges
  let stats := outs.map (triangles r.n)
  let exceed := (stats.filter fun s => decide (observed ≤ s)).length
  ⟨r.n, r.edges.length, r.trades, r.b, count, observed, exceed,
    budgetCheck r.n r.edges.length r.p r.q r.k r.trades,
    rankCheck r.b exceed r.etaNum r.etaDen r.alphaNum r.alphaDen, stats, outs⟩

def encodeFields (f : ResultFields) : String :=
  let statsWire := String.intercalate "," (f.stats.map toString)
  let graphsWire := String.intercalate ";" (f.graphs.map encodeEdges)
  s!"CBSAMPLE1 result {f.n} {f.m} {f.trades} {f.replicates} {f.attempted} {f.observed} {f.exceed} {if f.budget then "true" else "false"} {if f.rank then "true" else "false"} {statsWire} {graphsWire}\n"

/-- Definitional refinement of the actual renderer to every computed field. -/
theorem render_exact_fields (r : Request) (outs : List Edges) (count : Nat) :
    render r outs count = encodeFields (computedFields r outs count) := by
  rfl

theorem fields_statistics (r : Request) (outs : List Edges) (count : Nat) :
    (computedFields r outs count).observed = triangles r.n r.edges ∧
    (computedFields r outs count).stats = outs.map (triangles r.n) ∧
    (computedFields r outs count).exceed =
      ((outs.map (triangles r.n)).filter fun s => decide (triangles r.n r.edges ≤ s)).length := by
  exact ⟨rfl, rfl, rfl⟩

theorem fields_complete_lengths {r : Request} {outs : List Edges} {count : Nat}
    (h : outs.length = r.b) :
    (computedFields r outs count).stats.length = r.b ∧
      (computedFields r outs count).graphs.length = r.b := by
  simp [computedFields, h]

theorem fields_exceed_le {r : Request} {outs : List Edges} {count : Nat}
    (h : outs.length = r.b) : (computedFields r outs count).exceed ≤ r.b := by
  simpa [computedFields, h] using
    List.length_filter_le (fun s => decide (triangles r.n r.edges ≤ s))
      (outs.map (triangles r.n))

theorem fields_rank_correspondence (r : Request) (outs : List Edges) (count : Nat) :
    (computedFields r outs count).rank =
      rankCheck r.b (computedFields r outs count).exceed
        r.etaNum r.etaDen r.alphaNum r.alphaDen := by
  rfl

theorem fields_budget_preflight {r : Request} (outs : List Edges) (count : Nat)
    (h : arithmeticPlan r = true) : (computedFields r outs count).budget = true := by
  exact (arithmeticPlan_success h).1

/-- Rendered ranktrue implies the actual native conservative integer cutoff.
    This is an arithmetic event correspondence, never a probability guarantee. -/
theorem fields_rank_cutoff {r : Request} {outs : List Edges} {count : Nat}
    (h : (computedFields r outs count).rank = true) :
    let e := (computedFields r outs count).exceed
    0 < r.b ∧ e ≤ r.b ∧ 0 < r.etaDen ∧ 0 < r.alphaDen ∧
    0 < r.alphaNum ∧ r.alphaNum < r.alphaDen ∧
    r.etaNum*r.alphaDen < r.alphaNum*r.etaDen ∧
    (e+1)*r.alphaDen*r.etaDen + (r.b+1)*r.etaNum*r.alphaDen
      ≤ r.alphaNum*(r.b+1)*r.etaDen := by
  rw [fields_rank_correspondence] at h
  simpa [rankCheck] using h

structure Reply where
  text : String
  exitCode : UInt32

inductive Failure where
  | malformed | arguments | plan | entropySize | draw | incomplete | io

def failureReply : Failure → Reply
  | .malformed => ⟨"CBSAMPLE1 error malformed-request\n", 2⟩
  | .arguments => ⟨"CBSAMPLE1 error argument-count\n", 2⟩
  | .plan => ⟨"CBSAMPLE1 error invalid-arithmetic-plan\n", 2⟩
  | .entropySize => ⟨"CBSAMPLE1 error entropy-size\n", 3⟩
  | .draw => ⟨"CBSAMPLE1 error entropy-or-draw\n", 3⟩
  | .incomplete => ⟨"CBSAMPLE1 error incomplete-batch\n", 3⟩
  | .io => ⟨"CBSAMPLE1 error io-failure\n", 4⟩

def completionGuard (r : Request) (outs : List Edges) (count : Nat) (rest : List Bool) : Bool :=
  !rest.isEmpty || outs.length != r.b || count != r.b*r.trades

def completionReply (r : Request) (outs : List Edges) (count : Nat) (rest : List Bool) : Reply :=
  if completionGuard r outs count rest then failureReply .incomplete
  else ⟨render r outs count, 0⟩

def tapeReply (r : Request) (bytes : ByteArray) : Reply :=
  if bytes.size != entropyBytes r then failureReply .entropySize
  else match batch r r.b (bytesBits bytes) with
  | none => failureReply .draw
  | some (outs,count,rest) => completionReply r outs count rest

theorem failureReply_nonzero (e : Failure) : (failureReply e).exitCode ≠ 0 := by
  cases e <;> decide

/-- A success exit code is a necessary receiving-boundary condition. Thus these
    failures cannot supply an admissible rejection output, regardless of rank
    text or any later statistical theorem. This is not a proof of Python/OS I/O. -/
def AdmissibleRankOutput (r : Request) (outs : List Edges) (reply : Reply) : Prop :=
  reply.exitCode = 0 ∧ outs.length = r.b ∧ reply.text = render r outs (r.b*r.trades) ∧
    budgetCheck r.n r.edges.length r.p r.q r.k r.trades = true ∧
    (computedFields r outs (r.b*r.trades)).rank = true

theorem errors_not_admissible (r : Request) (outs : List Edges) (e : Failure) :
    ¬ AdmissibleRankOutput r outs (failureReply e) := by
  intro h
  exact failureReply_nonzero e h.1

theorem completionReply_success_iff (r : Request) (outs : List Edges) (count : Nat)
    (rest : List Bool) :
    (completionReply r outs count rest).exitCode = 0 ↔
      completionGuard r outs count rest = false := by
  cases hg : completionGuard r outs count rest <;>
    simp [completionReply, hg, failureReply] <;> decide

theorem completionGuard_valid {r : Request} {outs : List Edges} {count : Nat}
    {rest : List Bool} (h : completionGuard r outs count rest = false) :
    rest.isEmpty = true ∧ outs.length = r.b ∧ count = r.b*r.trades := by
  simpa [completionGuard, and_assoc] using h

theorem completionReply_success_fields {r : Request} {outs : List Edges} {count : Nat}
    {rest : List Bool} (h : (completionReply r outs count rest).exitCode = 0) :
    rest.isEmpty = true ∧ outs.length = r.b ∧ count = r.b*r.trades ∧
    (completionReply r outs count rest).text =
      encodeFields (computedFields r outs (r.b*r.trades)) := by
  have hg := (completionReply_success_iff r outs count rest).mp h
  have hv := completionGuard_valid hg
  refine ⟨hv.1, hv.2.1, hv.2.2, ?_⟩
  have ht : (completionReply r outs count rest).text =
      encodeFields (computedFields r outs count) := by
    simp [completionReply, hg, render_exact_fields]
  simpa only [hv.2.2] using ht

theorem tapeReply_success {r : Request} {bytes : ByteArray}
    (h : (tapeReply r bytes).exitCode = 0) :
    bytes.size = entropyBytes r ∧
    ∃ outs count rest, batch r r.b (bytesBits bytes) = some (outs,count,rest) ∧
      rest.isEmpty = true ∧ outs.length = r.b ∧ count = r.b*r.trades ∧
      (tapeReply r bytes).text = encodeFields (computedFields r outs (r.b*r.trades)) := by
  by_cases hs : bytes.size != entropyBytes r
  · have he : (failureReply .entropySize).exitCode = 0 := by simpa [tapeReply, hs] using h
    exact False.elim (failureReply_nonzero .entropySize he)
  · have hsize : bytes.size = entropyBytes r := by simpa using hs
    cases hb : batch r r.b (bytesBits bytes) with
    | none =>
      have he : (failureReply .draw).exitCode = 0 := by simpa [tapeReply, hs, hb] using h
      exact False.elim (failureReply_nonzero .draw he)
    | some x =>
      rcases x with ⟨outs,count,rest⟩
      have hc : (completionReply r outs count rest).exitCode = 0 := by
        simpa [tapeReply, hs, hb] using h
      have hv := completionReply_success_fields hc
      refine ⟨hsize, outs, count, rest, rfl, hv.1, hv.2.1, hv.2.2.1, ?_⟩
      simpa [tapeReply, hs, hb] using hv.2.2.2

/-- Calls the actual compiler-generated local loop of the frozen main. This
    avoids unfolding a duplicated loop at fuel262145 merely to prove equality.
    It is proof-only; the runtime keeps its original implementation. -/
def readTape (entropyPath : String) : IO ByteArray :=
  IO.FS.withFile entropyPath .read fun h => _root_.main.loop h 262145 ByteArray.empty

def writeReply (stdout : IO.FS.Stream) (reply : Reply) : IO UInt32 := do
  stdout.putStr reply.text
  return reply.exitCode

/-- Exact post-read continuation from main, preserving write failures. -/
def writeTapeResult (stdout : IO.FS.Stream) (r : Request) (bytes : ByteArray) : IO UInt32 := do
  if bytes.size != entropyBytes r then
    stdout.putStr "CBSAMPLE1 error entropy-size\n"; return 3
  match batch r r.b (bytesBits bytes) with
  | none => stdout.putStr "CBSAMPLE1 error entropy-or-draw\n"; return 3
  | some (outs,count,rest) =>
    if !rest.isEmpty || outs.length != r.b || count != r.b*r.trades then
      stdout.putStr "CBSAMPLE1 error incomplete-batch\n"; return 3
    stdout.putStr (render r outs count)
    return 0

theorem writeTapeResult_exact_reply (stdout : IO.FS.Stream) (r : Request)
    (bytes : ByteArray) :
    writeTapeResult stdout r bytes = writeReply stdout (tapeReply r bytes) := by
  by_cases hs : bytes.size != entropyBytes r
  · simp [writeTapeResult, writeReply, tapeReply, hs, failureReply]
  · cases hb : batch r r.b (bytesBits bytes) with
    | none => simp [writeTapeResult, writeReply, tapeReply, hs, hb, failureReply]
    | some x =>
      rcases x with ⟨outs,count,rest⟩
      cases hg : completionGuard r outs count rest <;>
        simp only [completionGuard] at hg <;>
        simp [writeTapeResult, writeReply, tapeReply, completionReply, hs, hb,
          completionGuard, hg, failureReply]

/-- Actual main program equality, not equality of a replacement probabilistic
    model. It retains getStdout, the read/close operation, and the IO catch. -/
theorem main_validated {wire entropyPath : String} {r : Request}
    (hp : parse wire = some r) (ha : arithmeticPlan r = true) :
    _root_.main [wire,entropyPath] = (do
      let stdout ← IO.getStdout
      try
        let bytes ← readTape entropyPath
        if bytes.size != entropyBytes r then
          stdout.putStr "CBSAMPLE1 error entropy-size\n"; return 3
        match batch r r.b (bytesBits bytes) with
        | none => stdout.putStr "CBSAMPLE1 error entropy-or-draw\n"; return 3
        | some (outs,count,rest) =>
          if !rest.isEmpty || outs.length != r.b || count != r.b*r.trades then
            stdout.putStr "CBSAMPLE1 error incomplete-batch\n"; return 3
          stdout.putStr (render r outs count)
          return 0
      catch _ =>
        stdout.putStr "CBSAMPLE1 error io-failure\n"; return 4) := by
  simp only [_root_.main, hp, ha, Bool.not_true, Bool.false_eq_true, ite_false]
  rfl

theorem main_validated_exact_fields {wire entropyPath : String} {r : Request}
    (hp : parse wire = some r) (ha : arithmeticPlan r = true) :
    _root_.main [wire,entropyPath] = (do
      let stdout ← IO.getStdout
      try
        let bytes ← readTape entropyPath
        if bytes.size != entropyBytes r then
          stdout.putStr "CBSAMPLE1 error entropy-size\n"; return 3
        match batch r r.b (bytesBits bytes) with
        | none => stdout.putStr "CBSAMPLE1 error entropy-or-draw\n"; return 3
        | some (outs,count,rest) =>
          if !rest.isEmpty || outs.length != r.b || count != r.b*r.trades then
            stdout.putStr "CBSAMPLE1 error incomplete-batch\n"; return 3
          stdout.putStr (encodeFields (computedFields r outs count))
          return 0
      catch _ =>
        stdout.putStr "CBSAMPLE1 error io-failure\n"; return 4) := by
  rw [main_validated hp ha]
  simp only [render_exact_fields]

theorem main_malformed {wire entropyPath : String} (hp : parse wire = none) :
    _root_.main [wire,entropyPath] = (do
      let stdout ← IO.getStdout
      writeReply stdout (failureReply .malformed)) := by
  simp only [_root_.main, hp]
  rfl

theorem main_plan_failure {wire entropyPath : String} {r : Request}
    (hp : parse wire = some r) (ha : arithmeticPlan r = false) :
    _root_.main [wire,entropyPath] = (do
      let stdout ← IO.getStdout
      writeReply stdout (failureReply .plan)) := by
  simp only [_root_.main, hp, ha, Bool.not_false, ite_true]
  rfl

theorem main_no_arguments : _root_.main [] = (do
    let stdout ← IO.getStdout
    writeReply stdout (failureReply .arguments)) := by rfl

theorem main_one_argument (wire : String) : _root_.main [wire] = (do
    let stdout ← IO.getStdout
    writeReply stdout (failureReply .arguments)) := by rfl

theorem main_extra_arguments (a b c : String) (rest : List String) :
    _root_.main (a::b::c::rest) = (do
      let stdout ← IO.getStdout
      writeReply stdout (failureReply .arguments)) := by rfl

#print axioms parse_success
#print axioms parse_success_utf8
#print axioms parse_validates_graph
#print axioms arithmeticPlan_native_budget
#print axioms render_exact_fields
#print axioms fields_rank_cutoff
#print axioms errors_not_admissible
#print axioms tapeReply_success
#print axioms writeTapeResult_exact_reply
#print axioms main_validated_exact_fields
#print axioms main_malformed
#print axioms main_plan_failure
end CurveballNativeSamplingBoundary
