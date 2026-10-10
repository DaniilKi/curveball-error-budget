import FiniteProbability
import Mathlib.Data.Finset.Max

namespace CurveballVerified
open scoped BigOperators

def rankCount {ι : Type} [Fintype ι] (score : ι → Nat) (i : ι) : Nat :=
  (Finset.univ.filter (fun j => score i ≤ score j)).card

def smallRanks {ι : Type} [Fintype ι] (score : ι → Nat) (p q : Nat) : Finset ι :=
  Finset.univ.filter (fun i => rankCount score i * q ≤ p * Fintype.card ι)

/-- Deterministic conservative-tie rank counting, valid for every score vector. -/
theorem smallRanks_card {ι : Type} [Fintype ι] (score : ι → Nat) (p q : Nat) :
    (smallRanks score p q).card * q ≤ p * Fintype.card ι := by
  classical
  by_cases h : (smallRanks score p q).Nonempty
  · obtain ⟨i, hi, hmin⟩ := Finset.exists_min_image (smallRanks score p q) score h
    have hsub : smallRanks score p q ⊆ Finset.univ.filter (fun j => score i ≤ score j) := by
      intro j hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, hmin j hj⟩
    have hc := Nat.mul_le_mul_right q (Finset.card_le_card hsub)
    exact hc.trans (Finset.mem_filter.mp hi).2
  · have hz : smallRanks score p q = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp [hz]

noncomputable section

/-- Exchangeability is represented by equality of coordinate-event probabilities,
    not by assuming the desired p-value bound. IID sampling must establish this
    premise at the final sampler interface. -/
theorem conservative_rank_bound {Ω ι : Type} [Fintype Ω] [Fintype ι]
    (law : FiniteLaw Ω) (score : Ω → ι → Nat) (i0 : ι) (p q : Nat) (hq : 0 < q)
    (hexchange : ∀ i,
      eventMass law (fun x => rankCount (score x) i * q ≤ p * Fintype.card ι) =
      eventMass law (fun x => rankCount (score x) i0 * q ≤ p * Fintype.card ι)) :
    eventMass law (fun x => rankCount (score x) i0 * q ≤ p * Fintype.card ι)
      ≤ (p : ℝ) / q := by
  classical
  let E (i : ι) (x : Ω) := rankCount (score x) i * q ≤ p * Fintype.card ι
  have hpoint (x : Ω) :
      (∑ i, if E i x then (1 : ℝ) else 0) * q ≤ (p : ℝ) * Fintype.card ι := by
    have h := smallRanks_card (score x) p q
    have hc : (∑ i, if E i x then (1 : ℝ) else 0) = (smallRanks (score x) p q).card := by
      simp [smallRanks, E]
    rw [hc]
    exact_mod_cast h
  have hweighted := Finset.sum_le_sum (fun x (_ : x ∈ (Finset.univ : Finset Ω)) =>
    mul_le_mul_of_nonneg_left (hpoint x) (law.nonnegative x))
  have hleft : (∑ x, law.mass x * ((∑ i, if E i x then (1 : ℝ) else 0) * q)) =
      (Fintype.card ι : ℝ) *
        eventMass law (E i0) * q := by
    simp_rw [← mul_assoc, Finset.mul_sum]
    rw [← Finset.sum_mul, Finset.sum_comm]
    have he (i : ι) : (∑ x, law.mass x * (if E i x then (1 : ℝ) else 0)) =
        eventMass law (E i0) := by
      simpa [eventMass, E] using hexchange i
    simp_rw [he]
    simp
  have hright : (∑ x, law.mass x * ((p : ℝ) * Fintype.card ι)) =
      (p : ℝ) * Fintype.card ι := by
    rw [← Finset.sum_mul, law.normalized, one_mul]
  rw [hleft, hright] at hweighted
  have : Nonempty ι := ⟨i0⟩
  have hN : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  apply (le_div_iff₀ hqR).mpr
  nlinarith

#print axioms smallRanks_card
#print axioms conservative_rank_bound
end
end CurveballVerified
