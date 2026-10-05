import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Levels.PLBandCutoff

/-!
# Local PL scalar operations for the original defining cut

Affine postcomposition, finite common refinements and finite sums
preserve the actual open coordinate domains. See Hudson 1969,
pp. 12--17, and M76 Dehn derivation 006.
-/

set_option autoImplicit false

open Set
open scoped BigOperators

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {f g : E → ℝ} {U : Set E}

/-- Negation retains the full local PL source.
See Hudson pp. 15--17 and Dehn derivation 006. -/
theorem LocallyPiecewiseAffineOn.neg (hf : LocallyPiecewiseAffineOn f U) :
    LocallyPiecewiseAffineOn (fun x => -f x) U := by
  let a := (-ContinuousLinearMap.id ℝ ℝ).toContinuousAffineMap
  have h := (locallyPiecewiseAffineOn_affine a isOpen_univ).comp hf
  rw [preimage_univ, inter_univ] at h
  exact h.congr (fun _ _ => rfl)

/-- Addition uses the actual common source and finite refinements.
See Hudson pp. 12--17 and Dehn derivation 006. -/
theorem LocallyPiecewiseAffineOn.add (hf : LocallyPiecewiseAffineOn f U)
    (hg : LocallyPiecewiseAffineOn g U) :
    LocallyPiecewiseAffineOn (fun x => f x + g x) U := by
  let a := (ContinuousLinearMap.fst ℝ ℝ ℝ +
    ContinuousLinearMap.snd ℝ ℝ ℝ).toContinuousAffineMap
  have h := (locallyPiecewiseAffineOn_affine a isOpen_univ).comp (hf.prod_mk hg)
  rw [preimage_univ, inter_univ] at h
  exact h.congr (fun _ _ => rfl)

/-- Minimum retains the equality locus and the complete open source.
See Hudson pp. 12--17 and Dehn derivation 006. -/
theorem LocallyPiecewiseAffineOn.min (hf : LocallyPiecewiseAffineOn f U)
    (hg : LocallyPiecewiseAffineOn g U) :
    LocallyPiecewiseAffineOn (fun x => min (f x) (g x)) U := by
  apply (hf.neg.max hg.neg).neg.congr
  intro x _
  change -Max.max (-f x) (-g x) = Min.min (f x) (g x)
  rcases le_total (f x) (g x) with h | h
  · rw [max_eq_left (neg_le_neg h), neg_neg, min_eq_left h]
  · rw [max_eq_right (neg_le_neg h), neg_neg, min_eq_right h]

/-- The actual finite sum of original local PL scalars is local PL
on the same open coordinate domain, including the empty sum.
See Hudson pp. 12--17 and Dehn derivation 006. -/
theorem locallyPiecewiseAffineOn_finset_sum {ι : Type*} (s : Finset ι)
    (hU : IsOpen U) (f : ι → E → ℝ)
    (hf : ∀ i ∈ s, LocallyPiecewiseAffineOn (f i) U) :
    LocallyPiecewiseAffineOn (fun x => ∑ i ∈ s, f i x) U := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact (locallyPiecewiseAffineOn_affine
      (ContinuousAffineMap.const ℝ E (0 : ℝ)) hU).congr (fun _ _ => rfl)
  | @insert i s hi ih =>
    have hiPL := hf i (Finset.mem_insert_self i s)
    have hsPL := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    simpa only [Finset.sum_insert hi] using hiPL.add hsPL

end Geometry
