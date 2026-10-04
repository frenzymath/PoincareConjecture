import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Schedules.Gluing.Construction.PullbackErrors

/-!
# Linear operations on vanishing finite jets

Differentiation and fixed linear contractions preserve vanishing jets.
These are the operations in the cylinder connection recurrence.
Source: Definition 2.16 and Proposition 15.2, pp. 353-354.
-/

set_option autoImplicit false

open Filter
open scoped ContDiff Topology

namespace PoincareMT.M45.PointJetsVanish

variable {ι E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {l : Filter ι} {x : ι → E} {f : ι → E → F}

/-- The zero-order vanishing jet is the actual value limit.
Derivation: GluingCompactness.md, applying Proposition 15.2, pp. 353-354. -/
theorem values (hf : PointJetsVanish f x l) :
    Tendsto (fun i => f i (x i)) l (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [norm_iteratedFDeriv_zero, norm_zero] using (hf 0).norm

/-- Differentiation preserves vanishing jets and uses one more input order.
Derivation: GluingCompactness.md, applying Proposition 15.2, pp. 353-354. -/
theorem fderiv (hf : PointJetsVanish f x l) :
    PointJetsVanish (fun i => _root_.fderiv ℝ (f i)) x l := by
  intro m
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [norm_iteratedFDeriv_fderiv, norm_zero] using (hf (m + 1)).norm

/-- Fixed continuous linear contractions preserve vanishing jets.
Derivation: GluingCompactness.md, applying Proposition 15.2, pp. 353-354. -/
theorem clm (hf : PointJetsVanish f x l)
    (hfs : ∀ i, ContDiffAt ℝ ∞ (f i) (x i)) (L : F →L[ℝ] G) :
    PointJetsVanish (fun i => L ∘ f i) x l := by
  intro m
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun i => L.norm_iteratedFDeriv_comp_left (hfs i) (by exact_mod_cast le_top))
  simpa only [norm_zero, mul_zero] using ((hf m).norm.const_mul ‖L‖)

/-- A finite sum of actual smooth vanishing errors has vanishing jets.
Derivation: GluingCompactness.md, applying Proposition 15.2, pp. 353-354. -/
theorem sum {κ : Type*} (s : Finset κ) {f : κ → ι → E → F}
    (hf : ∀ k ∈ s, PointJetsVanish (f k) x l)
    (hfs : ∀ k ∈ s, ∀ i, ContDiffAt ℝ ∞ (f k i) (x i)) :
    PointJetsVanish (fun i y => ∑ k ∈ s, f k i y) x l := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      intro m
      simp only [Finset.sum_empty, iteratedFDeriv_fun_zero, Pi.zero_apply]
      exact tendsto_const_nhds
  | @insert k s hk ih =>
      have ht := (hf k (Finset.mem_insert_self k s)).add
        (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
          (fun j hj => hfs j (Finset.mem_insert_of_mem hj)))
        (hfs k (Finset.mem_insert_self k s))
        (fun i => ContDiffAt.sum (fun j hj => hfs j (Finset.mem_insert_of_mem hj) i))
      simpa only [Finset.sum_insert hk] using ht

end PoincareMT.M45.PointJetsVanish
