import PoincareConjecture.Proofs.M76.Mathlib.AffineHypersurfaceCharts
import Mathlib.Analysis.Convex.PathConnected

set_option autoImplicit false

open Set

namespace ContinuousAffineMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem isConnected_halfspace_sdiff
    (ell : E →ᴬ[ℝ] ℝ) (hell : ell.toAffineMap.linear ≠ 0)
    {U A : Set E} (hU : IsOpen U) (hconv : Convex ℝ U)
    (hne : (U ∩ {x | 0 ≤ ell x}).Nonempty)
    (hA : A ⊆ {x | ell x = 0}) :
    IsConnected ((U ∩ {x | 0 ≤ ell x}) \ A) := by
  have hopen : IsOpenMap (ell : E → ℝ) := ell.toAffineMap.isOpenMap ell.continuous
    (ell.toAffineMap.linear_surjective_iff.mp (LinearMap.surjective hell))
  have hclosure : closure {x | 0 < ell x} = {x | 0 ≤ ell x} := by
    change closure ((ell : E → ℝ) ⁻¹' Ioi 0) = (ell : E → ℝ) ⁻¹' Ici 0
    rw [← hopen.preimage_closure_eq_closure_preimage ell.continuous, closure_Ioi]
  have hdense : U ∩ {x | 0 ≤ ell x} ⊆ closure (U ∩ {x | 0 < ell x}) := by
    intro x hx
    exact hU.inter_closure ⟨hx.1, hclosure.symm ▸ hx.2⟩
  have hpos : (U ∩ {x | 0 < ell x}).Nonempty := (hne.mono hdense).of_closure
  have hconnected : IsConnected (U ∩ {x | 0 < ell x}) :=
    (hconv.inter ((convex_Ioi (0 : ℝ)).affine_preimage ell.toAffineMap)).isConnected hpos
  apply hconnected.subset_closure
  · intro x hx
    have hxpos : 0 < ell x := hx.2
    refine ⟨⟨hx.1, hxpos.le⟩, ?_⟩
    intro hxA
    exact (ne_of_gt hxpos) (hA hxA)
  · intro x hx
    exact hdense hx.1

end ContinuousAffineMap
