import PoincareConjecture.Proofs.M76.Mathlib.AffineInterpolation
import PoincareConjecture.Proofs.M76.Mathlib.ConvexAffineInjectivity










set_option autoImplicit false

open Set

namespace Geometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

theorem exists_affine_transition_on_convexHull {ι : Type*}
    (p : ι → E) (hp : AffineIndependent ℝ p)
    (A D : E →ᴬ[ℝ] F) (hi : InjOn A (convexHull ℝ (range p)))
    (f : F → F) (hf : ∀ z ∈ convexHull ℝ (range p), f (A z) = D z) :
    AffineIndependent ℝ (A ∘ p) ∧
      ∃ B : F →ᴬ[ℝ] F, EqOn f B (convexHull ℝ (range (A ∘ p))) := by
  have hpA := A.toAffineMap.affineIndependent_comp_of_injOn_convexHull hp hi
  obtain ⟨B, hB⟩ := hpA.range.exists_continuousAffineMap_eqOn f
  have hvertices : EqOn (B.toAffineMap.comp A.toAffineMap) D.toAffineMap (range p) := by
    rintro _ ⟨i, rfl⟩
    exact (hB (mem_range_self i)).trans
      (hf (p i) (subset_convexHull ℝ _ (mem_range_self i)))
  refine ⟨hpA, B, ?_⟩
  intro y hy
  have himage : convexHull ℝ (range (A ∘ p)) = A '' convexHull ℝ (range p) := by
    simpa only [range_comp, ContinuousAffineMap.coe_toAffineMap] using
      (A.toAffineMap.image_convexHull (range p)).symm
  obtain ⟨z, hz, rfl⟩ := himage ▸ hy
  exact (hf z hz).trans
    (AffineMap.eqOn_affineSpan hvertices (convexHull_subset_affineSpan _ hz)).symm

end Geometry
