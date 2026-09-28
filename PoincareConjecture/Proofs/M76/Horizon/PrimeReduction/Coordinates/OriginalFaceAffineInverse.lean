import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Coordinates.AffineTriangleComponents
import PoincareConjecture.Proofs.M76.Mathlib.AffineInterpolation









set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76

theorem exists_original_face_chart_affine_inverse
    {E F X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [TopologicalSpace X]
    (K : SimplicialComplex ℝ E) (g : E → X) (hgi : InjOn g K.space)
    {s : Finset E} (hs : s ∈ K.faces)
    (Q : OpenPartialHomeomorph X F) (A : E →ᴬ[ℝ] F)
    (hmap : MapsTo g (convexHull ℝ (s : Set E)) Q.source)
    (hA : EqOn (Q ∘ g) A (convexHull ℝ (s : Set E))) :
    ∃ B : F →ᴬ[ℝ] E,
      LeftInvOn B A (convexHull ℝ (s : Set E)) ∧
      RightInvOn B A (convexHull ℝ (A '' (s : Set E))) ∧
      MapsTo B (convexHull ℝ (A '' (s : Set E))) (convexHull ℝ (s : Set E)) ∧
      EqOn (g ∘ B) Q.symm (convexHull ℝ (A '' (s : Set E))) := by
  classical
  have hAi : InjOn A (convexHull ℝ (s : Set E)) := by
    intro x hx y hy hxy
    exact hgi (K.convexHull_subset_space hs hx) (K.convexHull_subset_space hs hy)
      (Q.injOn (hmap hx) (hmap hy) ((hA hx).trans (hxy.trans (hA hy).symm)))
  let inv := Function.invFunOn A (convexHull ℝ (s : Set E))
  have hinv : LeftInvOn inv A (convexHull ℝ (s : Set E)) := hAi.leftInvOn_invFunOn
  obtain ⟨B, hB⟩ := AffineIndependent.exists_continuousAffineMap_eqOn
    (affineIndependent_original_face_chart K g hgi hs Q A hmap hA) inv
  have hverts : EqOn (B.toAffineMap.comp A.toAffineMap) (AffineMap.id ℝ E) (s : Set E) := by
    intro x hx
    exact (hB (mem_image_of_mem A hx)).trans (hinv (subset_convexHull ℝ _ hx))
  have hleft : LeftInvOn B A (convexHull ℝ (s : Set E)) := by
    intro x hx
    exact (AffineMap.eqOn_affineSpan hverts) (convexHull_subset_affineSpan _ hx)
  have hpre : ∀ y ∈ convexHull ℝ (A '' (s : Set E)),
      ∃ x ∈ convexHull ℝ (s : Set E), A x = y := by
    intro y hy
    exact (A.toAffineMap.image_convexHull (s : Set E)).symm.subset hy
  refine ⟨B, hleft, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := hpre y hy
    rw [hleft hx]
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := hpre y hy
    rw [hleft hx]
    exact hx
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := hpre y hy
    change g (B (A x)) = Q.symm (A x)
    rw [hleft hx, ← show Q (g x) = A x from hA hx, Q.left_inv (hmap hx)]

end PoincareConjecture.M76
