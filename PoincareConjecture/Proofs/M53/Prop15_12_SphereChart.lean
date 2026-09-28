import PoincareConjecture.Definitions.M53SphereSeparation
import PoincareConjecture.Proofs.M53.Mathlib.CenteredHypersurfaceChart










set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.Proofs.M53




theorem sphere_exists_centered_zero_slice_chart
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    (S : SmoothEmbeddedNullHomotopicSphere (M := M)) (x : UnitTwoSphere) :
    ∃ e : OpenPartialHomeomorph M (ULift.{u} (EuclideanSpace ℝ (Fin 2)) × ℝ),
      S.sphere x ∈ e.source ∧ e (S.sphere x) = 0 ∧
        ∀ y ∈ e.source, y ∈ Set.range S.sphere ↔ (e y).2 = 0 := by
  obtain ⟨e, hx, he, hslice⟩ :=
    S.smooth_embedding.exists_centered_zero_slice_chart (by simp) x
  let L : (EuclideanSpace ℝ (Fin 2) × ℝ) ≃ₜ
      (ULift.{u} (EuclideanSpace ℝ (Fin 2)) × ℝ) :=
    Homeomorph.ulift.symm.prodCongr (Homeomorph.refl ℝ)
  refine ⟨e.transHomeomorph L, hx, ?_, hslice⟩
  change L (e (S.sphere x)) = 0
  rw [he]
  rfl

end PoincareConjecture.Proofs.M53
