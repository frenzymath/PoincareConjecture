import PoincareConjecture.Proofs.M76.Mathlib.RadialSphereExtension

set_option autoImplicit false

open Set Metric

namespace Homeomorph

theorem exists_extension_of_unitBall_models
    {E F X Y A B : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E] [Nontrivial E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [ProperSpace F] [Nontrivial F]
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace A] [TopologicalSpace B]
    (iA : A → X) (iB : B → Y)
    (hX : X ≃ₜ closedBall (0 : E) 1) (hY : Y ≃ₜ closedBall (0 : F) 1)
    (hA : A ≃ₜ sphere (0 : E) 1) (hB : B ≃ₜ sphere (0 : F) 1)
    (hXA : ∀ a, hX (iA a) = ⟨hA a, sphere_subset_closedBall (hA a).property⟩)
    (hYB : ∀ b, hY (iB b) = ⟨hB b, sphere_subset_closedBall (hB b).property⟩)
    (e : A ≃ₜ B) : ∃ f : X ≃ₜ Y, ∀ a, f (iA a) = iB (e a) := by
  let es := hA.symm.trans (e.trans hB)
  let f := hX.trans (es.radialClosedBallExtension.trans hY.symm)
  refine ⟨f, ?_⟩
  intro a
  apply hY.injective
  change hY (hY.symm (es.radialClosedBallExtension (hX (iA a)))) = hY (iB (e a))
  rw [hY.apply_symm_apply, hXA, hYB, radialClosedBallExtension_apply_sphere]
  apply Subtype.ext
  change (hB (e (hA.symm (hA a))) : F) = (hB (e a) : F)
  rw [hA.symm_apply_apply]

end Homeomorph
