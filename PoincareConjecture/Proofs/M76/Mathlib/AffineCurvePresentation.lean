import PoincareConjecture.Proofs.M76.Mathlib.AlexanderComplexityPresentation
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderComplexityCharge
import PoincareConjecture.Proofs.M76.Mathlib.PolygonAffineImage










set_option autoImplicit false

open Set

namespace Set

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]




theorem HasAlexanderCurvePresentation.affine_image {S : Set E} {a : ℕ}
    (h : HasAlexanderCurvePresentation S a) (f : E →ᵃ[ℝ] F)
    (hf : Function.Injective f) : HasAlexanderCurvePresentation (f '' S) a := by
  obtain ⟨m, n, P, r, hP, hr, hcover, hpair, hcount⟩ := h
  let Q := fun i => (P i).affineImage f
  have hQb (i : Fin m) : (Q i).boundary ℝ = f '' (P i).boundary ℝ :=
    (P i).affineImage_boundary f
  refine ⟨m, n, Q, f '' r, ?_, hr.image f, ?_, ?_, ?_⟩
  · intro i
    exact ⟨hf.comp (hP i).1, (P i).hasSimplicialEdges_affineImage (hP i).2 f hf⟩
  · rw [hcover, image_union, image_iUnion]
    simp only [hQb]
  · intro i j hij
    rw [hQb i, hQb j, ← image_inter hf]
    exact image_mono (hpair hij)
  · simp only [hQb]
    exact (alexanderCurveCount_image (fun i => (P i).boundary ℝ)
      (s := univ) (fun _ => subset_univ _) f hf.injOn).trans hcount

end Set
