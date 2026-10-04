import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.AlexanderComplexityPresentation
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.AlexanderComplexityCharge
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Affine.PolygonAffineImage

/-!
# Affine transport of complete Alexander curve presentations

An injective affine map preserves each actual polygon, its
index, the subsingleton residue and the complete curve charge.
This supplies coordinate recentering of a zero section. See
Alexander 1924, pp. 6--8 and M76 derivation 271.
-/

set_option autoImplicit false

open Set

namespace Set

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Injective affine maps preserve a complete geometric curve
presentation and its exact charge. Empty families and empty
residues are included. See Alexander pp. 6--8 and derivation 271. -/
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
