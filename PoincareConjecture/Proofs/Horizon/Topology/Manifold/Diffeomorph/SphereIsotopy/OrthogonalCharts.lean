import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.SphereIsotopy.LocalNormalization
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.SpaceForm.LocalIsometry.SphereMotions

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric IsManifold
open scoped Manifold ContDiff InnerProductSpace

namespace Poincare.Manifold.SphereIsotopy

private abbrev E2 := EuclideanSpace ℝ (Fin 2)
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev S2 := PoincareConjecture.UnitTwoSphere

private theorem exists_orthogonal_extension (p q : S2)
    (B : (ℝ ∙ (p : E3))ᗮ ≃ₗᵢ[ℝ] (ℝ ∙ (q : E3))ᗮ) :
    ∃ A : E3 ≃ₗᵢ[ℝ] E3, A (p : E3) = (q : E3) ∧
      ∀ v : (ℝ ∙ (p : E3))ᗮ, A (v : E3) = (B v : E3) := by
  have hnorm (r : S2) : ‖(r : E3)‖ = 1 := norm_eq_of_mem_sphere r
  have hself (r : S2) : inner ℝ (r : E3) (r : E3) = 1 := by
    rw [real_inner_self_eq_norm_sq, hnorm, one_pow]
  have hnormal (r : S2) (v : (ℝ ∙ (r : E3))ᗮ) :
      inner ℝ (r : E3) (v : E3) = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp v.property
  have hnormal' (r : S2) (v : (ℝ ∙ (r : E3))ᗮ) :
      inner ℝ (v : E3) (r : E3) = 0 := by
    rw [real_inner_comm, hnormal]
  let P := (ℝ ∙ (p : E3))ᗮ.orthogonalProjectionOnto
  have hsplit (x : E3) : inner ℝ (p : E3) x • (p : E3) + (P x : E3) = x := by
    rw [← Submodule.starProjection_unit_singleton ℝ (hnorm p)]
    exact (ℝ ∙ (p : E3)).starProjection_add_starProjection_orthogonal x
  let T : E3 →ₗ[ℝ] E3 :=
    (innerSL ℝ (p : E3)).toLinearMap.smulRight (q : E3) +
      (ℝ ∙ (q : E3))ᗮ.subtype.comp (B.toLinearMap.comp P.toLinearMap)
  have hT (x : E3) : T x = inner ℝ (p : E3) x • (q : E3) + (B (P x) : E3) := rfl
  have hTinner (x y : E3) : inner ℝ (T x) (T y) = inner ℝ x y := by
    have hxy : inner ℝ x y = inner ℝ (p : E3) x * inner ℝ (p : E3) y +
        inner ℝ (P x : E3) (P y : E3) := by
      conv_lhs => rw [← hsplit x, ← hsplit y]
      simp only [inner_add_left, inner_add_right, real_inner_smul_left,
        real_inner_smul_right, hself, hnormal, hnormal', mul_one, mul_zero, add_zero]
      ring
    rw [hT, hT, hxy]
    have hB : inner ℝ (B (P x) : E3) (B (P y) : E3) =
        inner ℝ (P x : E3) (P y : E3) := B.inner_map_map (P x) (P y)
    simp only [inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right, hself, hnormal, hnormal', mul_one, mul_zero, add_zero, hB]
    ring
  let Ti := T.isometryOfInner hTinner
  have hsurj : Function.Surjective Ti :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp Ti.injective
  let A := LinearIsometryEquiv.ofSurjective Ti hsurj
  refine ⟨A, ?_, ?_⟩
  · change T (p : E3) = (q : E3)
    rw [hT, hself]
    have hPp : P (p : E3) = 0 := by
      simp [P, Submodule.orthogonalProjectionOnto_orthogonalComplement_singleton_eq_zero]
    simp [hPp]
  · intro v
    change T (v : E3) = (B v : E3)
    rw [hT, hnormal, zero_smul, zero_add]
    exact congrArg (fun w => (B w : E3))
      ((ℝ ∙ (p : E3))ᗮ.orthogonalProjectionOnto_mem_subspace_eq_self v)

theorem exists_orthogonal_chart_map (p q : S2) (Q : E2 ≃ₗᵢ[ℝ] E2) :
    ∃ A : E3 ≃ₗᵢ[ℝ] E3,
      ∃ d : Diffeomorph (𝓡 2) (𝓡 2) S2 S2 ∞,
        (∀ x, (d x : E3) = A (x : E3)) ∧ d p = q ∧
        ∀ x : E2, d ((centeredChart p).symm x) = (centeredChart q).symm (Q x) := by
  let : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩
  let U (r : S2) : (ℝ ∙ ((-r : S2) : E3))ᗮ ≃ₗᵢ[ℝ] E2 :=
    (OrthonormalBasis.fromOrthogonalSpanSingleton 2
      (ne_zero_of_mem_unit_sphere (-r))).repr
  let B := ((U p).trans Q).trans (U q).symm
  obtain ⟨A, hA, hAB⟩ := exists_orthogonal_extension (-p) (-q) B
  let d := Poincare.Geometry.Riemannian.SpaceForm.sphereMotion A
  have hinv (r : S2) (x : E2) :
      ((centeredChart r).symm x : E3) =
        (‖x‖ ^ 2 + 4)⁻¹ • (4 : ℝ) • ((U r).symm x : E3) +
        (‖x‖ ^ 2 + 4)⁻¹ • (‖x‖ ^ 2 - 4) • ((-r : S2) : E3) := by
    simpa only [centeredChart, U, ← Submodule.coe_norm, LinearIsometryEquiv.norm_map] using
      (stereographic'_symm_apply (-r) x)
  have hchart (x : E2) :
      d ((centeredChart p).symm x) = (centeredChart q).symm (Q x) := by
    apply Subtype.ext
    change A ((centeredChart p).symm x : E3) = ((centeredChart q).symm (Q x) : E3)
    rw [hinv, hinv, Q.norm_map, map_add, map_smul, map_smul, map_smul, map_smul,
      hA, hAB]
    simp [B]
  refine ⟨A, d, fun _ => rfl, ?_, hchart⟩
  simpa using hchart 0

end Poincare.Manifold.SphereIsotopy
