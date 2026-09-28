import Mathlib.Geometry.Manifold.Instances.Sphere











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff InnerProductSpace




theorem exists_stereographic_antipode_linearIsometry
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)]
    (v : sphere (0 : E) 1) :
    ∃ B : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n),
      ∀ x : EuclideanSpace ℝ (Fin n), x ≠ 0 →
        stereographic' n (-v) ((stereographic' n v).symm x) =
          (4 / ‖x‖ ^ 2) • B x := by
  let Pv := (ℝ ∙ (v : E))ᗮ
  let Pm := (ℝ ∙ ((-v : sphere (0 : E) 1) : E))ᗮ
  have hspan : ℝ ∙ (-(v : E)) = ℝ ∙ (v : E) := by
    simpa only [Set.neg_singleton] using
      (Submodule.span_neg (R := ℝ) ({(v : E)} : Set E))
  have hp : Pv = Pm := congrArg Submodule.orthogonal hspan.symm
  let e : Pv ≃ₗᵢ[ℝ] Pm := LinearIsometryEquiv.ofEq Pv Pm hp
  let Uv : Pv ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
    (OrthonormalBasis.fromOrthogonalSpanSingleton n (ne_zero_of_mem_unit_sphere v)).repr
  let Um : Pm ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
    (OrthonormalBasis.fromOrthogonalSpanSingleton n (ne_zero_of_mem_unit_sphere (-v))).repr
  refine ⟨Uv.symm.trans (e.trans Um), ?_⟩
  intro x hx
  let w : Pv := Uv.symm x
  have hw : ‖(w : E)‖ = ‖x‖ := by
    change ‖Uv.symm x‖ = ‖x‖
    exact Uv.symm.norm_map x
  have hv : ‖(v : E)‖ = 1 := norm_eq_of_mem_sphere v
  have horth : ⟪(v : E), (w : E)⟫_ℝ = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp w.property
  have hvv : ⟪(v : E), (v : E)⟫_ℝ = 1 := by simp [hv]
  have hprojw : Pm.orthogonalProjectionOnto (w : E) = e w := by
    have h := Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (e w)
    simpa only [e, LinearIsometryEquiv.coe_ofEq_apply] using h
  have hprojv : Pm.orthogonalProjectionOnto (v : E) = 0 := by
    have h := Submodule.orthogonalProjectionOnto_orthogonalComplement_singleton_eq_zero
      (𝕜 := ℝ) (-(v : E))
    change Pm.orthogonalProjectionOnto (-(v : E)) = 0 at h
    simpa only [map_neg, neg_eq_zero] using h
  have hz : (((stereographic' n v).symm x) : E) =
      (‖x‖ ^ 2 + 4)⁻¹ • (4 : ℝ) • (w : E) +
        (‖x‖ ^ 2 + 4)⁻¹ • (‖x‖ ^ 2 - 4) • (v : E) := by
    rw [stereographic'_symm_apply]
    change (‖(w : E)‖ ^ 2 + 4)⁻¹ • (4 : ℝ) • (w : E) +
      (‖(w : E)‖ ^ 2 + 4)⁻¹ • (‖(w : E)‖ ^ 2 - 4) • (v : E) = _
    rw [hw]
  have hi : ⟪((-v : sphere (0 : E) 1) : E),
      (((stereographic' n v).symm x) : E)⟫_ℝ =
      -((‖x‖ ^ 2 + 4)⁻¹ * (‖x‖ ^ 2 - 4)) := by
    rw [hz]
    change ⟪-(v : E), _⟫_ℝ = _
    simp only [inner_neg_left, inner_add_right, inner_smul_right, horth, hvv]
    ring
  have hproj : Pm.orthogonalProjectionOnto
      (((stereographic' n v).symm x) : E) =
      (‖x‖ ^ 2 + 4)⁻¹ • (4 : ℝ) • e w := by
    rw [hz]
    simp only [map_add, map_smul, hprojw, hprojv, smul_zero, add_zero]
  have hs : 2 / (1 - -((‖x‖ ^ 2 + 4)⁻¹ * (‖x‖ ^ 2 - 4))) *
      (‖x‖ ^ 2 + 4)⁻¹ * 4 = 4 / ‖x‖ ^ 2 := by
    field_simp
    ring_nf
    simp only [← mul_pow, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx), one_pow]
  change Um (stereographic (norm_eq_of_mem_sphere (-v))
    ((stereographic' n v).symm x)) = (4 / ‖x‖ ^ 2) • Um (e w)
  rw [stereographic_apply, hi, hproj]
  simp only [map_smul, smul_smul, ← mul_assoc, hs]
