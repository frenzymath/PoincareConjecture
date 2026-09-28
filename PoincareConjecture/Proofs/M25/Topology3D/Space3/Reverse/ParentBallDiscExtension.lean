import PoincareConjecture.Proofs.M25.Topology3D.Space3.Reverse.ParentBallDiscLinear
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Reverse.ParentBallCapPlane
import PoincareConjecture.Proofs.M25.Topology3D.Space3.BallChartIsometry
import PoincareConjecture.Proofs.M25.Topology3D.Space3.BoundaryChartLinearization
import PoincareConjecture.Proofs.M25.Topology3D.Space3.BoundaryTranslation
import PoincareConjecture.Proofs.M25.Topology3D.Space3.HeightPlaneProjection










set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

attribute [local instance] sourceCircle_stereographic_dimension



theorem exists_sphere_disc_pointwise_extension
    (e₁ e₂ : OpenPartialHomeomorph E2 UnitTwoSphere)
    (h₁ : closedBall (0 : E2) 1 ⊆ e₁.source)
    (h₂ : closedBall (0 : E2) 1 ⊆ e₂.source)
    (he₁ : ContMDiffOn 𝓘(ℝ, E2) (𝓡 2) ∞ e₁ e₁.source)
    (hei₁ : ContMDiffOn (𝓡 2) 𝓘(ℝ, E2) ∞ e₁.symm e₁.target)
    (he₂ : ContMDiffOn 𝓘(ℝ, E2) (𝓡 2) ∞ e₂ e₂.source)
    (hei₂ : ContMDiffOn (𝓡 2) 𝓘(ℝ, E2) ∞ e₂.symm e₂.target) :
    ∃ R : ℝ, 1 < R ∧
      closedBall (0 : E2) R ⊆ e₁.source ∩ e₂.source ∧
      ∃ G : Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞,
        (∀ y : E3, ‖G y‖ = ‖y‖) ∧
        ∀ X : E2, ‖X‖ ≤ R → G (e₁ X : E3) = (e₂ X : E3) := by
  classical
  obtain ⟨δ, hδ, hδsource⟩ :=
    (isCompact_closedBall (0 : E2) 1).exists_thickening_subset_open
      (e₁.open_source.inter e₂.open_source) (fun X hX => ⟨h₁ hX, h₂ hX⟩)
  rw [thickening_closedBall hδ zero_le_one] at hδsource
  let R : ℝ := 1 + δ / 2
  have hR : 1 < R := by dsimp only [R]; linarith only [hδ]
  have hR0 : 0 < R := zero_lt_one.trans hR
  have hsource : closedBall (0 : E2) R ⊆ e₁.source ∩ e₂.source := by
    intro X hX
    apply hδsource
    rw [mem_ball_zero_iff]
    exact (mem_closedBall_zero_iff.mp hX).trans_lt (by dsimp only [R]; linarith only [hδ])
  let v₀ : UnitTwoSphere := ⟨EuclideanSpace.single (2 : Fin 3) 1, by simp⟩
  let V₀ := (ℝ ∙ (v₀ : E3))ᗮ
  have hnormalize (e : OpenPartialHomeomorph E2 UnitTwoSphere)
      (hs : closedBall (0 : E2) R ⊆ e.source)
      (he : ContMDiffOn 𝓘(ℝ, E2) (𝓡 2) ∞ e e.source)
      (hei : ContMDiffOn (𝓡 2) 𝓘(ℝ, E2) ∞ e.symm e.target) :
      ∃ J : E2 ≃L[ℝ] V₀,
        ∃ Q : Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞,
          (∀ y : E3, ‖Q y‖ = ‖y‖) ∧
          ∀ X : E2, ‖X‖ ≤ R → Q (e X : E3) =
            (stereoInvFun (norm_eq_of_mem_sphere v₀) (J X) : E3) := by
    let S : E2 ≃L[ℝ] E2 :=
      (LinearEquiv.smulOfNeZero ℝ E2 R hR0.ne').toContinuousLinearEquiv
    have hS (X : E2) : S X = R • X := rfl
    let eR := S.toHomeomorph.toOpenPartialHomeomorph.trans e
    have heRsource : closedBall (0 : E2) 1 ⊆ eR.source := by
      intro X hX
      refine ⟨mem_univ _, hs ?_⟩
      change S X ∈ closedBall (0 : E2) R
      rw [mem_closedBall_zero_iff, hS, norm_smul, Real.norm_eq_abs, abs_of_pos hR0]
      exact (mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp hX) hR0.le).trans
        (by rw [mul_one])
    have heR : ContMDiffOn 𝓘(ℝ, E2) (𝓡 2) ∞ eR eR.source :=
      he.comp S.contDiff.contMDiff.contMDiffOn (fun _ hX => hX.2)
    have heiR : ContMDiffOn (𝓡 2) 𝓘(ℝ, E2) ∞ eR.symm eR.target :=
      S.symm.contDiff.contMDiff.comp_contMDiffOn (hei.mono inter_subset_left)
    obtain ⟨v, _hv, D, _hchart, _hDs, _hDt, _hDf, _hDi, hrecovery, _himage⟩ :=
      exists_sphere_disc_plane_chart eR heRsource heR heiR
    let V := (ℝ ∙ (v : E3))ᗮ
    let U : V ≃ₗᵢ[ℝ] E2 :=
      (OrthonormalBasis.fromOrthogonalSpanSingleton 2 (ne_zero_of_mem_unit_sphere v)).repr
    let B := D.isometryConjugate U
    obtain ⟨A, r, hr, _hr1, F, hFnorm, hF, _hFsupport⟩ :=
      exists_boundary_disc_affine_image (v : E3) (norm_eq_of_mem_sphere v) B
    let affine : V → V := fun w => B.chart 0 + A (r • w)
    have hscale : Continuous (fun w : V => r • w) :=
      (contDiff_const_smul r : ContDiff ℝ ∞ (fun w : V => r • w)).continuous
    have haffine : Continuous affine := continuous_const.add
      (A.continuous.comp hscale)
    obtain ⟨T, hTnorm, hT, _hTsupport⟩ :=
      exists_boundary_translation (v : E3) (norm_eq_of_mem_sphere v)
        ((isCompact_closedBall (0 : V) 1).image haffine) (-B.chart 0)
    let scaling : V ≃L[ℝ] V :=
      (LinearEquiv.smulOfNeZero ℝ V (r / R) (div_ne_zero hr.ne' hR0.ne')).toContinuousLinearEquiv
    let L : E2 ≃L[ℝ] V := (U.symm.toContinuousLinearEquiv.trans scaling).trans A
    have hL (X : E2) : L X = A ((r / R) • U.symm X) := rfl
    have hH (X : E2) (hX : ‖X‖ ≤ R) : T (F (e X : E3)) =
        (stereoInvFun (norm_eq_of_mem_sphere v) (L X) : E3) := by
      let Z := R⁻¹ • X
      have hZ : Z ∈ closedBall (0 : E2) 1 := by
        rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs,
          abs_of_pos (inv_pos.mpr hR0)]
        exact (mul_le_mul_of_nonneg_left hX (inv_nonneg.mpr hR0.le)).trans
          (by rw [inv_mul_cancel₀ hR0.ne'])
      have hSZ : S Z = X := by
        rw [hS]
        dsimp only [Z]
        rw [smul_smul, mul_inv_cancel₀ hR0.ne', one_smul]
      have hw : U.symm Z ∈ closedBall (0 : V) 1 := by
        simpa only [mem_closedBall_zero_iff, U.symm.norm_map] using hZ
      have hrecover : (stereoInvFun (norm_eq_of_mem_sphere v)
          (B.chart (U.symm Z)) : E3) = (e X : E3) := by
        have hh := congrArg (fun q : UnitTwoSphere => (q : E3))
          (hrecovery Z (D.closedBall_subset_source hZ))
        change (stereoInvFun (norm_eq_of_mem_sphere v) (U.symm (D.chart Z)) : E3) =
          (e (S Z) : E3) at hh
        rw [hSZ] at hh
        simpa only [B, BallNeighborhoodChart.isometryConjugate_apply,
          U.apply_symm_apply] using hh
      rw [← hrecover, hF _ hw, hT _ ⟨U.symm Z, hw, rfl⟩]
      have hcenter : B.chart 0 + A (r • U.symm Z) + -B.chart 0 =
          A (r • U.symm Z) := by abel
      rw [hcenter, hL]
      congr 2
      dsimp only [Z]
      rw [U.symm.map_smul, smul_smul, div_eq_mul_inv]
    let W : E3 ≃ₗᵢ[ℝ] E3 := (ℝ ∙ ((v : E3) - (v₀ : E3)))ᗮ.reflection
    have hWv : W (v : E3) = v₀ :=
      Submodule.reflection_sub ((norm_eq_of_mem_sphere v).trans
        (norm_eq_of_mem_sphere v₀).symm)
    have hWi : W.symm (v₀ : E3) = v := by rw [← hWv, W.symm_apply_apply]
    have hWV (x : V) : W (x : E3) ∈ V₀ := by
      apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
      rw [← hWv, W.inner_map_map]
      exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp x.property
    have hWVi (x : V₀) : W.symm (x : E3) ∈ V := by
      apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
      rw [← hWi, W.symm.inner_map_map]
      exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp x.property
    let I : V ≃ₗᵢ[ℝ] V₀ := {
      toFun := fun x => ⟨W x, hWV x⟩
      invFun := fun x => ⟨W.symm x, hWVi x⟩
      left_inv := fun x => Subtype.ext (W.symm_apply_apply x)
      right_inv := fun x => Subtype.ext (W.apply_symm_apply x)
      map_add' := fun x y => Subtype.ext (W.map_add x y)
      map_smul' := fun s x => Subtype.ext (W.map_smul s x)
      norm_map' := fun x => W.norm_map x }
    have hWstereo (x : V) :
        W (stereoInvFun (norm_eq_of_mem_sphere v) x : E3) =
          (stereoInvFun (norm_eq_of_mem_sphere v₀) (I x) : E3) := by
      rw [stereoInvFun_apply, stereoInvFun_apply, map_smul, map_add,
        map_smul, map_smul, hWv, I.norm_map]
      rfl
    refine ⟨L.trans I.toContinuousLinearEquiv,
      (F.trans T).trans W.toContinuousLinearEquiv.toDiffeomorph, ?_, ?_⟩
    · intro y
      change ‖W (T (F y))‖ = ‖y‖
      rw [W.norm_map, hTnorm, hFnorm]
    · intro X hX
      change W (T (F (e X : E3))) =
        (stereoInvFun (norm_eq_of_mem_sphere v₀) (I (L X)) : E3)
      rw [hH X hX, hWstereo]
  obtain ⟨J₁, Q₁, hQ₁norm, hQ₁⟩ :=
    hnormalize e₁ (fun _ hX => (hsource hX).1) he₁ hei₁
  obtain ⟨J₂, Q₂, hQ₂norm, hQ₂⟩ :=
    hnormalize e₂ (fun _ hX => (hsource hX).2) he₂ hei₂
  obtain ⟨Z, hZnorm, hZ⟩ := exists_boundary_linear_realization v₀ (J₁.symm.trans J₂)
    ((isCompact_closedBall (0 : E2) R).image J₁.continuous)
  refine ⟨R, hR, hsource, (Q₁.trans Z).trans Q₂.symm, ?_, ?_⟩
  · intro y
    change ‖Q₂.symm (Z (Q₁ y))‖ = ‖y‖
    rw [← hQ₂norm (Q₂.symm (Z (Q₁ y))), Q₂.apply_symm_apply, hZnorm, hQ₁norm]
  · intro X hX
    change Q₂.symm (Z (Q₁ (e₁ X : E3))) = (e₂ X : E3)
    rw [hQ₁ X hX, hZ _ ⟨X, mem_closedBall_zero_iff.mpr hX, rfl⟩]
    change Q₂.symm (stereoInvFun (norm_eq_of_mem_sphere v₀)
      (J₂ (J₁.symm (J₁ X))) : E3) = _
    rw [J₁.symm_apply_apply, ← hQ₂ X hX, Q₂.symm_apply_apply]

end PoincareConjecture.M25.Topology3D
