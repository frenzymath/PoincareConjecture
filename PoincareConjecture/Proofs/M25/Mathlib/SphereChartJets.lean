import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.SpaceForm.Stereographic.Transition
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Coefficients.ChristoffelEstimate
import PoincareConjecture.Proofs.M25.Mathlib.SecondDerivative
import Mathlib.Tactic.Module











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 8

open Set Filter
open scoped ContDiff Manifold Topology InnerProductSpace

private theorem fderiv_stereoInvFunAux_apply
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a x v : E) :
    fderiv ℝ (stereoInvFunAux a) x v =
      (-(‖x‖ ^ 2 + 4)⁻¹ ^ 2 * (2 * ⟪x, v⟫_ℝ)) •
        ((4 : ℝ) • x + (‖x‖ ^ 2 - 4) • a) +
      (‖x‖ ^ 2 + 4)⁻¹ • ((4 : ℝ) • v + (2 * ⟪x, v⟫_ℝ) • a) := by
  have hn := (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have hi := (hasFDerivAt_inv (by positivity : ‖x‖ ^ 2 + 4 ≠ 0)).comp x
    (hn.add_const 4)
  have hb := ((hasFDerivAt_id x).const_smul (4 : ℝ)).add
    ((hn.sub_const 4).smul_const a)
  have hd := hi.smul hb
  change HasFDerivAt (stereoInvFunAux a) _ x at hd
  rw [hd.fderiv]
  simp [smul_smul, inv_pow, add_comm, mul_comm, mul_left_comm, mul_assoc]




theorem fderiv_fderiv_stereoInvFunAux_zero
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a v w : E) :
    fderiv ℝ (fderiv ℝ (stereoInvFunAux a)) 0 v w = ⟪v, w⟫_ℝ • a := by
  have hD : DifferentiableAt ℝ (fderiv ℝ (stereoInvFunAux a)) (0 : E) :=
    ((contDiff_stereoInvFunAux (v := a) (m := ∞)).contDiffAt.fderiv_right
      (m := 1) (by norm_cast)).differentiableAt (by norm_num)
  have heval := (hD.hasFDerivAt.clm_apply (hasFDerivAt_const w (0 : E))).fderiv
  have hevalv : fderiv ℝ (fun x => fderiv ℝ (stereoInvFunAux a) x w) 0 v =
      fderiv ℝ (fderiv ℝ (stereoInvFunAux a)) 0 v w := by
    simpa using congrArg (fun L : E →L[ℝ] E => L v) heval
  have hn : HasFDerivAt (fun x : E => ‖x‖ ^ 2) (0 : E →L[ℝ] ℝ) 0 := by
    simpa using (hasStrictFDerivAt_norm_sq (0 : E)).hasFDerivAt
  have hi : HasFDerivAt (fun x : E => (‖x‖ ^ 2 + 4)⁻¹)
      (0 : E →L[ℝ] ℝ) 0 := by
    have h := (hasFDerivAt_inv (by positivity : ‖(0 : E)‖ ^ 2 + 4 ≠ 0)).comp
      (0 : E) (hn.add_const 4)
    change HasFDerivAt (fun x : E => (‖x‖ ^ 2 + 4)⁻¹) _ 0 at h
    simpa only [ContinuousLinearMap.comp_zero] using h
  have hw : HasFDerivAt (fun x : E => ⟪x, w⟫_ℝ)
      ((innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ).flip w) 0 :=
    ((innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ).flip w).hasFDerivAt
  have hb := ((hasFDerivAt_id (0 : E)).const_smul (4 : ℝ)).add
    ((hn.sub_const 4).smul_const a)
  have hc := (hasFDerivAt_const ((4 : ℝ) • w) (0 : E)).add
    ((hw.const_mul 2).smul_const a)
  have hd := (((hi.pow 2).neg.mul (hw.const_mul 2)).smul hb).add (hi.smul hc)
  change HasFDerivAt (fun x : E =>
    (-(‖x‖ ^ 2 + 4)⁻¹ ^ 2 * (2 * ⟪x, w⟫_ℝ)) •
        ((4 : ℝ) • x + (‖x‖ ^ 2 - 4) • a) +
      (‖x‖ ^ 2 + 4)⁻¹ • ((4 : ℝ) • w + (2 * ⟪x, w⟫_ℝ) • a)) _ 0 at hd
  have hfun : (fun x => fderiv ℝ (stereoInvFunAux a) x w) =
      fun x => (-(‖x‖ ^ 2 + 4)⁻¹ ^ 2 * (2 * ⟪x, w⟫_ℝ)) •
          ((4 : ℝ) • x + (‖x‖ ^ 2 - 4) • a) +
        (‖x‖ ^ 2 + 4)⁻¹ • ((4 : ℝ) • w + (2 * ⟪x, w⟫_ℝ) • a) :=
    funext fun x => fderiv_stereoInvFunAux_apply a x w
  rw [← hevalv, hfun, hd.fderiv]
  norm_num [ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    innerSL_apply_apply, real_inner_comm w v, smul_smul]
  change (1 / 8 * ⟪w, v⟫_ℝ * 4) • a + (1 / 4 * (2 * ⟪w, v⟫_ℝ)) • a =
    ⟪w, v⟫_ℝ • a
  module

namespace Poincare.Geometry.Riemannian.SpaceForm

open PoincareConjecture

private theorem sphere_chart_symm_inclusion_contDiff {n : ℕ} (q : UnitSphere n) :
    ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ (Fin n) =>
      ((chartAt (EuclideanSpace ℝ (Fin n)) q).symm x :
        EuclideanSpace ℝ (Fin (n + 1)))) := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
    ⟨by simp⟩
  have hcoe : ContMDiff (𝓡 n) (𝓡 (n + 1)) ∞
      (Subtype.val : UnitSphere n → EuclideanSpace ℝ (Fin (n + 1))) :=
    contMDiff_coe_sphere
  exact contMDiff_iff_contDiff.mp (hcoe.comp (sphere_chart_symm_contMDiff q))




theorem sphere_chart_symm_inclusion_fderiv_fderiv_zero
    {n : ℕ} (q : UnitSphere n) (v w : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (fderiv ℝ (fun x : EuclideanSpace ℝ (Fin n) =>
      ((chartAt (EuclideanSpace ℝ (Fin n)) q).symm x :
        EuclideanSpace ℝ (Fin (n + 1))))) 0 v w =
      -⟪v, w⟫_ℝ • (q : EuclideanSpace ℝ (Fin (n + 1))) := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
    ⟨by simp⟩
  let p : UnitSphere n := -q
  let U : (ℝ ∙ (p : EuclideanSpace ℝ (Fin (n + 1))))ᗮ ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin n) := (OrthonormalBasis.fromOrthogonalSpanSingleton n
    (ne_zero_of_mem_unit_sphere p)).repr
  let A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
    (ℝ ∙ (p : EuclideanSpace ℝ (Fin (n + 1))))ᗮ.subtypeL.comp
      U.symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hAinner (a b : EuclideanSpace ℝ (Fin n)) :
      ⟪A a, A b⟫_ℝ = ⟪a, b⟫_ℝ := U.symm.inner_map_map a b
  have hfun : (fun x : EuclideanSpace ℝ (Fin n) =>
      ((chartAt (EuclideanSpace ℝ (Fin n)) q).symm x :
        EuclideanSpace ℝ (Fin (n + 1)))) =
      stereoInvFunAux (p : EuclideanSpace ℝ (Fin (n + 1))) ∘ A := by
    funext x
    change ((stereographic' n p).symm x : EuclideanSpace ℝ (Fin (n + 1))) = _
    rw [stereographic'_symm_apply]
    simp [A, U, stereoInvFunAux, smul_add, smul_smul]
  have hDA : fderiv ℝ (A : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin (n + 1))) = fun _ => A :=
    funext fun x => A.fderiv
  have hchain := fderiv_fderiv_comp_apply_of_contDiffOn
    (f := (A : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (n + 1))))
    (g := stereoInvFunAux (p : EuclideanSpace ℝ (Fin (n + 1))))
    (U := univ) (V := univ) (x := 0) isOpen_univ isOpen_univ (mem_univ _)
    A.contDiff.contDiffOn (contDiff_stereoInvFunAux (m := 2)).contDiffOn
    (fun _ _ => mem_univ _) v w
  rw [hfun]
  simpa [hDA, fderiv_fderiv_stereoInvFunAux_zero, hAinner, p] using hchain




theorem norm_fderiv_roundSphere_chart_pullbackCoefficients_le
    {n : ℕ} (q : UnitSphere n) (x : EuclideanSpace ℝ (Fin n)) :
    ‖fderiv ℝ ((roundSphereMetric n).pullbackCoefficients
      (chartAt (EuclideanSpace ℝ (Fin n)) q).symm) x‖ ≤ ‖x‖ := by
  let B : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
    (roundSphereMetric n).pullbackCoefficients
      (chartAt (EuclideanSpace ℝ (Fin n)) q).symm
  let I : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
    innerSL ℝ
  have hn := (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have hi := (hasFDerivAt_inv (by positivity : ‖x‖ ^ 2 + 4 ≠ 0)).comp x
    (hn.add_const 4)
  have hd := ((hi.pow 2).const_mul 16).smul_const I
  change HasFDerivAt (fun y => (16 * ((‖y‖ ^ 2 + 4)⁻¹) ^ 2) • I) _ x at hd
  have hfun : B = fun y => (16 * ((‖y‖ ^ 2 + 4)⁻¹) ^ 2) • I := by
    rw [show B = (roundSphereMetric n).pullbackCoefficients
      (chartAt (EuclideanSpace ℝ (Fin n)) q).symm from rfl,
      roundSphereMetric_pullbackCoefficients_chart]
    funext y
    simp [I, div_eq_mul_inv, inv_pow]
  have hderiv (v : EuclideanSpace ℝ (Fin n)) :
      fderiv ℝ B x v = (-64 * ⟪x, v⟫_ℝ / (‖x‖ ^ 2 + 4) ^ 3) • I := by
    rw [hfun, hd.fderiv]
    norm_num [ContinuousLinearMap.comp_apply, smul_smul]
    simp only [← neg_smul]
    congr 1
    field_simp
    ring
  change ‖fderiv ℝ B x‖ ≤ ‖x‖
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg x)
  intro v
  rw [hderiv, norm_smul]
  have hden : (0 : ℝ) < ‖x‖ ^ 2 + 4 := by positivity
  have hcube : (64 : ℝ) ≤ (‖x‖ ^ 2 + 4) ^ 3 := by
    calc
      (64 : ℝ) = 4 ^ 3 := by norm_num
      _ ≤ (‖x‖ ^ 2 + 4) ^ 3 := by gcongr; nlinarith [sq_nonneg ‖x‖]
  have hfac : 64 / (‖x‖ ^ 2 + 4) ^ 3 ≤ (1 : ℝ) :=
    (div_le_one (pow_pos hden 3)).mpr hcube
  have hscalar : |-64 * ⟪x, v⟫_ℝ / (‖x‖ ^ 2 + 4) ^ 3| ≤ ‖x‖ * ‖v‖ := by
    calc
      _ = (64 / (‖x‖ ^ 2 + 4) ^ 3) * |⟪x, v⟫_ℝ| := by
        rw [abs_div, abs_mul, abs_of_pos (pow_pos hden 3)]
        norm_num
        ring
      _ ≤ 1 * (‖x‖ * ‖v‖) :=
        mul_le_mul hfac (abs_real_inner_le_norm x v) (abs_nonneg _) zero_le_one
      _ = ‖x‖ * ‖v‖ := one_mul _
  have hI : ‖I‖ ≤ (1 : ℝ) := norm_innerSL_le ℝ
  exact (mul_le_mul hscalar hI (norm_nonneg I) (by positivity)).trans_eq (mul_one _)




theorem sphere_chart_recenter_twoJet {n : ℕ} (q : UnitSphere n)
    (y : EuclideanSpace ℝ (Fin n)) (hy : ‖y‖ ≤ 1 / 4) :
    let p := (chartAt (EuclideanSpace ℝ (Fin n)) q).symm y
    let f := (chartAt (EuclideanSpace ℝ (Fin n)) p) ∘
      (chartAt (EuclideanSpace ℝ (Fin n)) q).symm
    ContDiffOn ℝ ∞ f (Metric.ball 0 (1 / 2)) ∧
      (∀ z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (1 / 2),
        (chartAt (EuclideanSpace ℝ (Fin n)) q).symm z ∈
          (chartAt (EuclideanSpace ℝ (Fin n)) p).source) ∧
      (∀ z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (1 / 2),
        (chartAt (EuclideanSpace ℝ (Fin n)) p).symm (f z) =
          (chartAt (EuclideanSpace ℝ (Fin n)) q).symm z) ∧
      f y = 0 ∧ ‖fderiv ℝ f y‖ ≤ 1 ∧
        ‖fderiv ℝ (fderiv ℝ f) y‖ ≤ 3 * ‖y‖ := by
  let p := (chartAt (EuclideanSpace ℝ (Fin n)) q).symm y
  let f := (chartAt (EuclideanSpace ℝ (Fin n)) p) ∘
    (chartAt (EuclideanSpace ℝ (Fin n)) q).symm
  have hpq : ‖(q : EuclideanSpace ℝ (Fin (n + 1))) - p‖ < 1 / 2 := by
    calc
      _ = ‖(p : EuclideanSpace ℝ (Fin (n + 1))) - q‖ := norm_sub_rev _ _
      _ ≤ ‖y‖ := norm_sphere_chart_symm_sub_center_le q y
      _ < 1 / 2 := hy.trans_lt (by norm_num)
  have hymem : y ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (1 / 2) := by
    rw [Metric.mem_ball, dist_zero_right]
    exact hy.trans_lt (by norm_num)
  have hsmooth : ContDiffOn ℝ ∞ f (Metric.ball 0 (1 / 2)) :=
    contDiffOn_sphere_chart_transition p q hpq
  have hsource (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ Metric.ball 0 (1 / 2)) :
      (chartAt (EuclideanSpace ℝ (Fin n)) q).symm z ∈
        (chartAt (EuclideanSpace ℝ (Fin n)) p).source :=
    (sphere_chart_transition_mapsTo_ball p q hpq z hz).1
  have hinverse (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ Metric.ball 0 (1 / 2)) :
      (chartAt (EuclideanSpace ℝ (Fin n)) p).symm (f z) =
        (chartAt (EuclideanSpace ℝ (Fin n)) q).symm z :=
    (chartAt (EuclideanSpace ℝ (Fin n)) p).left_inv (hsource z hz)
  have hcenter : f y = 0 := sphere_chart_center p
  let B := (roundSphereMetric n).pullbackCoefficients
    (chartAt (EuclideanSpace ℝ (Fin n)) q).symm
  let C := (roundSphereMetric n).pullbackCoefficients
    (chartAt (EuclideanSpace ℝ (Fin n)) p).symm
  have hmetric (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ Metric.ball 0 (1 / 2))
      (v w : EuclideanSpace ℝ (Fin n)) :
      B z v w = C (f z) (fderiv ℝ f z v) (fderiv ℝ f z w) :=
    (sphere_chart_transition_metric p q hpq hz v w).symm
  have hCzero : C 0 = (innerSL ℝ :
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) := by
    dsimp only [C]
    rw [roundSphereMetric_pullbackCoefficients_chart]
    norm_num
  have hfirst : ‖fderiv ℝ f y‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro v
    have hm := hmetric y hymem v v
    rw [hcenter, hCzero] at hm
    have hsq : ‖fderiv ℝ f y v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq]
      exact hm.symm.le.trans (roundSphere_chart_quadratic_bounds q (x := y) le_rfl v).2
    simpa only [one_mul] using
      (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq
  have hlow (r : UnitSphere n) (z : EuclideanSpace ℝ (Fin n))
      (hz : ‖z‖ ≤ 1 / 4) (v : EuclideanSpace ℝ (Fin n)) :
      (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ (roundSphereMetric n).pullbackCoefficients
        (chartAt (EuclideanSpace ℝ (Fin n)) r).symm z v v := by
    have hhalf : (1 / 2 : ℝ) ≤ 16 / ((1 / 2 : ℝ) ^ 2 + 4) ^ 2 := by norm_num
    exact (mul_le_mul_of_nonneg_right hhalf (sq_nonneg _)).trans
      (roundSphere_chart_quadratic_bounds r (r := 1 / 2)
        (hz.trans (by norm_num)) v).1
  have hBinv : (B y).IsInvertible :=
    CoordinateTransition.isInvertible_of_uniformEllipticity (by norm_num : (0 : ℝ) < 1 / 2)
      (hlow q y hy)
  have hCinv : (C (f y)).IsInvertible := by
    rw [hcenter]
    exact CoordinateTransition.isInvertible_of_uniformEllipticity
      (by norm_num : (0 : ℝ) < 1 / 2) (hlow p 0 (by norm_num))
  have hcoeffSmooth (r : UnitSphere n) : ContDiff ℝ ∞
      ((roundSphereMetric n).pullbackCoefficients
        (chartAt (EuclideanSpace ℝ (Fin n)) r).symm) := by
    apply contDiff_iff_contDiffAt.mpr
    intro z
    exact (roundSphereMetric n).contDiffAt_pullbackCoefficients
      (sphere_chart_symm_contMDiff r z)
  have hsymm (r : UnitSphere n) (z v w : EuclideanSpace ℝ (Fin n)) :
      (roundSphereMetric n).pullbackCoefficients
        (chartAt (EuclideanSpace ℝ (Fin n)) r).symm z v w =
      (roundSphereMetric n).pullbackCoefficients
        (chartAt (EuclideanSpace ℝ (Fin n)) r).symm z w v := by
    rw [roundSphereMetric_pullbackCoefficients_chart]
    change _ * ⟪v, w⟫_ℝ = _ * ⟪w, v⟫_ℝ
    rw [real_inner_comm v w]
  have hmetricGerm : ∀ᶠ z in 𝓝 y, ∀ v w,
      B z v w = C (f z) (fderiv ℝ f z v) (fderiv ℝ f z w) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hymem] with z hz
    exact hmetric z hz
  have hsurj := CoordinateTransition.surjective_of_pullback_isInvertible
    hBinv (hmetric y hymem)
  have hGammaB : ‖CoordinateExponential.christoffelBilinear B y‖ ≤ 3 * ‖y‖ := by
    have hb := CoordinateExponential.norm_christoffelBilinear_le_of_ellipticity B y
      (by norm_num : (0 : ℝ) < 1 / 2) (hlow q y hy)
    norm_num at hb
    exact hb.trans (mul_le_mul_of_nonneg_left
      (norm_fderiv_roundSphere_chart_pullbackCoefficients_le q y) (by norm_num))
  have hGammaC : CoordinateExponential.christoffelBilinear C 0 = 0 := by
    apply norm_eq_zero.mp
    apply le_antisymm ?_ (norm_nonneg _)
    have hc := CoordinateExponential.norm_christoffelBilinear_le_of_ellipticity C 0
      (by norm_num : (0 : ℝ) < 1 / 2) (hlow p 0 (by norm_num))
    have hD := norm_fderiv_roundSphere_chart_pullbackCoefficients_le p 0
    norm_num at hc
    rw [norm_zero] at hD
    exact hc.trans (by simpa only [mul_zero] using
      (mul_le_mul_of_nonneg_left hD (by norm_num : (0 : ℝ) ≤ 3)))
  have hsecond (v w : EuclideanSpace ℝ (Fin n)) :
      fderiv ℝ (fderiv ℝ f) y v w =
        fderiv ℝ f y (CoordinateExponential.christoffelBilinear B y v w) := by
    have h := CoordinateTransition.fderiv_fderiv_eq_christoffel
      ((hcoeffSmooth q).differentiable (by simp) y)
      ((hcoeffSmooth p).differentiable (by simp) (f y)) hBinv hCinv
      (Filter.Eventually.of_forall (fun z => hsymm q z))
      (Filter.Eventually.of_forall (fun z => hsymm p z))
      (hsmooth.contDiffAt (Metric.isOpen_ball.mem_nhds hymem)) hsurj hmetricGerm v w
    change fderiv ℝ (fderiv ℝ f) y v w =
      fderiv ℝ f y (CoordinateExponential.christoffelBilinear B y v w) -
        CoordinateExponential.christoffelBilinear C (f y)
          (fderiv ℝ f y v) (fderiv ℝ f y w) at h
    simpa only [hcenter, hGammaC, zero_apply, sub_zero] using h
  refine ⟨hsmooth, hsource, hinverse, hcenter, hfirst, ?_⟩
  apply ContinuousLinearMap.opNorm_le_bound₂ _ (by positivity)
  intro v w
  rw [hsecond]
  calc
    _ ≤ ‖fderiv ℝ f y‖ * ‖CoordinateExponential.christoffelBilinear B y v w‖ :=
      (fderiv ℝ f y).le_opNorm _
    _ ≤ 1 * ((3 * ‖y‖) * ‖v‖ * ‖w‖) :=
      mul_le_mul hfirst
        ((CoordinateExponential.christoffelBilinear B y).le_opNorm₂ v w |>.trans
          (by gcongr)) (norm_nonneg _) zero_le_one
    _ = (3 * ‖y‖) * ‖v‖ * ‖w‖ := one_mul _




theorem norm_fderiv_fderiv_sphere_chart_symm_inclusion_le
    {n : ℕ} (q : UnitSphere n) (y : EuclideanSpace ℝ (Fin n))
    (hy : ‖y‖ ≤ 1 / 4) :
    ‖fderiv ℝ (fderiv ℝ (fun x : EuclideanSpace ℝ (Fin n) =>
      ((chartAt (EuclideanSpace ℝ (Fin n)) q).symm x :
        EuclideanSpace ℝ (Fin (n + 1))))) y‖ ≤ 2 := by
  let p := (chartAt (EuclideanSpace ℝ (Fin n)) q).symm y
  let f := (chartAt (EuclideanSpace ℝ (Fin n)) p) ∘
    (chartAt (EuclideanSpace ℝ (Fin n)) q).symm
  let sigma (r : UnitSphere n) : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin (n + 1)) := fun z =>
    ((chartAt (EuclideanSpace ℝ (Fin n)) r).symm z : EuclideanSpace ℝ (Fin (n + 1)))
  obtain ⟨hsmooth, _, hinverse, hcenter, hfirst, hsecond⟩ :=
    sphere_chart_recenter_twoJet q y hy
  change ContDiffOn ℝ ∞ f (Metric.ball 0 (1 / 2)) at hsmooth
  change f y = 0 at hcenter
  change ‖fderiv ℝ f y‖ ≤ 1 at hfirst
  change ‖fderiv ℝ (fderiv ℝ f) y‖ ≤ 3 * ‖y‖ at hsecond
  have hymem : y ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (1 / 2) := by
    rw [Metric.mem_ball, dist_zero_right]
    exact hy.trans_lt (by norm_num)
  have heq : sigma q =ᶠ[𝓝 y] sigma p ∘ f := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hymem] with z hz
    exact (congrArg Subtype.val (hinverse z hz)).symm
  have hsecondEq : fderiv ℝ (fderiv ℝ (sigma q)) y =
      fderiv ℝ (fderiv ℝ (sigma p ∘ f)) y := heq.fderiv.fderiv_eq
  have hsigmaD : ‖fderiv ℝ (sigma p) 0‖ ≤ 1 :=
    norm_fderiv_le_of_lipschitz ℝ (sphere_chart_symm_lipschitz p)
  have hsigmaDD : ‖fderiv ℝ (fderiv ℝ (sigma p)) 0‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound₂ _ zero_le_one
    intro v w
    rw [sphere_chart_symm_inclusion_fderiv_fderiv_zero]
    simpa only [norm_smul, Real.norm_eq_abs, abs_neg, norm_eq_of_mem_sphere,
      mul_one, one_mul] using abs_real_inner_le_norm v w
  have hDDf : ‖fderiv ℝ (fderiv ℝ f) y‖ ≤ 1 :=
    hsecond.trans (by nlinarith)
  have hDf (v : EuclideanSpace ℝ (Fin n)) : ‖fderiv ℝ f y v‖ ≤ ‖v‖ := by
    exact ((fderiv ℝ f y).le_opNorm v).trans
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hfirst (norm_nonneg v))
  change ‖fderiv ℝ (fderiv ℝ (sigma q)) y‖ ≤ 2
  apply ContinuousLinearMap.opNorm_le_bound₂ _ (by norm_num)
  intro v w
  have hchain := fderiv_fderiv_comp_apply_of_contDiffOn
    (f := f) (g := sigma p) (U := Metric.ball 0 (1 / 2)) (V := univ)
    Metric.isOpen_ball isOpen_univ hymem (hsmooth.of_le (by norm_cast))
    ((sphere_chart_symm_inclusion_contDiff p).of_le (by norm_cast)).contDiffOn
    (fun _ _ => mem_univ _) v w
  rw [hsecondEq, hchain, hcenter]
  have hleft : ‖fderiv ℝ (fderiv ℝ (sigma p)) 0
      (fderiv ℝ f y v) (fderiv ℝ f y w)‖ ≤ ‖v‖ * ‖w‖ := by
    calc
      _ ≤ ‖fderiv ℝ (fderiv ℝ (sigma p)) 0‖ *
          ‖fderiv ℝ f y v‖ * ‖fderiv ℝ f y w‖ :=
        (fderiv ℝ (fderiv ℝ (sigma p)) 0).le_opNorm₂ _ _
      _ ≤ 1 * ‖v‖ * ‖w‖ := by gcongr <;> exact hDf _
      _ = ‖v‖ * ‖w‖ := by ring
  have hright : ‖fderiv ℝ (sigma p) 0 (fderiv ℝ (fderiv ℝ f) y v w)‖ ≤
      ‖v‖ * ‖w‖ := by
    calc
      _ ≤ ‖fderiv ℝ (sigma p) 0‖ * ‖fderiv ℝ (fderiv ℝ f) y v w‖ :=
        (fderiv ℝ (sigma p) 0).le_opNorm _
      _ ≤ 1 * (1 * ‖v‖ * ‖w‖) :=
        mul_le_mul hsigmaD
          ((fderiv ℝ (fderiv ℝ f) y).le_opNorm₂ v w |>.trans (by gcongr))
          (norm_nonneg _) zero_le_one
      _ = ‖v‖ * ‖w‖ := by ring
  exact (norm_add_le _ _).trans ((add_le_add hleft hright).trans_eq (by ring))

end Poincare.Geometry.Riemannian.SpaceForm
