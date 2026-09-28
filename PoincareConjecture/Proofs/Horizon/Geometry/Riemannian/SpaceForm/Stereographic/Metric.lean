import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.SpaceForm.RoundSphere
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Coefficients
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology InnerProductSpace

namespace Poincare.Geometry.Riemannian.SpaceForm

private theorem fderiv_stereoInvFunAux_apply
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v x a : E) :
    fderiv ℝ (stereoInvFunAux v) x a =
      (-(‖x‖ ^ 2 + 4)⁻¹ ^ 2 * (2 * ⟪x, a⟫_ℝ)) •
        ((4 : ℝ) • x + (‖x‖ ^ 2 - 4) • v) +
      (‖x‖ ^ 2 + 4)⁻¹ • ((4 : ℝ) • a + (2 * ⟪x, a⟫_ℝ) • v) := by
  have hn := (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have hi := (hasFDerivAt_inv (by positivity : ‖x‖ ^ 2 + 4 ≠ 0)).comp x
    (hn.add_const 4)
  have hs := ((hasFDerivAt_id x).const_smul (4 : ℝ)).add
    ((hn.sub_const 4).smul_const v)
  have hd := hi.smul hs
  change HasFDerivAt (stereoInvFunAux v) _ x at hd
  rw [hd.fderiv]
  simp [smul_smul, inv_pow, add_comm, mul_comm, mul_left_comm, mul_assoc]

theorem inner_fderiv_stereoInvFunAux
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {v : E} (hv : ‖v‖ = 1) {x a b : E}
    (hx : ⟪x, v⟫_ℝ = 0) (ha : ⟪a, v⟫_ℝ = 0) (hb : ⟪b, v⟫_ℝ = 0) :
    ⟪fderiv ℝ (stereoInvFunAux v) x a,
      fderiv ℝ (stereoInvFunAux v) x b⟫_ℝ =
      16 / (‖x‖ ^ 2 + 4) ^ 2 * ⟪a, b⟫_ℝ := by
  have hden : ‖x‖ ^ 2 + 4 ≠ 0 := by positivity
  have hvx : ⟪v, x⟫_ℝ = 0 := by rw [real_inner_comm, hx]
  have hvb : ⟪v, b⟫_ℝ = 0 := by rw [real_inner_comm, hb]
  rw [fderiv_stereoInvFunAux_apply, fderiv_stereoInvFunAux_apply]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, hx, ha, hvx, hvb, real_inner_self_eq_norm_sq, hv]
  rw [real_inner_comm a x]
  field_simp
  ring

theorem roundSphereMetric_chart_symm_inner {n : ℕ} (q : UnitSphere n)
    (x a b : EuclideanSpace ℝ (Fin n)) :
    (roundSphereMetric n).inner ((chartAt (EuclideanSpace ℝ (Fin n)) q).symm x)
      (mfderiv (𝓡 n) (𝓡 n) (chartAt (EuclideanSpace ℝ (Fin n)) q).symm x a)
      (mfderiv (𝓡 n) (𝓡 n) (chartAt (EuclideanSpace ℝ (Fin n)) q).symm x b) =
      16 / (‖x‖ ^ 2 + 4) ^ 2 * ⟪a, b⟫_ℝ := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
    ⟨by simp⟩
  let v : UnitSphere n := -q
  let c := chartAt (EuclideanSpace ℝ (Fin n)) q
  let U : (ℝ ∙ (v : EuclideanSpace ℝ (Fin (n + 1))))ᗮ ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin n) := (OrthonormalBasis.fromOrthogonalSpanSingleton n
    (ne_zero_of_mem_unit_sphere v)).repr
  let A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
    (ℝ ∙ (v : EuclideanSpace ℝ (Fin (n + 1))))ᗮ.subtypeL.comp
      U.symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hAnorm (y : EuclideanSpace ℝ (Fin n)) : ‖A y‖ = ‖y‖ := U.symm.norm_map y
  have hAinner (y z : EuclideanSpace ℝ (Fin n)) :
      ⟪A y, A z⟫_ℝ = ⟪y, z⟫_ℝ := U.symm.inner_map_map y z
  have hAorth (y : EuclideanSpace ℝ (Fin n)) :
      ⟪A y, (v : EuclideanSpace ℝ (Fin (n + 1)))⟫_ℝ = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_left.mp (U.symm y).property
  let f : UnitSphere n → EuclideanSpace ℝ (Fin (n + 1)) := Subtype.val
  have heq : f ∘ c.symm = stereoInvFunAux (v : EuclideanSpace ℝ (Fin (n + 1))) ∘ A := by
    funext y
    change ((stereographic' n v).symm y : EuclideanSpace ℝ (Fin (n + 1))) = _
    rw [stereographic'_symm_apply]
    simp [A, U, stereoInvFunAux, smul_add, smul_smul]
  have hc : ContMDiff (𝓡 n) (𝓡 n) ∞ c.symm := by
    have h := contMDiffOn_chart_symm (I := 𝓡 n) (x := q) (n := (∞ : ℕ∞ω))
    have ht : c.target = univ := stereographic'_target v
    rw [show (chartAt (EuclideanSpace ℝ (Fin n)) q).target = univ from ht] at h
    exact contMDiffOn_univ.mp h
  have hf : ContMDiff (𝓡 n) (𝓡 (n + 1)) ∞ f := contMDiff_coe_sphere
  have hder : fderiv ℝ (f ∘ c.symm) x =
      (mfderiv (𝓡 n) (𝓡 (n + 1)) f (c.symm x)).comp
        (mfderiv (𝓡 n) (𝓡 n) c.symm x) := by
    rw [← mfderiv_eq_fderiv]
    exact mfderiv_comp x (hf (c.symm x) |>.mdifferentiableAt (by simp))
      (hc x |>.mdifferentiableAt (by simp))
  have hderA : fderiv ℝ (f ∘ c.symm) x =
      (fderiv ℝ (stereoInvFunAux (v : EuclideanSpace ℝ (Fin (n + 1)))) (A x)).comp A := by
    rw [heq, fderiv_comp x ((contDiff_stereoInvFunAux (m := (∞ : ℕ∞ω))).differentiable
      (by simp) (A x))
      A.differentiableAt, A.fderiv]
  rw [roundSphereMetric_inner, PoincareConjecture.RiemannianMetric.euclideanMetric_inner]
  change @inner ℝ (EuclideanSpace ℝ (Fin (n + 1))) _
    ((mfderiv (𝓡 n) (𝓡 (n + 1)) f (c.symm x))
      (mfderiv (𝓡 n) (𝓡 n) c.symm x a))
    ((mfderiv (𝓡 n) (𝓡 (n + 1)) f (c.symm x))
      (mfderiv (𝓡 n) (𝓡 n) c.symm x b)) = _
  have h := congrArg (fun T : EuclideanSpace ℝ (Fin n) →L[ℝ]
    EuclideanSpace ℝ (Fin (n + 1)) => ⟪T a, T b⟫_ℝ) (hder.symm.trans hderA)
  refine h.trans ?_
  simpa only [ContinuousLinearMap.comp_apply, hAnorm, hAinner] using
    inner_fderiv_stereoInvFunAux (norm_eq_of_mem_sphere v) (hAorth x) (hAorth a) (hAorth b)

theorem roundSphereMetric_pullbackCoefficients_chart {n : ℕ} (q : UnitSphere n) :
    (roundSphereMetric n).pullbackCoefficients
      (chartAt (EuclideanSpace ℝ (Fin n)) q).symm =
      fun x => (16 / (‖x‖ ^ 2 + 4) ^ 2) •
        (innerSL ℝ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) := by
  funext x
  ext a b
  exact roundSphereMetric_chart_symm_inner q x a b

theorem exists_uniform_roundSphere_chart_jet_bound (n j : ℕ) (r : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ q : UnitSphere n, ∀ x : EuclideanSpace ℝ (Fin n),
      ‖x‖ ≤ r →
      ‖iteratedFDeriv ℝ j ((roundSphereMetric n).pullbackCoefficients
        (chartAt (EuclideanSpace ℝ (Fin n)) q).symm) x‖ ≤ B := by
  let F : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
    fun x => (16 / (‖x‖ ^ 2 + 4) ^ 2) • innerSL ℝ
  have hF : ContDiff ℝ ∞ F := by
    let : IsBoundedSMul ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
      NormedSpace.toIsBoundedSMul (𝕜 := ℝ)
        (E := EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    have hs : ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ (Fin n) =>
        16 / (‖x‖ ^ 2 + 4) ^ 2) :=
      contDiff_const.div (((contDiff_norm_sq ℝ).add contDiff_const).pow 2)
        (fun x => by positivity)
    exact hs.smul contDiff_const
  have hcont := ContDiff.continuous_iteratedFDeriv (m := j)
    (by norm_cast; exact le_top : (j : ℕ∞ω) ≤ ∞) hF
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) r).exists_bound_of_continuousOn
    hcont.continuousOn
  refine ⟨max 0 B, le_max_left _ _, ?_⟩
  intro q x hx
  rw [roundSphereMetric_pullbackCoefficients_chart]
  exact (hB x (by simpa only [Metric.mem_closedBall, dist_zero_right] using hx)).trans
    (le_max_right _ _)

theorem roundSphere_chart_quadratic_bounds {n : ℕ} (q : UnitSphere n)
    {r : ℝ} {x : EuclideanSpace ℝ (Fin n)} (hx : ‖x‖ ≤ r)
    (v : EuclideanSpace ℝ (Fin n)) :
    (16 / (r ^ 2 + 4) ^ 2) * ‖v‖ ^ 2 ≤
        (roundSphereMetric n).pullbackCoefficients
          (chartAt (EuclideanSpace ℝ (Fin n)) q).symm x v v ∧
      (roundSphereMetric n).pullbackCoefficients
          (chartAt (EuclideanSpace ℝ (Fin n)) q).symm x v v ≤ ‖v‖ ^ 2 := by
  rw [roundSphereMetric_pullbackCoefficients_chart]
  change (16 / (r ^ 2 + 4) ^ 2) * ‖v‖ ^ 2 ≤
      (16 / (‖x‖ ^ 2 + 4) ^ 2) * ⟪v, v⟫_ℝ ∧
    (16 / (‖x‖ ^ 2 + 4) ^ 2) * ⟪v, v⟫_ℝ ≤ ‖v‖ ^ 2
  rw [real_inner_self_eq_norm_sq]
  have hx2 : ‖x‖ ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (norm_nonneg x) hx 2
  have hlo : 16 / (r ^ 2 + 4) ^ 2 ≤ 16 / (‖x‖ ^ 2 + 4) ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (pow_le_pow_left₀ (by positivity) (by linarith) 2)
  have hhi : 16 / (‖x‖ ^ 2 + 4) ^ 2 ≤ 1 := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [sq_nonneg (‖x‖ ^ 2)]
  exact ⟨mul_le_mul_of_nonneg_right hlo (sq_nonneg _),
    (mul_le_mul_of_nonneg_right hhi (sq_nonneg _)).trans_eq (one_mul _)⟩

end Poincare.Geometry.Riemannian.SpaceForm
