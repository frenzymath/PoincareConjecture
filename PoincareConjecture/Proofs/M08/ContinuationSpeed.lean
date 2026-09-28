import PoincareConjecture.Proofs.M08.SecondVariationCoefficients
import PoincareConjecture.Proofs.M08.VariationChartFields
import PoincareConjecture.Proofs.M08.ChartEulerEquation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Topology
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M08

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local instance continuationSpeedDualGroup : NormedAddCommGroup (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance continuationSpeedDualSpace : NormedSpace ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance continuationSpeedBilinGroup :
    NormedAddCommGroup (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance continuationSpeedBilinSpace :
    NormedSpace ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

def continuationSpeedSq {J : Set ℝ} (F : RicciFlow n M J) (T : ℝ)
    (α : ℝ → M) (C : Set ℝ) (s : ℝ) : ℝ :=
  (F.metric (T - s ^ 2)).inner (α s)
    (curveVelocityWithin (n := n) α C s) (curveVelocityWithin (n := n) α C s)

theorem continuationSpeedSq_nonneg {J : Set ℝ} (F : RicciFlow n M J) (T : ℝ)
    (α : ℝ → M) (C : Set ℝ) (s : ℝ) : 0 ≤ continuationSpeedSq F T α C s := by
  by_cases h : curveVelocityWithin (n := n) α C s = 0
  · simp only [continuationSpeedSq, h, map_zero, le_refl]
  · exact ((F.metric (T - s ^ 2)).pos (α s) _ h).le

theorem continuationSpeedSq_contDiffOn {J C U : Set ℝ} (F : RicciFlow n M J) (T : ℝ)
    (α : ℝ → M) (hC : UniqueDiffOn ℝ C) (hU : IsOpen U) (hCU : C ⊆ U)
    (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ α U)
    (htime : ∀ s ∈ C, T - s ^ 2 ∈ J) :
    ContDiffOn ℝ ∞ (continuationSpeedSq F T α C) C := by
  have hA : ContMDiffOn (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun s ↦ Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (α s)
        (curveVelocityWithin (n := n) α C s)) C := by
    apply ((contMDiffOn_mfderiv_const_apply hU α hα (1 : ℝ)).mono hCU).congr
    intro s hs
    apply congrArg (fun w : TangentSpace (𝓡 n) (α s) ↦
      Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (α s) w)
    unfold curveVelocityWithin
    rw [mfderivWithin_eq_mfderiv (hC.uniqueMDiffOn s hs)
      (((hα s (hCU hs)).contMDiffAt (hU.mem_nhds (hCU hs))).mdifferentiableAt (by simp))]
  exact (movingMetric_pair_contMDiffOn F (fun s : ℝ ↦ T - s ^ 2) α
    (curveVelocityWithin (n := n) α C) (curveVelocityWithin (n := n) α C)
    (contDiff_const.sub (contDiff_id.pow 2)).contMDiff.contMDiffOn
    (hα.mono hCU) hA hA (fun s hs ↦ htime s hs)).contDiffOn

set_option maxHeartbeats 2200000 in
theorem continuationSpeedSq_hasDerivAt {J C U : Set ℝ}
    (F : RicciFlow n M J) (hM04 : RicciFlowCurvatureTheory.{u}) (T : ℝ)
    (α : ℝ → M) (hC : UniqueDiffOn ℝ C) (hU : IsOpen U) (hCU : C ⊆ U)
    (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ α U)
    (htime : ∀ s ∈ C, T - s ^ 2 ∈ J)
    (E : ParametricAlongCurveExtensionOn C α (curveVelocityWithin (n := n) α C))
    {s : ℝ} (hs : s ∈ C) (hsN : C ∈ 𝓝 s) :
    HasDerivAt (continuationSpeedSq F T α C)
      (2 * (F.metric (T - s ^ 2)).inner (α s)
          (pullbackCovariantDerivative F (fun r ↦ T - r ^ 2) α
            (curveVelocityWithin (n := n) α C) C E s)
          (curveVelocityWithin (n := n) α C s) +
        4 * s * (F.connection (T - s ^ 2)).ricci (α s)
          (curveVelocityWithin (n := n) α C s) (curveVelocityWithin (n := n) α C s)) s := by
  let x := α s
  let e := extChartAt (𝓡 n) x
  let N := U ∩ α ⁻¹' (chartAt (EuclideanSpace ℝ (Fin n)) x).source
  let q := e ∘ α
  let A := deriv q
  let G := chartActionMetric F T x
  have hN : IsOpen N := hα.continuousOn.isOpen_inter_preimage hU
    (chartAt (EuclideanSpace ℝ (Fin n)) x).open_source
  have hx : α s ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source := mem_chart_source _ _
  have hsN' : s ∈ N := ⟨hCU hs, hx⟩
  have hq : ContDiffOn ℝ ∞ q N := chart_curve_contDiffOn x α
    (hα.mono inter_subset_left) (fun r hr ↦ hr.2)
  have hA : ContDiffOn ℝ ∞ A N := hq.deriv_of_isOpen hN (by simp)
  have hαd (r : ℝ) (hr : r ∈ N) : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) α r :=
    ((hα r hr.1).contMDiffAt (hU.mem_nhds hr.1)).mdifferentiableAt (by simp)
  have hfield (r : ℝ) (hr : r ∈ C ∩ N) :
      chartFrame x (A r) (α r) = curveVelocityWithin (n := n) α C r := by
    rw [chartFrame_curveVelocity hr.2.2 (hαd r hr.2)]
    unfold curveVelocityWithin curveVelocity
    rw [mfderivWithin_eq_mfderiv (hC r hr.1).uniqueMDiffWithinAt (hαd r hr.2)]
  have htarget : q s ∈ e.target := e.map_source
    (by simpa only [e, extChartAt_source] using hx)
  have hprod : C ×ˢ e.target ∈ 𝓝 (s, q s) :=
    prod_mem_nhds hsN ((isOpen_extChartAt_target (I := 𝓡 n) x).mem_nhds htarget)
  have hGd : DifferentiableAt ℝ G (s, q s) :=
    (((chartActionMetric_closed_contDiffOn F T x htime) (s, q s) ⟨hs, htarget⟩).contDiffAt
      hprod).differentiableAt (by simp)
  have hqd : DifferentiableAt ℝ q s :=
    ((hq s hsN').contDiffAt (hN.mem_nhds hsN')).differentiableAt (by simp)
  have hAd : HasDerivAt A (deriv A s) s :=
    (((hA s hsN').contDiffAt (hN.mem_nhds hsN')).differentiableAt (by simp)).hasDerivAt
  have hGc : HasDerivAt (fun r ↦ G (r, q r)) (fderiv ℝ G (s, q s) (1, A s)) s := by
    simpa only [Function.comp_def, id_eq] using
      hGd.hasFDerivAt.comp_hasDerivAt s ((hasDerivAt_id s).prodMk hqd.hasDerivAt)
  have hp := (hGc.clm_apply hAd).clm_apply hAd
  have hpb := pullbackCovariantDerivative_chart_formula_local F (fun r ↦ T - r ^ 2)
    hN x α A hA (fun r hr ↦ hr.2.2) _ hfield E hs hsN' (hC s hs) (hαd s hsN')
  have hDA : pullbackCovariantDerivative F (fun r ↦ T - r ^ 2) α
      (curveVelocityWithin (n := n) α C) C E s =
    chartFrame x (deriv A s + closedChartChristoffel F T x C (s, q s) (A s) (A s)) (α s) := by
    rw [hpb, closedChartChristoffel_connection F T htime hx hs]
    exact ((trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x).symmL ℝ
      (α s)).map_add _ _ |>.symm
  have hspace := chartActionMetric_spatial_compatibility F T htime hx hs (A s) (A s) (A s)
  change spatialWithinFDeriv C e.target G (s, q s) (A s) (A s) (A s) = _ at hspace
  rw [spatialWithinFDeriv_apply_of_mem_nhds G hprod (A s)] at hspace
  have hsplit : fderiv ℝ G (s, q s) (1, A s) (A s) (A s) =
      fderiv ℝ G (s, q s) (1, 0) (A s) (A s) +
      G (s, q s) (closedChartChristoffel F T x C (s, q s) (A s) (A s)) (A s) +
      G (s, q s) (A s) (closedChartChristoffel F T x C (s, q s) (A s) (A s)) := by
    rw [show ((1 : ℝ), A s) = (1, (0 : EuclideanSpace ℝ (Fin n))) + (0, A s) by simp,
      map_add, add_apply, add_apply, hspace]
    dsimp only [G, q, e, Function.comp_def]
    ring
  have htimeG := chartActionMetric_time_pair_interior F hM04 T hC htime hx hs hsN (A s) (A s)
  have hpair : (fderiv ℝ G (s, q s) (1, A s) (A s) +
        G (s, q s) (deriv A s)) (A s) + G (s, q s) (A s) (deriv A s) =
      2 * (F.metric (T - s ^ 2)).inner (α s)
        (pullbackCovariantDerivative F (fun r ↦ T - r ^ 2) α
          (curveVelocityWithin (n := n) α C) C E s) (curveVelocityWithin (n := n) α C s) +
      4 * s * (F.connection (T - s ^ 2)).ricci (α s)
        (curveVelocityWithin (n := n) α C s) (curveVelocityWithin (n := n) α C s) := by
    rw [hDA, ← hfield s ⟨hs, hsN'⟩, ← chartActionMetric_apply F T hx,
      ← htimeG, add_apply, hsplit]
    simp only [map_add, add_apply]
    dsimp only [G, q, e, Function.comp_def]
    rw [chartActionMetric_symm_at F T hx s (deriv A s) (A s),
      chartActionMetric_symm_at F T hx s
        (closedChartChristoffel F T x C (s, extChartAt (𝓡 n) x (α s)) (A s) (A s)) (A s)]
    ring
  rw [hpair] at hp
  apply hp.congr_of_eventuallyEq
  filter_upwards [hsN, hN.mem_nhds hsN'] with r hrC hrN
  dsimp only [G, q, e, Function.comp_def]
  rw [chartActionMetric_apply F T hrN.2, hfield r ⟨hrC, hrN⟩]
  rfl

theorem regularized_continuationSpeedSq_hasDerivAt {J : Set ℝ} {F : RicciFlow n M J}
    {T τ₁ τ₂ : ℝ} (hM04 : RicciFlowCurvatureTheory.{u})
    {p : BackwardTimePath F T τ₁ τ₂} (R : RegularizedLGeodesicData p) {s : ℝ}
    (hs : s ∈ Ioo (Real.sqrt τ₁) (Real.sqrt τ₂)) :
    HasDerivAt (continuationSpeedSq F T R.path.curve (sqrtParameterInterval τ₁ τ₂))
      (4 * s ^ 2 * scalarCurvatureDifferential F (fun r ↦ T - r ^ 2) R.path.curve s
          (curveVelocityWithin (n := n) R.path.curve (sqrtParameterInterval τ₁ τ₂) s) -
        4 * s * (F.connection (T - s ^ 2)).ricci (R.path.curve s)
          (curveVelocityWithin (n := n) R.path.curve (sqrtParameterInterval τ₁ τ₂) s)
          (curveVelocityWithin (n := n) R.path.curve (sqrtParameterInterval τ₁ τ₂) s)) s := by
  have hsC : s ∈ sqrtParameterInterval τ₁ τ₂ := Ioo_subset_Icc_self hs
  have htime (r : ℝ) (hr : r ∈ sqrtParameterInterval τ₁ τ₂) : T - r ^ 2 ∈ J :=
    p.time_mem _ (square_mem_backward_interval p hr)
  have h := continuationSpeedSq_hasDerivAt F hM04 T R.path.curve
    (uniqueDiffOn_Icc (Real.sqrt_lt_sqrt p.nonnegative p.ordered)) R.path.open_domain
    R.path.interval_subset R.path.smooth htime R.velocity_extension hsC (Icc_mem_nhds hs.1 hs.2)
  have heq := R.equation s hsC
    (curveVelocityWithin (n := n) R.path.curve (sqrtParameterInterval τ₁ τ₂) s)
  unfold regularizedEulerResidual at heq
  convert h using 1 <;> dsimp only [sqrtParameterInterval] at heq ⊢ <;> linarith

theorem backward_gronwall_bound {q q' : ℝ → ℝ} {a c C : ℝ}
    (hq : ContinuousOn q (Icc a c))
    (hqd : ∀ s ∈ Ioo a c, HasDerivAt q (q' s) s)
    (hbound : ∀ s ∈ Ioo a c, -(C * (q s + 1)) ≤ q' s)
    {s : ℝ} (hs : s ∈ Icc a c) :
    q s + 1 ≤ Real.exp (C * (c - s)) * (q c + 1) := by
  let f := fun r ↦ Real.exp (C * r) * (q r + 1)
  have hf : ContinuousOn f (Icc a c) :=
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn).mul
      (hq.add continuousOn_const)
  have hfd (r : ℝ) (hr : r ∈ Ioo a c) :
      HasDerivAt f (Real.exp (C * r) * (q' r + C * (q r + 1))) r := by
    convert (((hasDerivAt_id r).const_mul C).exp).mul ((hqd r hr).add_const 1) using 1 <;>
      first | rfl | (simp only [id_eq, mul_one]; ring)
  have hmono : MonotoneOn f (Icc a c) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a c) hf
      (f' := fun r ↦ Real.exp (C * r) * (q' r + C * (q r + 1)))
    · intro r hr
      rw [interior_Icc] at hr
      exact (hfd r hr).hasDerivWithinAt
    · intro r hr
      rw [interior_Icc] at hr
      exact mul_nonneg (Real.exp_pos _).le (by linarith [hbound r hr])
  have hsc := hmono hs ⟨hs.1.trans hs.2, le_rfl⟩ hs.2
  change Real.exp (C * s) * (q s + 1) ≤ Real.exp (C * c) * (q c + 1) at hsc
  calc
    q s + 1 = (Real.exp (C * s) * (q s + 1)) / Real.exp (C * s) := by
      field_simp
    _ ≤ (Real.exp (C * c) * (q c + 1)) / Real.exp (C * s) :=
      div_le_div_of_nonneg_right hsc (Real.exp_pos _).le
    _ = Real.exp (C * (c - s)) * (q c + 1) := by
      rw [mul_div_right_comm, ← Real.exp_sub, mul_sub]

theorem backward_gronwall_uniform_bound {q q' : ℝ → ℝ} {a c C : ℝ}
    (ha : 0 ≤ a) (hC : 0 ≤ C) (hqc : 0 ≤ q c)
    (hq : ContinuousOn q (Icc a c))
    (hqd : ∀ s ∈ Ioo a c, HasDerivAt q (q' s) s)
    (hbound : ∀ s ∈ Ioo a c, -(C * (q s + 1)) ≤ q' s)
    {s : ℝ} (hs : s ∈ Icc a c) :
    q s ≤ Real.exp (C * c) * (q c + 1) := by
  have h := backward_gronwall_bound hq hqd hbound hs
  have hexp : Real.exp (C * (c - s)) ≤ Real.exp (C * c) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left (sub_le_self c (ha.trans hs.1)) hC
  nlinarith [mul_le_mul_of_nonneg_right hexp (by linarith : 0 ≤ q c + 1)]

end PoincareConjecture.M08
