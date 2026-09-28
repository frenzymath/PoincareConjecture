import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerHarmonicDecay
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.Eigenfunction
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.WeakDerivativeLimit











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped ContDiff Topology

noncomputable section

namespace PoincareConjecture.M60

open Poincare.Analysis.Sobolev.Weak
open Poincare.Analysis.Elliptic.Iteration
open Poincare.Analysis.Elliptic.InteriorEstimates

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "L" => secondOrderOperator (fun _ : Plane => (1 : Matrix (Fin 2) (Fin 2) ℝ))
  (fun _ : Fin 2 => fun _ : Plane => (0 : ℝ))



theorem suWeak_partial_congr {O : Set Plane} {u v p q : Plane → ℝ} {i : Fin 2}
    (hw : HasWeakPartialDeriv i p u O)
    (huv : u =ᵐ[volume.restrict O] v) (hpq : p =ᵐ[volume.restrict O] q) :
    HasWeakPartialDeriv i q v O := by
  intro φ hφ hφc hφO
  calc
    _ = ∫ x in O, u x * fderiv ℝ φ x (EuclideanSpace.single i 1) := by
      apply integral_congr_ae
      filter_upwards [huv] with x hx using congrArg
        (fun t => t * fderiv ℝ φ x (EuclideanSpace.single i 1)) hx.symm
    _ = -(∫ x in O, p x * φ x) := hw φ hφ hφc hφO
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [hpq] with x hx using congrArg (fun t => t * φ x) hx




theorem suPlane_partial_smooth {O : Set Plane} (hO : IsOpen O) {u : Plane → ℝ}
    (hu : ContDiffOn ℝ ∞ u O) (i : Fin 2) :
    ContDiffOn ℝ ∞ (partialDeriv i u) O :=
  (hu.fderiv_of_isOpen hO (m := ∞) (by simp)).clm_apply contDiffOn_const




theorem suHarmonic_partial {O : Set Plane} (hO : IsOpen O) {u : Plane → ℝ}
    (hu : ContDiffOn ℝ ∞ u O) (hz : EqOn (L u) (fun _ => 0) O) (i : Fin 2) :
    EqOn (L (partialDeriv i u)) (fun _ => 0) O := by
  intro x hx
  obtain ⟨r, hr, hrO⟩ := Metric.mem_nhds_iff.mp (hO.mem_nhds hx)
  let V := Metric.ball x (r / 2)
  have hV : IsOpen V := Metric.isOpen_ball
  have hxV : x ∈ V := Metric.mem_ball_self (half_pos hr)
  have hVc : IsCompact (closure V) := by
    simpa only [V, closure_ball x (half_pos hr).ne'] using isCompact_closedBall x (r / 2)
  have hVO : closure V ⊆ O := Metric.closure_ball_subset_closedBall.trans
    ((Metric.closedBall_subset_ball (half_lt_self hr)).trans hrO)
  obtain ⟨v, hv, hvu⟩ := exists_smooth_extension_on_precompact hO hVc hVO hu
  have hevent : v =ᶠ[𝓝 x] u := by
    filter_upwards [hV.mem_nhds hxV] with y hy using hvu hy
  have hpartial : partialDeriv i v =ᶠ[𝓝 x] partialDeriv i u := by
    filter_upwards [hevent.fderiv (𝕜 := ℝ)] with y hy
    exact congrArg (fun A : Plane →L[ℝ] ℝ => A (EuclideanSpace.single i 1)) hy
  have hLv : EqOn (L v) (L u) V := secondOrderOperator_eqOn
    (b := fun _ : Fin 2 => fun _ : Plane => (0 : ℝ)) hV (fun _ _ => rfl)
    (fun _ _ _ => rfl) hvu
  have hLzero : L v =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [hV.mem_nhds hxV] with y hy
    exact (hLv hy).trans (hz (hVO (subset_closure hy)))
  rw [← secondOrderOperator_eq_of_eventuallyEq _ _ hpartial,
    suPlaneLaplace_partial hv i]
  change fderiv ℝ (L v) x (EuclideanSpace.single i 1) = 0
  rw [hLzero.fderiv_eq]
  simp



theorem suPlaneLaplace_smooth {O : Set Plane} (hO : IsOpen O) {u : Plane → ℝ}
    (hu : ContDiffOn ℝ ∞ u O) : ContDiffOn ℝ ∞ (L u) O := by
  have heq : L u = fun x => partialDeriv 0 (partialDeriv 0 u) x +
      partialDeriv 1 (partialDeriv 1 u) x := by
    ext x
    simp [secondOrderOperator, Matrix.one_apply, Fin.sum_univ_two]
  rw [heq]
  exact (suPlane_partial_smooth hO (suPlane_partial_smooth hO hu 0) 0).add
    (suPlane_partial_smooth hO (suPlane_partial_smooth hO hu 1) 1)

private theorem smooth_mul_test_integrable {O : Set Plane} (hO : IsOpen O)
    {f φ : Plane → ℝ} (hf : ContinuousOn f O) (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) (hφO : tsupport φ ⊆ O) :
    IntegrableOn (fun x => f x * φ x) O := by
  have hcont : Continuous (fun x => φ x * f x) :=
    (hφ.continuous.continuousOn.mul hf).continuous_of_tsupport_subset hO
      (tsupport_mul_subset_left.trans hφO)
  simpa only [mul_comm] using
    (hcont.integrable_of_hasCompactSupport hφc.mul_right).integrableOn (s := O)




theorem suPlaneLaplace_zero_of_weak {O : Set Plane} (hO : IsOpen O) {u : Plane → ℝ}
    (hu : ContDiffOn ℝ ∞ u O)
    (heq : ∀ φ : Plane → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ O →
      (∫ x in O, ∑ i : Fin 2, partialDeriv i u x * partialDeriv i φ x) = 0) :
    EqOn (L u) (fun _ => 0) O := by
  have hcont := (suPlaneLaplace_smooth hO hu).continuousOn
  have haezero : ∀ᵐ x ∂volume, x ∈ O → L u x = 0 := by
    apply hO.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hcont.locallyIntegrableOn hO.measurableSet)
    intro φ hφ hφc hφO
    have hp (i) := suPlane_partial_smooth hO hu i
    have hpp (i j) := suPlane_partial_smooth hO (hp i) j
    have hint (i) : IntegrableOn (fun x => partialDeriv i u x * partialDeriv i φ x) O :=
      smooth_mul_test_integrable hO (hp i).continuousOn (contDiff_partial hφ i)
        (hasCompactSupport_partial hφc i) ((tsupport_partial_subset i φ).trans hφO)
    have hint' (i) : IntegrableOn
        (fun x => partialDeriv i (partialDeriv i u) x * φ x) O :=
      smooth_mul_test_integrable hO (hpp i i).continuousOn hφ hφc hφO
    have he := heq φ hφ hφc hφO
    simp only [Fin.sum_univ_two] at he
    rw [integral_add (hint 0) (hint 1)] at he
    have hzero : ∀ x, x ∉ O → φ x • L u x = 0 := by
      intro x hx
      rw [image_eq_zero_of_notMem_tsupport (fun ht => hx (hφO ht)), zero_smul]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
    have hform (x : Plane) : φ x • L u x =
        partialDeriv 0 (partialDeriv 0 u) x * φ x +
          partialDeriv 1 (partialDeriv 1 u) x * φ x := by
      simp [secondOrderOperator, Matrix.one_apply, Fin.sum_univ_two, smul_eq_mul,
        mul_add, mul_comm]
    simp_rw [hform]
    rw [integral_add (hint' 0) (hint' 1)]
    have h0 := Poincare.Analysis.Elliptic.integral_mul_partial_test hO (hp 0)
      (EuclideanSpace.single 0 1) hφ hφc hφO
    have h1 := Poincare.Analysis.Elliptic.integral_mul_partial_test hO (hp 1)
      (EuclideanSpace.single 1 1) hφ hφc hφO
    change (∫ x in O, partialDeriv 0 u x * partialDeriv 0 φ x) =
      -(∫ x in O, partialDeriv 0 (partialDeriv 0 u) x * φ x) at h0
    change (∫ x in O, partialDeriv 1 u x * partialDeriv 1 φ x) =
      -(∫ x in O, partialDeriv 1 (partialDeriv 1 u) x * φ x) at h1
    linarith
  have hae : L u =ᵐ[volume.restrict O] fun _ => 0 :=
    (ae_restrict_iff' hO.measurableSet).mpr haezero
  exact Measure.eqOn_open_of_ae_eq hae hO hcont continuousOn_const

private theorem continuous_memLp_two_precompact {O V : Set Plane}
    (hV : IsOpen V) (hVc : IsCompact (closure V)) (hVO : closure V ⊆ O)
    {f : Plane → ℝ} (hf : ContinuousOn f O) : MemLp f 2 (volume.restrict V) := by
  have hfm : AEStronglyMeasurable f (volume.restrict V) :=
    (hf.mono (subset_closure.trans hVO)).aestronglyMeasurable hV.measurableSet
  apply (memLp_two_iff_integrable_sq hfm).mpr
  exact ((hf.mono hVO).pow 2).integrableOn_compact hVc |>.mono_set subset_closure




theorem suWeakHarmonic_representative {O V : Set Plane}
    (hO : IsOpen O) (hV : IsOpen V) (hVc : IsCompact (closure V))
    (hVO : closure V ⊆ O) {u : Plane → ℝ} {p : Fin 2 → Plane → ℝ}
    (hu : MemLp u 2 (volume.restrict O))
    (hp : ∀ i, MemLp (p i) 2 (volume.restrict O))
    (hw : ∀ i, HasWeakPartialDeriv i (p i) u O)
    (heq : WeakEquation O p (fun _ => 0)) :
    ∃ U : Plane → ℝ, ContDiffOn ℝ ∞ U O ∧ U =ᵐ[volume.restrict O] u ∧
      (∀ i, partialDeriv i U =ᵐ[volume.restrict V] p i) ∧ EqOn (L U) (fun _ => 0) V := by
  obtain ⟨U, hU, hUu⟩ := Poincare.Analysis.Elliptic.exists_smooth_representative
    (by norm_num : 0 < 2) hO (fun _ : Plane => (1 : Matrix (Fin 2) (Fin 2) ℝ))
    (fun _ => 0) u p (fun _ _ => contDiffOn_const) (fun _ _ => Matrix.PosDef.one)
    contDiffOn_const
    (fun _ _ hKO => hu.mono_measure (Measure.restrict_mono hKO le_rfl))
    (fun i _ _ hKO => (hp i).mono_measure (Measure.restrict_mono hKO le_rfl)) hw (by
      intro φ hφ hφc hφO
      simpa [Matrix.one_apply, partialDeriv] using heq φ hφ hφc hφO)
  have hsub : V ⊆ O := subset_closure.trans hVO
  have hUuV := hUu.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))
  have hgrad (i : Fin 2) : partialDeriv i U =ᵐ[volume.restrict V] p i := by
    have hwV := suWeak_partial_congr ((hw i).restrict hV hsub) hUuV.symm (Filter.EventuallyEq.rfl)
    have hclass : HasWeakPartialDeriv i (partialDeriv i U) U V :=
      fun _ hφ hφc hφV => Poincare.Analysis.Elliptic.integral_mul_partial_test
        hV (hU.mono hsub) (EuclideanSpace.single i 1) hφ hφc hφV
    exact HasWeakPartialDeriv.ae_eq hV hclass hwV
      ((continuous_memLp_two_precompact hV hVc hVO
        (suPlane_partial_smooth hO hU i).continuousOn).locallyIntegrable (by norm_num))
      (((hp i).mono_measure (Measure.restrict_mono hsub le_rfl)).locallyIntegrable (by norm_num))
  refine ⟨U, hU, hUu, hgrad, ?_⟩
  apply suPlaneLaplace_zero_of_weak hV (hU.mono hsub)
  intro φ hφ hφc hφV
  have he := ((heq.restrict hsub).congr_flux (fun i => (hgrad i).symm)) φ hφ hφc hφV
  simpa only [zero_mul, integral_zero, partialDeriv] using he




theorem suWeakHarmonic_hessian {O V : Set Plane}
    (hO : IsOpen O) (hV : IsOpen V) (hVc : IsCompact (closure V))
    (hVO : closure V ⊆ O) {u : Plane → ℝ} {p : Fin 2 → Plane → ℝ}
    {H : Fin 2 → Fin 2 → Plane → ℝ}
    (hu : MemLp u 2 (volume.restrict O))
    (hp : ∀ i, MemLp (p i) 2 (volume.restrict O))
    (hw : ∀ i, HasWeakPartialDeriv i (p i) u O)
    (hH : ∀ i j, MemLp (H i j) 2 (volume.restrict V))
    (hwH : ∀ i j, HasWeakPartialDeriv j (H i j) (p i) V)
    (heq : WeakEquation O p (fun _ => 0)) :
    ∃ U : Plane → ℝ, ContDiffOn ℝ ∞ U O ∧ EqOn (L U) (fun _ => 0) V ∧
      ∀ i j, partialDeriv j (partialDeriv i U) =ᵐ[volume.restrict V] H i j := by
  obtain ⟨U, hU, _, hgrad, hzero⟩ := suWeakHarmonic_representative hO hV hVc hVO hu hp hw heq
  refine ⟨U, hU, hzero, ?_⟩
  intro i j
  have hwH' := suWeak_partial_congr (hwH i j) (hgrad i).symm (Filter.EventuallyEq.rfl)
  have hclass : HasWeakPartialDeriv j (partialDeriv j (partialDeriv i U))
      (partialDeriv i U) V :=
    fun _ hφ hφc hφV => Poincare.Analysis.Elliptic.integral_mul_partial_test hV
      ((suPlane_partial_smooth hO hU i).mono (subset_closure.trans hVO))
      (EuclideanSpace.single j 1) hφ hφc hφV
  exact HasWeakPartialDeriv.ae_eq hV hclass hwH'
    ((continuous_memLp_two_precompact hV hVc hVO
      (suPlane_partial_smooth hO (suPlane_partial_smooth hO hU i) j).continuousOn
        ).locallyIntegrable (by norm_num))
    ((hH i j).locallyIntegrable (by norm_num))




theorem suWeakHarmonic_hessian_decay :
    ∃ C : ℝ, 0 < C ∧ ∀ {u : Plane → ℝ} {p : Fin 2 → Plane → ℝ}
      {H : Fin 2 → Fin 2 → Plane → ℝ},
      MemLp u 2 (volume.restrict (Metric.ball 0 1)) →
      (∀ i, MemLp (p i) 2 (volume.restrict (Metric.ball 0 1))) →
      (∀ i, HasWeakPartialDeriv i (p i) u (Metric.ball 0 1)) →
      (∀ i j, MemLp (H i j) 2 (volume.restrict (Metric.ball 0 (1 / 2)))) →
      (∀ i j, HasWeakPartialDeriv j (H i j) (p i) (Metric.ball 0 (1 / 2))) →
      WeakEquation (Metric.ball 0 1) p (fun _ => 0) →
      ∀ r : ℝ, 0 < r → r ≤ 1 / 4 →
        (∫ x in Metric.ball 0 r, ∑ i : Fin 2, ∑ j : Fin 2, H i j x ^ 2) ≤
          C * r ^ 2 * ∫ x in Metric.ball 0 (1 / 2),
            ∑ i : Fin 2, ∑ j : Fin 2, H i j x ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := suHarmonic_disk_decay
  refine ⟨4 * C, by positivity, ?_⟩
  intro u p H hu hp hw hH hwH heq r hr hr1
  have hVc : IsCompact (closure (Metric.ball (0 : Plane) (1 / 2))) := by
    rw [closure_ball (0 : Plane) (by norm_num : (1 / 2 : ℝ) ≠ 0)]
    exact isCompact_closedBall (0 : Plane) (1 / 2 : ℝ)
  have hVO : closure (Metric.ball (0 : Plane) (1 / 2)) ⊆ Metric.ball 0 1 :=
    Metric.closure_ball_subset_closedBall.trans (Metric.closedBall_subset_ball (by norm_num))
  obtain ⟨U, hU, hzero, hHess⟩ := suWeakHarmonic_hessian Metric.isOpen_ball Metric.isOpen_ball
    hVc hVO hu hp hw hH hwH heq
  have hUs : ContDiffOn ℝ ∞ U (Metric.ball 0 (1 / 2)) :=
    hU.mono (Metric.ball_subset_ball (by norm_num))
  have hsmall : Metric.ball (0 : Plane) r ⊆ Metric.ball 0 (1 / 2) :=
    Metric.ball_subset_ball (by linarith)
  have hcomponent (i j : Fin 2) :
      (∫ x in Metric.ball 0 r, H i j x ^ 2) ≤
        4 * C * r ^ 2 * ∫ x in Metric.ball 0 (1 / 2), H i j x ^ 2 := by
    have hps := suPlane_partial_smooth Metric.isOpen_ball hUs i
    have hph := suHarmonic_partial Metric.isOpen_ball hUs hzero i
    have hpps := suPlane_partial_smooth Metric.isOpen_ball hps j
    have hpph := suHarmonic_partial Metric.isOpen_ball hps hph j
    have hpm := (hH i j).ae_eq (hHess i j).symm
    have hb := hbound 0 (by norm_num : (0 : ℝ) < 1 / 2) hr (by linarith)
      hpps hpph hpm
    have hsq : (fun x => partialDeriv j (partialDeriv i U) x ^ 2)
        =ᵐ[volume.restrict (Metric.ball 0 (1 / 2))] fun x => H i j x ^ 2 := by
      filter_upwards [hHess i j] with x hx using congrArg (fun t : ℝ => t ^ 2) hx
    have hsqSmall := hsq.filter_mono (ae_mono (Measure.restrict_mono hsmall le_rfl))
    rw [integral_congr_ae hsqSmall, integral_congr_ae hsq] at hb
    convert hb using 1
    ring
  have hi (i j : Fin 2) := (hH i j).integrable_sq
  have his (i j : Fin 2) :=
    ((hH i j).mono_measure (Measure.restrict_mono hsmall le_rfl)).integrable_sq
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => his i j)),
    integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j)),
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [integral_finsetSum _ (fun j _ => his i j),
    integral_finsetSum _ (fun j _ => hi i j), Finset.mul_sum]
  exact Finset.sum_le_sum fun j _ => hcomponent i j

end PoincareConjecture.M60

end
