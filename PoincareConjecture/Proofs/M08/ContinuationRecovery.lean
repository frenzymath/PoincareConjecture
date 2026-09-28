import PoincareConjecture.Proofs.M08.ContinuationLimit
import PoincareConjecture.Proofs.M08.ContinuationCurve
import PoincareConjecture.Proofs.M08.ManifoldEndpointExtension

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareConjecture.M08

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local instance continuationRecoveryDualGroup : NormedAddCommGroup (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance continuationRecoveryDualSpace : NormedSpace ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance continuationRecoveryBilinGroup :
    NormedAddCommGroup (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance continuationRecoveryBilinSpace :
    NormedSpace ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

private theorem recovery_referenceSpeedSq_congr (g : RiemannianMetric n M)
    {α β : ℝ → M} {s : ℝ} (h : β =ᶠ[𝓝 s] α) :
    referenceSpeedSq g β s = referenceSpeedSq g α s := by
  unfold referenceSpeedSq curveVelocity
  rw [h.mfderiv_eq, h.self_of_nhds]

set_option maxHeartbeats 2000000 in

theorem exists_continuation_endpoint_phase [ConnectedSpace M] [T3Space M]
    {J : Set ℝ} (F : RicciFlow n M J) (hM04 : RicciFlowCurvatureTheory.{u})
    (T : ℝ) (g : RiemannianMetric n M) (hg : MetricComplete g)
    {a c b L : ℝ} (hac : a < c) (hcb : c < b) (hL : 0 ≤ L)
    (α : ℝ → M) (hα : IsContinuationCurve F T α (Ioo a b))
    (hspeed : ∀ s ∈ Ioc a c, referenceSpeedSq g α s ≤ L)
    (htime : ∀ s ∈ Icc a c, T - s ^ 2 ∈ J) :
    ∃ (β : ℝ → M) (d : ℝ) (Pbar : ℝ → EuclideanSpace ℝ (Fin n)),
      ContinuousOn β (Icc a c) ∧ EqOn β α (Ioi a) ∧
      ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ β (Icc a c) ∧ a < d ∧ d < c ∧
      MapsTo β (Icc a d) (chartAt (EuclideanSpace ℝ (Fin n)) (β a)).source ∧
      ContDiffOn ℝ ∞ (fun s ↦ (extChartAt (𝓡 n) (β a) (β s), Pbar s)) (Icc a d) ∧
      EqOn Pbar (fun s ↦ chartMetricOperator F T (β a)
        (s, extChartAt (𝓡 n) (β a) (β s))
        (deriv ((extChartAt (𝓡 n) (β a)) ∘ β) s)) (Ioo a d) ∧
      ∀ s ∈ Icc a d, HasDerivWithinAt
        (fun r ↦ (extChartAt (𝓡 n) (β a) (β r), Pbar r))
        (closedChartEulerPhase F T (β a) (Icc a d) s
          (extChartAt (𝓡 n) (β a) (β s), Pbar s)) (Icc a d) s := by
  classical
  letI : MetricSpace M := referenceMetricSpace g
  letI : CompleteSpace M := referenceMetricSpace_complete g hg
  have hsub : Ioc a c ⊆ Ioo a b := fun s hs ↦ ⟨hs.1, hs.2.trans_lt hcb⟩
  have hLip := lipschitzOnWith_of_referenceSpeed_bound g hL isOpen_Ioo hsub α
    (hα.smooth.of_le (by simp)) hspeed
  obtain ⟨γ, hγ, hγα, _⟩ := exists_continuous_endpoint_of_lipschitz hac α hLip
  let β : ℝ → M := fun s ↦ if s = a then γ a else α s
  have hβα : EqOn β α (Ioi a) := by
    intro s hs
    exact if_neg (ne_of_gt hs)
  have hβγ : EqOn β γ (Icc a c) := by
    intro s hs
    by_cases hsa : s = a
    · subst s
      simp only [β, if_pos rfl]
    · have has : a < s := lt_of_le_of_ne hs.1 (Ne.symm hsa)
      exact (hβα has).trans (hγα ⟨has, hs.2⟩).symm
  have hβc : ContinuousOn β (Icc a c) := hγ.congr hβγ
  have hβU : IsContinuationCurve F T β (Ioo a b) :=
    hα.congr isOpen_Ioo (fun s hs ↦ hβα hs.1)
  obtain ⟨d, d', had, hdc, _, _, hsrc, _⟩ := endpoint_chart_intervals (n := n) hac β hβc
  let x := β a
  let e := extChartAt (𝓡 n) x
  let q := e ∘ β
  have hsmall : Icc a d ⊆ Icc a c := Icc_subset_Icc le_rfl hdc.le
  have hopen : Ioo a d ⊆ Ioo a b := Ioo_subset_Ioo le_rfl (hdc.trans hcb).le
  have hβreg : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ β (Ioo a d) := hβU.smooth.mono hopen
  have hsrc' : MapsTo β (Icc a d) e.source := by
    simpa only [e, x, extChartAt_source] using hsrc
  have htarget : MapsTo q (Icc a d) e.target := fun s hs ↦ e.map_source (hsrc' hs)
  have hq : ContinuousOn q (Icc a d) :=
    (continuousOn_extChartAt (I := 𝓡 n) x).comp (hβc.mono hsmall) hsrc'
  have hqd (s : ℝ) (hs : s ∈ Ioo a d) : HasDerivAt q (deriv q s) s := by
    have hm := ((hβreg s hs).contMDiffAt (isOpen_Ioo.mem_nhds hs)).mdifferentiableAt (by simp)
    exact ((mdifferentiableAt_extChartAt (hsrc (Ioo_subset_Icc_self hs))).comp s hm).differentiableAt.hasDerivAt
  have hβspeed (s : ℝ) (hs : s ∈ Ioo a d) : referenceSpeedSq g β s ≤ L := by
    have hnear : β =ᶠ[𝓝 s] α :=
      Filter.eventuallyEq_of_mem (isOpen_Ioi.mem_nhds hs.1) hβα
    rw [recovery_referenceSpeedSq_congr g hnear]
    exact hspeed s ⟨hs.1, hs.2.le.trans hdc.le⟩
  have hqmeas : AEStronglyMeasurable (referenceSpeedSq g β) (volume.restrict (Icc a d)) := by
    rw [← restrict_Ioo_eq_restrict_Icc]
    exact (referenceSpeedSq_continuousOn g isOpen_Ioo (hβreg.of_le (by simp))).aestronglyMeasurable
      measurableSet_Ioo
  have hqbound : ∀ᵐ s ∂volume.restrict (Icc a d), ‖referenceSpeedSq g β s‖ ≤ L := by
    rw [← restrict_Ioo_eq_restrict_Icc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    simpa only [Real.norm_eq_abs, abs_of_nonneg (referenceSpeedSq_nonneg g β s)] using hβspeed s hs
  have hE : IntervalIntegrable (referenceSpeedSq g β) volume a d := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le had.le).mpr
    exact (show Integrable (fun _ : ℝ ↦ L) (volume.restrict (Icc a d)) from
      integrable_const L).mono' hqmeas hqbound
  obtain ⟨k, hk, hcoercive⟩ := chart_velocity_L2_bound g x
    (isCompact_Icc.image_of_continuousOn (hβc.mono hsmall))
    (by rintro y ⟨s, hs, rfl⟩; exact hsrc hs)
  obtain ⟨hd, _⟩ := hcoercive had.le β (hβreg.of_le (by simp))
    (fun s hs ↦ mem_image_of_mem β hs) hE le_rfl
  have hmomentum (s : ℝ) (hs : s ∈ Ioo a d) :
      HasDerivAt (fun r ↦ chartMetricOperator F T x (r, q r) (deriv q r))
        (chartForceVector
          (spatialWithinFDeriv (Icc a d) e.target (chartActionMetric F T x) (s, q s))
          (spatialWithinFDeriv (Icc a d) e.target (chartActionPotential F T x) (s, q s))
          (deriv q s)) s := by
    rw [spatialWithinFDeriv_eq_spatialFDeriv (isOpen_extChartAt_target (I := 𝓡 n) x)
        _ (Icc_mem_nhds hs.1 hs.2) (htarget (Ioo_subset_Icc_self hs)),
      spatialWithinFDeriv_eq_spatialFDeriv (isOpen_extChartAt_target (I := 𝓡 n) x)
        _ (Icc_mem_nhds hs.1 hs.2) (htarget (Ioo_subset_Icc_self hs))]
    exact continuationCurve_momentum F T hβU (hopen hs) x (hsrc (Ioo_subset_Icc_self hs))
  obtain ⟨Pbar, hP, hPeq, hPd⟩ := endpoint_chart_phase_contDiffOn F hM04 T x had
    q (deriv q) hq hqd hd htarget (fun s hs ↦ htime s (hsmall hs)) hmomentum
  have hβlocal : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ β (Icc a d) := by
    have h := (contMDiffOn_extChartAt_symm (I := 𝓡 n) x).comp hP.fst.contMDiffOn htarget
    exact h.congr (fun s hs ↦ (e.left_inv (hsrc' hs)).symm)
  have hβsmooth : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ β (Icc a c) := by
    intro s hs
    by_cases hsa : s = a
    · subst s
      have hnhds : Icc a d ∈ 𝓝[Icc a c] a := by
        apply mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
        refine ⟨Iio d, isOpen_Iio.mem_nhds had, ?_⟩
        intro r hr
        exact ⟨hr.2.1, hr.1.le⟩
      exact (hβlocal a ⟨le_rfl, had.le⟩).mono_of_mem_nhdsWithin hnhds
    · have hsU : s ∈ Ioo a b := ⟨lt_of_le_of_ne hs.1 (Ne.symm hsa), hs.2.trans_lt hcb⟩
      exact ((hβU.smooth s hsU).contMDiffAt (isOpen_Ioo.mem_nhds hsU)).contMDiffWithinAt
  exact ⟨β, d, Pbar, hβc, hβα, hβsmooth, had, hdc, hsrc, hP, hPeq, hPd⟩

end PoincareConjecture.M08
