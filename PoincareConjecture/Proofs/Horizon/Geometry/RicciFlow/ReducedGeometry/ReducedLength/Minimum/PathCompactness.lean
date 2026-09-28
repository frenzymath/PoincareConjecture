import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Ancient.Sequence.Coercivity.Metric
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Ancient.Sequence.Coercivity.Curve
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Ancient.Sequence.Infimum
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.CompleteBalls
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.MetricSpace.Equicontinuity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open Filter
open scoped Manifold ContDiff Bundle intervalIntegral Topology BoundedContinuousFunction

universe u

namespace PoincareConjecture.ReducedLengthMinimum

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

noncomputable def referenceSpeedSq (g : RiemannianMetric n M)
    (γ : ℝ → M) (s : ℝ) : ℝ :=
  g.inner (γ s) (curveVelocity (n := n) γ s) (curveVelocity (n := n) γ s)

theorem referenceSpeedSq_nonneg (g : RiemannianMetric n M)
    (γ : ℝ → M) (s : ℝ) : 0 ≤ referenceSpeedSq g γ s := by
  by_cases hv : curveVelocity (n := n) γ s = 0
  · simp [referenceSpeedSq, hv]
  · exact (g.pos (γ s) _ hv).le

theorem referenceSpeedSq_continuousOn {γ : ℝ → M} {I : Set ℝ}
    (g : RiemannianMetric n M) (hI : IsOpen I)
    (hγ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) 1 γ I) :
    ContinuousOn (referenceSpeedSq g γ) I := by
  have h := (g.continuousOn_speed_of_contMDiffOn_one hI hγ).pow 2
  apply h.congr
  intro s _
  exact (Real.sq_sqrt (referenceSpeedSq_nonneg g γ s)).symm

omit [IsManifold (𝓡 n) ∞ M] in
theorem curveVelocity_comp_sq {γ : ℝ → M} {s : ℝ}
    (hγ : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) γ (s ^ 2)) :
    curveVelocity (n := n) (fun r ↦ γ (r ^ 2)) s =
      (2 * s) • curveVelocity (n := n) γ (s ^ 2) := by
  have hsq : HasDerivAt (fun r : ℝ ↦ r ^ 2) (2 * s) s := by
    simpa using hasDerivAt_pow 2 s
  have hsqmf_apply : mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ))
      (fun r : ℝ ↦ r ^ 2) s 1 = 2 * s := by
    have hm := hsq.hasFDerivAt.hasMFDerivAt.mfderiv
    have hv := congrArg (fun L : TangentSpace (𝓘(ℝ, ℝ)) s →L[ℝ]
        TangentSpace (𝓘(ℝ, ℝ)) (s ^ 2) ↦ L 1) hm
    change (mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) (fun r : ℝ ↦ r ^ 2) s) (1 : ℝ) =
      (ContinuousLinearMap.toSpanSingleton ℝ (2 * s)) (1 : ℝ) at hv
    simpa only [ContinuousLinearMap.toSpanSingleton_apply, one_smul] using hv
  change (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) (γ ∘ fun r : ℝ ↦ r ^ 2) s) 1 = _
  have hchain := mfderiv_comp_apply s (f := fun r : ℝ ↦ r ^ 2) (g := γ)
    hγ hsq.differentiableAt.mdifferentiableAt (1 : TangentSpace (𝓘(ℝ, ℝ)) s)
  have hinput : mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ))
      (fun r : ℝ ↦ r ^ 2) s 1 =
      (2 * s) • (1 : TangentSpace (𝓘(ℝ, ℝ)) s) := by
    rw [hsqmf_apply]
    simp
  rw [hinput, map_smul] at hchain
  simpa only [curveVelocity, Function.comp_apply] using hchain

private theorem squarePath_speed {J : Set ℝ} {F : RicciFlow n M J}
    {T τ : ℝ} (p : BackwardTimePath F T 0 τ)
    (g : RiemannianMetric n M) {s : ℝ} (hs : s ∈ Ioo 0 (Real.sqrt τ)) :
    referenceSpeedSq g (fun r ↦ p.curve (r ^ 2)) s =
      2 * ((Real.sqrt (s ^ 2) * referenceSpeedSq g p.curve (s ^ 2)) * (2 * s)) := by
  have hτ : s ^ 2 ∈ Ioo 0 τ :=
    ⟨sq_pos_of_pos hs.1, (Real.lt_sqrt hs.1.le).mp hs.2⟩
  have hγ := (p.regular _ hτ).contMDiffAt (isOpen_Ioo.mem_nhds hτ)
  have hv := curveVelocity_comp_sq (hγ.mdifferentiableAt one_ne_zero)
  unfold referenceSpeedSq
  rw [hv, Real.sqrt_sq hs.1.le]
  simp only [map_smul, smul_apply, smul_eq_mul]
  ring

theorem squarePath_referenceEnergy {J : Set ℝ} {F : RicciFlow n M J}
    {T τ : ℝ} (p : BackwardTimePath F T 0 τ) (g : RiemannianMetric n M)
    (hW : IntervalIntegrable (fun s ↦ Real.sqrt s * referenceSpeedSq g p.curve s)
      volume 0 τ) :
    IntervalIntegrable (referenceSpeedSq g (fun r ↦ p.curve (r ^ 2)))
      volume 0 (Real.sqrt τ) ∧
    (∫ s in 0..Real.sqrt τ, referenceSpeedSq g (fun r ↦ p.curve (r ^ 2)) s) =
      2 * ∫ s in 0..τ, Real.sqrt s * referenceSpeedSq g p.curve s := by
  let W := fun s ↦ Real.sqrt s * referenceSpeedSq g p.curve s
  have hderiv (s : ℝ) : HasDerivAt (fun r : ℝ ↦ r ^ 2) (2 * s) s := by
    simpa using hasDerivAt_pow 2 s
  have hnonneg : ∀ s ∈ uIoo 0 (Real.sqrt τ), 0 ≤ 2 * s := by
    intro s hs
    rw [uIoo_of_le (Real.sqrt_nonneg τ)] at hs
    exact mul_nonneg (by norm_num) hs.1.le
  have htrans : IntervalIntegrable (fun s ↦ W (s ^ 2) * (2 * s))
      volume 0 (Real.sqrt τ) := by
    apply (intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonneg
      (f := fun s : ℝ ↦ s ^ 2) (f' := fun s ↦ 2 * s) (g := W)
      (continuous_id.pow 2).continuousOn (fun s _ ↦ hderiv s) hnonneg).mpr
    simpa only [zero_pow two_ne_zero, Real.sq_sqrt p.ordered.le] using hW
  have hidentity : (∫ s in 0..Real.sqrt τ, W (s ^ 2) * (2 * s)) =
      ∫ s in 0..τ, W s := by
    have h := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
      (f := fun s : ℝ ↦ s ^ 2) (f' := fun s ↦ 2 * s) (g := W)
      (continuous_id.pow 2).continuousOn (fun s _ ↦ hderiv s) hnonneg
    simpa only [Function.comp_apply, zero_pow two_ne_zero, Real.sq_sqrt p.ordered.le] using h
  constructor
  · apply (htrans.const_mul 2).congr_uIoo
    intro s hs
    rw [uIoo_of_le (Real.sqrt_nonneg τ)] at hs
    exact (squarePath_speed p g hs).symm
  · calc
      _ = ∫ s in 0..Real.sqrt τ, 2 * (W (s ^ 2) * (2 * s)) :=
        intervalIntegral.integral_congr_Ioo_of_le (Real.sqrt_nonneg τ)
          (fun s hs ↦ squarePath_speed p g hs)
      _ = 2 * ∫ s in 0..Real.sqrt τ, W (s ^ 2) * (2 * s) :=
        intervalIntegral.integral_const_mul _ _
      _ = _ := by rw [hidentity]

private theorem sqrt_integral_bound {q : ℝ → ℝ} {s t : ℝ}
    (hst : s ≤ t) (hq : ContinuousOn q (Icc s t)) (hnonneg : ∀ r, 0 ≤ q r) :
    (∫ r in Icc s t, Real.sqrt (q r)) ≤
      Real.sqrt (∫ r in s..t, q r) * Real.sqrt (t - s) := by
  have hsq : MemLp (fun r ↦ Real.sqrt (q r)) 2 (volume.restrict (Icc s t)) := by
    apply (memLp_two_iff_integrable_sq
      ((Real.continuous_sqrt.comp_continuousOn hq).aestronglyMeasurable
        measurableSet_Icc)).mpr
    simpa only [Function.comp_apply, Real.sq_sqrt (hnonneg _)] using
      (show Integrable (fun r ↦ q r) (volume.restrict (Icc s t)) from hq.integrableOn_Icc)
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (ae_of_all _ (fun r ↦ Real.sqrt_nonneg (q r)))
    (ae_of_all _ (fun _ ↦ (zero_le_one : (0 : ℝ) ≤ 1)))
    (by simpa using hsq) (memLp_const (1 : ℝ))
  simpa only [mul_one, Real.rpow_two, Real.sq_sqrt (hnonneg _), one_pow,
    ← Real.sqrt_eq_rpow, setIntegral_const, smul_eq_mul, mul_one,
    Real.volume_real_Icc_of_le hst, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hst] using h

variable [ConnectedSpace M] [T3Space M]

theorem toReal_edist_le_sqrt_energy (g : RiemannianMetric n M) {α : ℝ → M}
    {a b C : ℝ} (hab : a < b) (hα : ContinuousOn α (Icc a b))
    (hreg : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) 1 α (Ioo a b))
    (hE : IntervalIntegrable (referenceSpeedSq g α) volume a b)
    (hbound : (∫ r in a..b, referenceSpeedSq g α r) ≤ C) :
    ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      (g.edist (α s) (α t)).toReal ≤ Real.sqrt C * Real.sqrt |t - s| := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  let : MetricSpace M := EMetricSpace.toMetricSpace (g.edist_ne_top)
  change ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
    dist (α s) (α t) ≤ Real.sqrt C * Real.sqrt |t - s|
  have hordered (s t : ℝ) (hs : s ∈ Ioo a b) (ht : t ∈ Ioo a b) (hst : s ≤ t) :
      dist (α s) (α t) ≤ Real.sqrt C * Real.sqrt (t - s) := by
    have hsub : Icc s t ⊆ Ioo a b := Icc_subset_Ioo hs.1 ht.2
    have hq := (referenceSpeedSq_continuousOn g isOpen_Ioo hreg).mono hsub
    have hsqrt : ContinuousOn (fun r ↦ Real.sqrt (referenceSpeedSq g α r)) (Icc s t) :=
      Real.continuous_sqrt.comp_continuousOn hq
    have hlength : Manifold.pathELength (𝓡 n) α s t =
        ENNReal.ofReal (∫ r in Icc s t, Real.sqrt (referenceSpeedSq g α r)) := by
      rw [Manifold.pathELength_eq_lintegral_mfderiv_Icc,
        ofReal_integral_eq_lintegral_ofReal hsqrt.integrableOn_Icc
          (ae_of_all _ (fun r ↦ Real.sqrt_nonneg _))]
      apply lintegral_congr
      intro r
      rw [← ofReal_norm, norm_eq_sqrt_real_inner]
      rfl
    have hdist : dist (α s) (α t) ≤
        ∫ r in Icc s t, Real.sqrt (referenceSpeedSq g α r) := by
      apply (edist_le_ofReal (integral_nonneg (fun r ↦ Real.sqrt_nonneg _))).mp
      change Manifold.riemannianEDist (𝓡 n) (α s) (α t) ≤ _
      rw [← hlength]
      exact Manifold.riemannianEDist_le_pathELength (hreg.mono hsub) rfl rfl hst
    have hpart : (∫ r in s..t, referenceSpeedSq g α r) ≤ C :=
      (intervalIntegral.integral_mono_interval hs.1.le hst ht.2.le
        (ae_of_all _ (referenceSpeedSq_nonneg g α)) hE).trans hbound
    exact hdist.trans ((sqrt_integral_bound hst hq (referenceSpeedSq_nonneg g α)).trans
      (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hpart) (Real.sqrt_nonneg _)))
  have hopen (s : ℝ) (hs : s ∈ Ioo a b) (t : ℝ) (ht : t ∈ Ioo a b) :
      dist (α s) (α t) ≤ Real.sqrt C * Real.sqrt |t - s| := by
    rcases le_total s t with hst | hts
    · simpa only [abs_of_nonneg (sub_nonneg.mpr hst)] using hordered s t hs ht hst
    · simpa only [dist_comm, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hts)] using
        hordered t s ht hs hts
  have hleft (s : ℝ) (hs : s ∈ Icc a b) (t : ℝ) (ht : t ∈ Ioo a b) :
      dist (α s) (α t) ≤ Real.sqrt C * Real.sqrt |t - s| := by
    apply le_on_closure (fun r hr ↦ hopen r hr t ht)
    · simpa only [closure_Ioo hab.ne, Function.comp_def] using
        continuous_dist.comp_continuousOn (hα.prodMk continuousOn_const)
    · exact (continuous_const.mul
        (Real.continuous_sqrt.comp (continuous_const.sub continuous_id).abs)).continuousOn
    · simpa only [closure_Ioo hab.ne] using hs
  intro s hs t ht
  apply le_on_closure (fun r hr ↦ hleft s hs r hr)
  · simpa only [closure_Ioo hab.ne, Function.comp_def] using
      continuous_dist.comp_continuousOn (continuousOn_const.prodMk hα)
  · exact (continuous_const.mul
      (Real.continuous_sqrt.comp (continuous_id.sub continuous_const).abs)).continuousOn
  · simpa only [closure_Ioo hab.ne] using ht

end PoincareConjecture.ReducedLengthMinimum

namespace PoincareConjecture.AncientKappaSolution

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]

theorem surface_referenceWeightedEnergy_bound (K : AncientKappaSolution 2 M)
    {τ : ℝ} (p : BackwardTimePath K.flow 0 0 τ) :
    IntervalIntegrable (fun s ↦ Real.sqrt s *
      ReducedLengthMinimum.referenceSpeedSq (K.flow.metric 0) p.curve s) volume 0 τ ∧
    (∫ s in 0..τ, Real.sqrt s *
      ReducedLengthMinimum.referenceSpeedSq (K.flow.metric 0) p.curve s) ≤
        backwardLLength K.flow 0 0 τ p.curve := by
  let W := fun s ↦ Real.sqrt s *
    ReducedLengthMinimum.referenceSpeedSq (K.flow.metric 0) p.curve s
  have hWnonneg (s : ℝ) : 0 ≤ W s :=
    mul_nonneg (Real.sqrt_nonneg _) (ReducedLengthMinimum.referenceSpeedSq_nonneg _ _ _)
  have hWbound (s : ℝ) (hs : s ∈ Icc 0 τ) :
      W s ≤ backwardLIntegrand K.flow 0 p.curve s := by
    have hR := (K.flow.connection (0 - s)).scalar_nonnegative_of_nonnegative_curvatureOperator
      (p.curve s) (K.nonnegative_curvature_operator (0 - s) (by linarith [hs.1]) (p.curve s))
    have hg := K.surface_metric_monotone (s := 0 - s) (t := 0) (by linarith [hs.1]) le_rfl
      (p.curve s) (curveVelocity p.curve s)
    exact mul_le_mul_of_nonneg_left (hg.trans (le_add_of_nonneg_left hR))
      (Real.sqrt_nonneg s)
  have hmeas : AEStronglyMeasurable W (volume.restrict (uIoc 0 τ)) := by
    rw [uIoc_of_le p.ordered.le, ← restrict_Ioo_eq_restrict_Ioc]
    exact (Real.continuous_sqrt.continuousOn.mul
      (ReducedLengthMinimum.referenceSpeedSq_continuousOn (K.flow.metric 0)
        isOpen_Ioo p.regular)).aestronglyMeasurable measurableSet_Ioo
  have hW : IntervalIntegrable W volume 0 τ := by
    apply p.l_integrable.mono_fun' hmeas
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
    rw [Real.norm_eq_abs, abs_of_nonneg (hWnonneg s)]
    apply hWbound
    simpa only [uIcc_of_le p.ordered.le] using uIoc_subset_uIcc hs
  exact ⟨hW, intervalIntegral.integral_mono_on p.ordered.le hW p.l_integrable hWbound⟩

theorem surface_squarePath_modulus (K : AncientKappaSolution 2 M)
    {τ C : ℝ} (p : BackwardTimePath K.flow 0 0 τ)
    (hC : backwardLLength K.flow 0 0 τ p.curve ≤ C) :
    ∀ s ∈ Icc 0 (Real.sqrt τ), ∀ t ∈ Icc 0 (Real.sqrt τ),
      ((K.flow.metric 0).edist (p.curve (s ^ 2)) (p.curve (t ^ 2))).toReal ≤
        Real.sqrt (2 * C) * Real.sqrt |t - s| := by
  let g := K.flow.metric 0
  let α := fun s ↦ p.curve (s ^ 2)
  have hweighted := K.surface_referenceWeightedEnergy_bound p
  have henergy := ReducedLengthMinimum.squarePath_referenceEnergy p g hweighted.1
  have hcont : ContinuousOn α (Icc 0 (Real.sqrt τ)) := by
    apply p.continuous.comp (continuous_id.pow 2).continuousOn
    intro s hs
    exact ⟨sq_nonneg s, (Real.le_sqrt hs.1 p.ordered.le).mp hs.2⟩
  have hreg : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 2) 1 α (Ioo 0 (Real.sqrt τ)) := by
    apply p.regular.comp ((contDiff_id.pow 2).contMDiff.contMDiffOn)
    intro s hs
    exact ⟨sq_pos_of_pos hs.1, (Real.lt_sqrt hs.1.le).mp hs.2⟩
  apply ReducedLengthMinimum.toReal_edist_le_sqrt_energy g
    (Real.sqrt_pos.mpr p.ordered) hcont hreg henergy.1
  rw [henergy.2]
  exact mul_le_mul_of_nonneg_left (hweighted.2.trans hC) (by norm_num)

theorem exists_uniform_subsequence_of_surface_action_bound (K : AncientKappaSolution 2 M)
    (p : M) {τ C : ℝ}
    (paths : ℕ → BackwardTimePath K.flow 0 0 τ)
    (hstart : ∀ k, (paths k).curve 0 = p)
    (haction : ∀ k, backwardLLength K.flow 0 0 τ (paths k).curve ≤ C) :
    ∃ α : C(Icc 0 (Real.sqrt τ), M), ∃ φ : ℕ → ℕ, StrictMono φ ∧
      α ⟨0, le_rfl, Real.sqrt_nonneg τ⟩ = p ∧
      ∀ ε > 0, ∃ N : ℕ, ∀ k ≥ N, ∀ s : Icc 0 (Real.sqrt τ),
        ((K.flow.metric 0).edist ((paths (φ k)).curve (s.val ^ 2)) (α s)).toReal < ε := by
  classical
  let g := K.flow.metric 0
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 2) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 2))
      (TangentSpace (𝓡 2) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 2) M
  let : MetricSpace M := EMetricSpace.toMetricSpace (g.edist_ne_top)
  let f : ℕ → Icc 0 (Real.sqrt τ) → M := fun k s ↦ (paths k).curve (s.val ^ 2)
  have hmod (k : ℕ) (s t : Icc 0 (Real.sqrt τ)) :
      dist (f k s) (f k t) ≤ Real.sqrt (2 * C) * Real.sqrt |t.val - s.val| :=
    K.surface_squarePath_modulus (paths k) (haction k) s s.property t t.property
  have hequi : Equicontinuous f := by
    intro s
    apply Metric.equicontinuousAt_iff_right.mpr
    intro ε hε
    have hcont : Continuous (fun t : Icc 0 (Real.sqrt τ) ↦
        Real.sqrt (2 * C) * Real.sqrt |t.val - s.val|) := by fun_prop
    have hnear := hcont.continuousAt.preimage_mem_nhds
      (Iio_mem_nhds (show Real.sqrt (2 * C) * Real.sqrt |s.val - s.val| < ε by
        simpa only [sub_self, abs_zero, Real.sqrt_zero, mul_zero] using hε))
    exact Filter.mem_of_superset hnear (fun t ht k ↦ (hmod k s t).trans_lt ht)
  let B := {q : M | g.edist p q ≤
    ENNReal.ofReal (Real.sqrt (2 * C) * Real.sqrt (Real.sqrt τ))}
  have hB : IsCompact B := g.isCompact_closedBall_of_metricComplete (K.complete 0 le_rfl) p _
  have hfB (k : ℕ) (s : Icc 0 (Real.sqrt τ)) : f k s ∈ B := by
    have h := hmod k ⟨0, le_rfl, Real.sqrt_nonneg τ⟩ s
    simp only [f, zero_pow two_ne_zero, hstart, sub_zero,
      abs_of_nonneg s.property.1] at h
    have hd : dist p (f k s) ≤ Real.sqrt (2 * C) * Real.sqrt (Real.sqrt τ) :=
      h.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt s.property.2)
        (Real.sqrt_nonneg _))
    exact (ENNReal.ofReal_toReal (g.edist_ne_top p (f k s))).symm.le.trans
      (ENNReal.ofReal_le_ofReal hd)
  let F : ℕ → Icc 0 (Real.sqrt τ) →ᵇ M := fun k ↦
    BoundedContinuousFunction.mkOfCompact ⟨f k, hequi.continuous k⟩
  have hFequi : Equicontinuous (fun q : range F ↦ (q.1 : Icc 0 (Real.sqrt τ) → M)) := by
    have h := hequi.comp (fun q : range F ↦ Classical.choose q.2)
    convert h using 1
    funext q t
    have hq := congrArg (fun a : Icc 0 (Real.sqrt τ) →ᵇ M ↦ a t)
      (Classical.choose_spec q.2)
    exact hq.symm
  have hcompact := BoundedContinuousFunction.arzela_ascoli B hB (range F)
    (by rintro _ s ⟨k, rfl⟩; exact hfB k s) hFequi
  obtain ⟨α, _, φ, hφ, hlim⟩ := hcompact.tendsto_subseq
    (fun k ↦ subset_closure (mem_range_self k))
  have hunif := BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hlim
  refine ⟨α.toContinuousMap, φ, hφ, ?_, ?_⟩
  · have hzero := hunif.tendsto_at ⟨0, le_rfl, Real.sqrt_nonneg τ⟩
    have hz : Tendsto (fun _ : ℕ ↦ p) atTop (𝓝 (α ⟨0, le_rfl, Real.sqrt_nonneg τ⟩)) := by
      simpa only [F, f, BoundedContinuousFunction.mkOfCompact_apply,
        Function.comp_apply, ContinuousMap.coe_mk, zero_pow two_ne_zero, hstart] using hzero
    exact (tendsto_nhds_unique tendsto_const_nhds hz).symm
  · intro ε hε
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hlim ε hε
    refine ⟨N, fun k hk s ↦ ?_⟩
    exact (BoundedContinuousFunction.dist_coe_le_dist s).trans_lt (hN k hk)

theorem exists_uniformly_convergent_spatial_minimizing_paths (K : AncientKappaSolution 2 M)
    (p : M) {τ : ℝ} (hτ : 0 < τ) :
    ∃ paths : ℕ → BackwardTimePath K.flow 0 0 τ,
      ∃ α : C(Icc 0 (Real.sqrt τ), M),
      (∀ k, (paths k).curve 0 = p) ∧
      Antitone (fun k ↦ backwardLLength K.flow 0 0 τ (paths k).curve) ∧
      Tendsto (fun k ↦ backwardLLength K.flow 0 0 τ (paths k).curve) atTop
        (𝓝 (2 * Real.sqrt τ * K.spatialReducedLengthInfimum p τ)) ∧
      α ⟨0, le_rfl, Real.sqrt_nonneg τ⟩ = p ∧
      ∀ ε > 0, ∃ N : ℕ, ∀ k ≥ N, ∀ s : Icc 0 (Real.sqrt τ),
        ((K.flow.metric 0).edist ((paths k).curve (s.val ^ 2)) (α s)).toReal < ε := by
  classical
  let S : Set ℝ := {L | ∃ path : BackwardTimePath K.flow 0 0 τ,
    path.curve 0 = p ∧ L = backwardLLength K.flow 0 0 τ path.curve}
  have hS : S.Nonempty := by
    obtain ⟨path, hp, _⟩ := K.exists_backwardTimePath_surface p p hτ
    exact ⟨_, path, hp, rfl⟩
  have hSbdd : BddBelow S := by
    refine ⟨0, ?_⟩
    rintro L ⟨path, _, rfl⟩
    exact K.backwardLLength_nonneg path.curve hτ.le
  have hden : 0 < 2 * Real.sqrt τ := by positivity
  have hinf : sInf S / (2 * Real.sqrt τ) = K.spatialReducedLengthInfimum p τ := by
    apply le_antisymm
    · apply le_csInf (range_nonempty (f := fun q ↦ reducedLength K.flow 0 p q τ))
      rintro L ⟨q, rfl⟩
      unfold PoincareConjecture.reducedLength
      simp only [dif_pos hτ]
      apply div_le_div_of_nonneg_right _ hden.le
      have hpaths : {L : ℝ | ∃ path : BackwardTimePath K.flow 0 0 τ,
          path.curve 0 = p ∧ path.curve τ = q ∧
          L = backwardLLength K.flow 0 0 τ path.curve}.Nonempty := by
        obtain ⟨path, hp, hq⟩ := K.exists_backwardTimePath_surface p q hτ
        exact ⟨_, path, hp, hq, rfl⟩
      apply le_csInf hpaths
      rintro L ⟨path, hp, _, rfl⟩
      exact csInf_le hSbdd ⟨path, hp, rfl⟩
    · apply (le_div_iff₀ hden).mpr
      apply le_csInf hS
      rintro L ⟨path, hp, rfl⟩
      exact (le_div_iff₀ hden).mp ((K.spatialReducedLengthInfimum_le p
        (path.curve τ) τ).trans (K.reducedLength_le_path path hp rfl))
  have hinf' : sInf S = 2 * Real.sqrt τ * K.spatialReducedLengthInfimum p τ := by
    exact (div_eq_iff hden.ne').mp hinf |>.trans (mul_comm _ _)
  obtain ⟨u, hanti, hlim, hu⟩ := exists_seq_tendsto_sInf hS hSbdd
  choose paths hstart hvalue using hu
  have hbound (k : ℕ) : backwardLLength K.flow 0 0 τ (paths k).curve ≤ u 0 := by
    rw [← hvalue k]
    exact hanti (Nat.zero_le k)
  obtain ⟨α, φ, hφ, hα0, huniform⟩ :=
    K.exists_uniform_subsequence_of_surface_action_bound p paths hstart hbound
  refine ⟨paths ∘ φ, α, (fun k ↦ hstart (φ k)), ?_, ?_, hα0, huniform⟩
  · intro i j hij
    simpa only [Function.comp_apply, ← hvalue] using hanti (hφ.monotone hij)
  · simpa only [Function.comp_def, ← hvalue, hinf'] using hlim.comp hφ.tendsto_atTop

end PoincareConjecture.AncientKappaSolution
