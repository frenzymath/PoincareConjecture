import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variational.TimeSupport
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variational.MinimizingPath
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variational.Extension.Manifold
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Geometry.TraceIntegral

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped Manifold ContDiff Bundle intervalIntegral

namespace PoincareConjecture.ReducedLengthMinimum.Variational

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem exists_finite_chart_primitive_of_smooth {a b : ℝ} (hab : a ≤ b)
    (α γ : ℝ → M) (hγ : Continuous γ) {U : Set ℝ} (hU : IsOpen U)
    (hI : Icc a b ⊆ U) (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ α U)
    (heq : EqOn γ α (Icc a b)) :
    ∃ (m : ℕ) (t : Fin (m + 1) → ℝ) (x : Fin m → M)
      (w : ∀ i : Fin m, IntervalL2 (EuclideanSpace ℝ (Fin n))
        (t i.castSucc) (t i.succ)),
      Monotone t ∧ t 0 = a ∧ t (Fin.last m) = b ∧
      (∀ i, MapsTo γ (Icc (t i.castSucc) (t i.succ))
        (chartAt (EuclideanSpace ℝ (Fin n)) (x i)).source) ∧
      ∀ i s, s ∈ Icc (t i.castSucc) (t i.succ) →
        extChartAt (𝓡 n) (x i) (γ s) = extChartAt (𝓡 n) (x i) (γ (t i.castSucc)) +
          ∫ r in t i.castSucc..s, w i r := by
  classical
  let V : M → Set (Icc a b) := fun x =>
    (fun s : Icc a b => γ s) ⁻¹' (chartAt (EuclideanSpace ℝ (Fin n)) x).source
  have hV (x : M) : IsOpen (V x) :=
    (chartAt (EuclideanSpace ℝ (Fin n)) x).open_source.preimage
      (hγ.comp continuous_subtype_val)
  have hcover : univ ⊆ ⋃ x, V x := by
    intro s _
    exact mem_iUnion.mpr ⟨γ s, mem_chart_source _ _⟩
  obtain ⟨u, hua, humono, ⟨m, hum⟩, hpieces⟩ :=
    exists_monotone_Icc_subset_open_cover_Icc hab hV hcover
  let t : Fin (m + 1) → ℝ := fun i => u i
  have htm : Monotone t := fun i j hij => humono hij
  have hta : t 0 = a := hua
  have htb : t (Fin.last m) = b := hum m le_rfl
  choose x hx using fun i : Fin m => hpieces i.1
  have hsub (i : Fin m) : Icc (t i.castSucc) (t i.succ) ⊆ Icc a b := by
    intro s hs
    exact ⟨(u i.1).2.1.trans hs.1, hs.2.trans (u (i.1 + 1)).2.2⟩
  have hsrc (i : Fin m) : MapsTo γ (Icc (t i.castSucc) (t i.succ))
      (chartAt (EuclideanSpace ℝ (Fin n)) (x i)).source := by
    intro s hs
    exact hx i (show (⟨s, hsub i hs⟩ : Icc a b) ∈ Icc (u i.1) (u (i.1 + 1)) from hs)
  have hsrcα (i : Fin m) : MapsTo α (Icc (t i.castSucc) (t i.succ))
      (chartAt (EuclideanSpace ℝ (Fin n)) (x i)).source := by
    intro s hs
    rw [← heq (hsub i hs)]
    exact hsrc i hs
  have hcoord (i : Fin m) (s : ℝ) (hs : s ∈ Icc (t i.castSucc) (t i.succ)) :
      ContDiffAt ℝ ∞ ((extChartAt (𝓡 n) (x i)) ∘ α) s := by
    have hc := (contMDiffAt_extChartAt' (I := 𝓡 n) (n := ∞)
      (hsrcα i hs)).comp s
      ((hα s (hI (hsub i hs))).contMDiffAt (hU.mem_nhds (hI (hsub i hs))))
    exact hc.contDiffAt
  have hLp (i : Fin m) : MemLp (deriv ((extChartAt (𝓡 n) (x i)) ∘ α)) 2
      (volume.restrict (Icc (t i.castSucc) (t i.succ))) := by
    apply (continuousOn_memLp_top_Icc (fun s hs =>
      ((hcoord i s hs).derivWithin (m := 0) (by simp)).continuousAt.continuousWithinAt)).mono_exponent
    exact le_top
  let w (i : Fin m) : IntervalL2 (EuclideanSpace ℝ (Fin n)) (t i.castSucc) (t i.succ) :=
    (hLp i).toLp (deriv ((extChartAt (𝓡 n) (x i)) ∘ α))
  refine ⟨m, t, x, w, htm, hta, htb, hsrc, ?_⟩
  intro i s hs
  have ha : t i.castSucc ∈ Icc (t i.castSucc) (t i.succ) :=
    ⟨le_rfl, htm (Fin.castSucc_le_succ i)⟩
  rw [heq (hsub i hs), heq (hsub i ha)]
  exact primitive_of_deriv
    (fun r hr => (hcoord i r hr).continuousAt.continuousWithinAt)
    (fun r hr => ((hcoord i r (Ioo_subset_Icc_self hr)).differentiableAt (by simp)).hasDerivAt)
    (hLp i) hs

end PoincareConjecture.ReducedLengthMinimum.Variational

namespace PoincareConjecture.AncientKappaSolution

open ReducedLengthMinimum ReducedLengthMinimum.Variational
open ReducedLengthMinimum.Variation.Geometry

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]

theorem stationary_time_comparison_of_sqrtRegularPath (K : AncientKappaSolution 2 M)
    (p : M) {τ : ℝ} (hτ : 0 < τ) (q : BackwardTimePath K.flow 0 0 τ)
    (S : SqrtRegularPath q) (hq0 : q.curve 0 = p)
    (haction : backwardLLength K.flow 0 0 τ q.curve =
      2 * Real.sqrt τ * K.spatialReducedLengthInfimum p τ) :
    ∀ u : ℝ, τ ≤ u → K.spatialReducedLengthInfimum p u ≤
      stationaryTimeSupport
        (fun r => (K.flow.connection (0 - r)).scalarCurvature (S.curve (Real.sqrt τ)))
        τ (K.spatialReducedLengthInfimum p τ) u := by
  let : MetricSpace M := referenceMetricSpace (K.flow.metric 0)
  have hc : 0 ≤ Real.sqrt τ := Real.sqrt_nonneg τ
  have hI : Icc 0 (Real.sqrt τ) ⊆ S.domain := by
    simpa only [sqrtParameterInterval, Real.sqrt_zero] using S.interval_subset
  let γ : ℝ → M := fun s => S.curve (projIcc 0 (Real.sqrt τ) hc s)
  have hγ : Continuous γ :=
    (continuousOn_iff_continuous_domRestrict.mp (S.smooth.continuousOn.mono hI)).comp
      continuous_projIcc
  have heq : EqOn γ S.curve (Icc 0 (Real.sqrt τ)) := by
    intro s hs
    dsimp only [γ]
    rw [projIcc_of_mem _ hs]
  have hγ0 : γ 0 = p := by
    rw [heq ⟨le_rfl, hc⟩]
    have h := S.agrees 0 (by simpa only [sqrtParameterInterval, Real.sqrt_zero]
      using (show (0 : ℝ) ∈ Icc 0 (Real.sqrt τ) from ⟨le_rfl, hc⟩))
    simpa only [zero_pow (by norm_num : 2 ≠ 0), hq0] using h
  have hγend : γ (Real.sqrt τ) = S.curve (Real.sqrt τ) := heq ⟨hc, le_rfl⟩
  obtain ⟨m, t, x, w, ht, ht0, htend, hsrc, hprimitive⟩ :=
    exists_finite_chart_primitive_of_smooth hc S.curve γ hγ S.open_domain hI S.smooth heq
  have hreg : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 2) 1 γ (Ioo 0 (Real.sqrt τ)) :=
    ((S.smooth.of_le (by simp)).mono (Ioo_subset_Icc_self.trans hI)).congr
      (fun s hs => heq (Ioo_subset_Icc_self hs))
  have htime : ∀ s ∈ Icc (t 0) (t (Fin.last m)), 0 - s ^ 2 ∈ Iic (0 : ℝ) := by
    intro s _
    exact sub_nonpos.mpr (sq_nonneg s)
  have hpotential : ContinuousOn
      (fun z : ℝ × M => 2 * z.1 ^ 2 * (K.flow.connection (0 - z.1 ^ 2)).scalarCurvature z.2)
      (Icc (t 0) (t (Fin.last m)) ×ˢ univ) := by
    rw [ht0, htend]
    exact K.regularizedPotential_continuousOn le_rfl hc univ
  have hsum := (finite_chart_action_of_interior_regular K.flow 0 t ht htime hpotential
    γ hγ.continuousOn (by simpa only [ht0, htend] using hreg) x hsrc w hprimitive).2
  have hactionγ : regularizedLAction K.flow 0 τ γ = regularizedLAction K.flow 0 τ S.curve := by
    apply intervalIntegral.integral_congr_Ioo_of_le hc
    intro s hs
    have hnear : γ =ᶠ[𝓝 s] S.curve := by
      filter_upwards [isOpen_Ioo.mem_nhds hs] with r hr
      exact heq (Ioo_subset_Icc_self hr)
    have hd := hnear.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := 𝓡 2)
    simp only [regularizedLIntegrand, curveVelocity, hd, hnear.eq_of_nhds]
    congr 2
    exact congrArg (fun y : M => (K.flow.metric (0 - s ^ 2)).inner y
      ((mfderiv (𝓘(ℝ, ℝ)) (𝓡 2) S.curve s) 1)
      ((mfderiv (𝓘(ℝ, ℝ)) (𝓡 2) S.curve s) 1)) hnear.eq_of_nhds
  have hsum' : (∑ i, chartH1Action K.flow 0 (x i) (t i.castSucc) (t i.succ) γ (w i)) =
      2 * Real.sqrt τ * K.spatialReducedLengthInfimum p τ := by
    rw [hsum, ht0, htend]
    change regularizedLAction K.flow 0 τ γ = _
    rw [hactionγ, sqrtRegularPath_action S, haction]
  intro u hu
  have hupos : 0 < 2 * Real.sqrt u := by
    have := hτ.trans_le hu
    positivity
  apply (le_div_iff₀ hupos).mpr
  have hext := K.reducedLength_le_stationary_extension hτ hu t ht ht0 htend
    γ hγ x hsrc w hprimitive
  change 2 * Real.sqrt u * reducedLength K.flow 0 (γ 0) (γ (Real.sqrt τ)) u ≤
    (∑ i, chartH1Action K.flow 0 (x i) (t i.castSucc) (t i.succ) γ (w i)) + _ at hext
  rw [hsum', hγ0, hγend] at hext
  have hinf := mul_le_mul_of_nonneg_left
    (K.spatialReducedLengthInfimum_le p (S.curve (Real.sqrt τ)) u) hupos.le
  simpa only [stationaryTimeSupport, mul_comm] using hinf.trans hext

theorem right_time_upper_support_of_sqrtRegularPath (K : AncientKappaSolution 2 M)
    (p : M) {τ : ℝ} (hτ : 0 < τ) (q : BackwardTimePath K.flow 0 0 τ)
    (S : SqrtRegularPath q) (hq0 : q.curve 0 = p)
    (haction : backwardLLength K.flow 0 0 τ q.curve =
      2 * Real.sqrt τ * K.spatialReducedLengthInfimum p τ) :
    ∃ b : ℝ → ℝ, b τ = K.spatialReducedLengthInfimum p τ ∧
      HasDerivAt b ((K.flow.connection (-τ)).scalarCurvature (S.curve (Real.sqrt τ)) / 2 -
        K.spatialReducedLengthInfimum p τ / (2 * τ)) τ ∧
      ∀ u : ℝ, τ ≤ u → K.spatialReducedLengthInfimum p u ≤ b u := by
  have hR : ContinuousOn
      (fun r => (K.flow.connection (0 - r)).scalarCurvature (S.curve (Real.sqrt τ)))
      (Ioi (0 : ℝ)) :=
    (K.flow.continuousOn_scalarCurvature_ancient_surface (S.curve (Real.sqrt τ))).comp
      (continuous_const.sub continuous_id).continuousOn
      (fun r hr => show 0 - r ∈ Iic 0 from by
        change 0 < r at hr
        exact sub_nonpos.mpr hr.le)
  refine ⟨stationaryTimeSupport _ τ (K.spatialReducedLengthInfimum p τ),
    stationaryTimeSupport_self _ hτ _, ?_,
    K.stationary_time_comparison_of_sqrtRegularPath p hτ q S hq0 haction⟩
  apply (hasDerivAt_stationaryTimeSupport _ hR hτ
    (K.spatialReducedLengthInfimum p τ)).congr_deriv
  exact congrArg (fun r : ℝ =>
    (K.flow.connection r).scalarCurvature (S.curve (Real.sqrt τ)) / 2 -
      K.spatialReducedLengthInfimum p τ / (2 * τ)) (zero_sub τ)

end PoincareConjecture.AncientKappaSolution
