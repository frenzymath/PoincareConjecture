import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variational.AncientAction









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set Filter Topology
open scoped Manifold ContDiff Bundle intervalIntegral

namespace PoincareConjecture.AncientKappaSolution

open ReducedLengthMinimum ReducedLengthMinimum.Variational

variable {M : Type*} [MetricSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [ConnectedSpace M]

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency true in
theorem finite_chart_limit_le_spatialInfimum (K : AncientKappaSolution 2 M)
    (p : M) {τ : ℝ} (hτ : 0 < τ)
    (paths : ℕ → BackwardTimePath K.flow 0 0 τ)
    (hanti : Antitone (fun k => backwardLLength K.flow 0 0 τ (paths k).curve))
    (hmin : Tendsto (fun k => backwardLLength K.flow 0 0 τ (paths k).curve)
      atTop (𝓝 (2 * Real.sqrt τ * K.spatialReducedLengthInfimum p τ)))
    (γ : ℝ → M) (hγ : Continuous γ)
    (hlim : TendstoUniformlyOn (fun k s => (paths k).curve (s ^ 2)) γ atTop
      (Icc 0 (Real.sqrt τ)))
    {m : ℕ} (t : Fin (m + 1) → ℝ) (ht : Monotone t)
    (hta : t 0 = 0) (htb : t (Fin.last m) = Real.sqrt τ)
    (x : Fin m → M) (Q : Fin m → Set M)
    (hQ : ∀ i, IsCompact (Q i) ∧
      γ '' Icc (t i.castSucc) (t i.succ) ⊆ interior (Q i) ∧
      Q i ⊆ (chartAt (EuclideanSpace ℝ (Fin 2)) (x i)).source) :
    ∃ w : ∀ i : Fin m, IntervalL2 (EuclideanSpace ℝ (Fin 2)) (t i.castSucc) (t i.succ),
      (∀ i s, s ∈ Icc (t i.castSucc) (t i.succ) →
        extChartAt (𝓡 2) (x i) (γ s) = extChartAt (𝓡 2) (x i) (γ (t i.castSucc)) +
          ∫ r in t i.castSucc..s, w i r) ∧
      (∑ i, ((∫ s in t i.castSucc..t i.succ,
        regularizedChartMetric K.flow 0 (x i) (s, γ s) (w i s) (w i s)) +
        ∫ s in t i.castSucc..t i.succ,
          2 * s ^ 2 * (K.flow.connection (0 - s ^ 2)).scalarCurvature (γ s))) ≤
        2 * Real.sqrt τ * K.spatialReducedLengthInfimum p τ := by
  classical
  have hseg (i : Fin m) : t i.castSucc ≤ t i.succ := ht (Fin.castSucc_le_succ i)
  have hleft (i : Fin m) : 0 ≤ t i.castSucc := by
    rw [← hta]; exact ht (Fin.zero_le _)
  have hright (i : Fin m) : t i.succ ≤ Real.sqrt τ := by
    rw [← htb]; exact ht (Fin.le_last _)
  have hsub (i : Fin m) : Icc (t i.castSucc) (t i.succ) ⊆ Icc 0 (Real.sqrt τ) :=
    Icc_subset_Icc (hleft i) (hright i)
  have heventually (i : Fin m) : ∀ᶠ k in atTop,
      MapsTo (fun s => (paths k).curve (s ^ 2)) (Icc (t i.castSucc) (t i.succ)) (Q i) := by
    obtain ⟨δ, hδ, hmargin⟩ := (isCompact_Icc.image hγ).exists_cthickening_subset_open
      isOpen_interior (hQ i).2.1
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hlim δ hδ] with k hk s hs
    apply interior_subset (hmargin ?_)
    exact Metric.mem_cthickening_of_dist_le _ (γ s) _ _ (mem_image_of_mem γ hs)
      (by simpa only [dist_comm] using (hk s (hsub i hs)).le)
  obtain ⟨N, htail⟩ := eventually_atTop.mp (Filter.eventually_all.mpr heventually)
  let q : ℕ → BackwardTimePath K.flow 0 0 τ := fun k => paths (k + N)
  let α : ℕ → ℝ → M := fun k s => (q k).curve (s ^ 2)
  have hshift : StrictMono (fun k : ℕ => k + N) := fun _ _ hij => Nat.add_lt_add_right hij N
  have hlimq : TendstoUniformlyOn α γ atTop (Icc 0 (Real.sqrt τ)) := by
    intro U hU
    exact hshift.tendsto_atTop.eventually (hlim U hU)
  have hα (i : Fin m) (k : ℕ) : ContinuousOn (α k) (Icc (t i.castSucc) (t i.succ)) := by
    apply (q k).continuous.comp (continuous_id.pow 2).continuousOn
    intro s hs
    exact ⟨sq_nonneg s, (Real.le_sqrt (hsub i hs).1 hτ.le).mp (hsub i hs).2⟩
  have hreg (i : Fin m) (k : ℕ) :
      ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 2) 1 (α k) (Ioo (t i.castSucc) (t i.succ)) := by
    apply (q k).regular.comp ((contDiff_id.pow 2).contMDiff.contMDiffOn)
    intro s hs
    have hs' := Ioo_subset_Ioo (hleft i) (hright i) hs
    exact ⟨sq_pos_of_pos hs'.1, (Real.lt_sqrt hs'.1.le).mp hs'.2⟩
  have hαQ (i : Fin m) (k : ℕ) : MapsTo (α k) (Icc (t i.castSucc) (t i.succ)) (Q i) :=
    htail (k + N) (Nat.le_add_left N k) i
  have hγQ (i : Fin m) : MapsTo γ (Icc (t i.castSucc) (t i.succ)) (Q i) :=
    fun s hs => interior_subset ((hQ i).2.1 (mem_image_of_mem γ hs))
  let C := 2 * backwardLLength K.flow 0 0 τ (paths 0).curve
  have hE (k : ℕ) : IntervalIntegrable (referenceSpeedSq (K.flow.metric 0) (α k))
      volume 0 (Real.sqrt τ) ∧
      (∫ s in 0..Real.sqrt τ, referenceSpeedSq (K.flow.metric 0) (α k) s) ≤ C := by
    have href := K.surface_referenceWeightedEnergy_bound (q k)
    have hsquare := squarePath_referenceEnergy (q k) (K.flow.metric 0) href.1
    refine ⟨hsquare.1, ?_⟩
    rw [hsquare.2]
    exact mul_le_mul_of_nonneg_left (href.2.trans (hanti (Nat.zero_le (k + N)))) (by norm_num)
  have hEpiece (i : Fin m) (k : ℕ) : IntervalIntegrable
      (referenceSpeedSq (K.flow.metric 0) (α k)) volume (t i.castSucc) (t i.succ) := by
    apply (hE k).1.mono_set
    simpa only [uIcc_of_le (hseg i), uIcc_of_le (Real.sqrt_nonneg τ)] using hsub i
  have hEbound (i : Fin m) (k : ℕ) :
      (∫ s in t i.castSucc..t i.succ, referenceSpeedSq (K.flow.metric 0) (α k) s) ≤ C := by
    apply le_trans _ (hE k).2
    exact intervalIntegral.integral_mono_interval (hleft i) (hseg i) (hright i)
      (Eventually.of_forall (referenceSpeedSq_nonneg _ _)) (hE k).1
  obtain ⟨v, w, B, φ, hφ, hv, hprimitive, hweak⟩ :=
    finite_chartH1_limit (K.flow.metric 0) (fun i => t i.castSucc) (fun i => t i.succ)
      hseg x Q (fun i => (hQ i).1) (fun i => (hQ i).2.2) α γ hα hreg hαQ hγQ
      (fun i s hs => hlimq.tendsto_at (hsub i hs)) hEpiece (fun _ => C) hEbound
  have hlimφ (i : Fin m) : TendstoUniformlyOn (fun k => α (φ k)) γ atTop
      (Icc (t i.castSucc) (t i.succ)) := by
    intro U hU
    exact hφ.tendsto_atTop.eventually ((hlimq.mono (hsub i)) U hU)
  have hpotential (i : Fin m) : ContinuousOn
      (fun z : ℝ × M => 2 * z.1 ^ 2 *
        (K.flow.connection (0 - z.1 ^ 2)).scalarCurvature z.2)
      (Icc (t i.castSucc) (t i.succ) ×ˢ Q i) :=
    K.regularizedPotential_continuousOn (hleft i) (hseg i) (Q i)
  have henergy (k : ℕ) :
      (∑ i : Fin m, ((∫ s in t i.castSucc..t i.succ,
        regularizedChartMetric K.flow 0 (x i) (s, α (φ k) s) (v i (φ k) s) (v i (φ k) s)) +
        ∫ s in t i.castSucc..t i.succ,
          2 * s ^ 2 * (K.flow.connection (0 - s ^ 2)).scalarCurvature (α (φ k) s))) ≤
        backwardLLength K.flow 0 0 τ (q (φ k)).curve := by
    have haction := squarePath_action (q (φ k))
    have hpieces (i : Fin m) := chart_piece_action_eq K.flow 0 (hseg i) (x i) (α (φ k))
      (hreg i (φ k)) (fun s hs => (hQ i).2.2 (hαQ i (φ k) hs))
      ((hpotential i).comp (continuousOn_id.prodMk (hα i (φ k)))
        (fun s hs => ⟨hs, hαQ i (φ k) hs⟩))
      (haction.1.mono_set (by
        simpa only [uIcc_of_le (hseg i), uIcc_of_le (Real.sqrt_nonneg τ)] using hsub i))
      (v i (φ k)) (hv i (φ k)).2
    simp_rw [hpieces]
    have hsum := sum_integral_fin_partition t ht (regularizedLIntegrand K.flow 0 (α (φ k)))
      (by simpa only [hta, htb] using haction.1)
    rw [hsum, hta, htb]
    exact haction.2.le
  refine ⟨w, hprimitive, ?_⟩
  exact @finite_chart_action_le 2 M inferInstance inferInstance inferInstance
    (Iic 0) K.flow 0 (Fin m) inferInstance (fun i => t i.castSucc) (fun i => t i.succ)
    hseg x Q (fun i => (hQ i).1)
    (fun i => (hQ i).2.2)
    (fun _ s _ => show 0 - s ^ 2 ∈ Iic 0 from sub_nonpos.mpr (sq_nonneg s))
    hpotential (fun k => α (φ k)) γ (fun i k => hα i (φ k))
    (fun _ => hγ.continuousOn) (fun i k => hαQ i (φ k)) hγQ hlimφ
    (fun i k => v i (φ k)) w B (fun i k => (hv i (φ k)).1) hweak
    (fun k => backwardLLength K.flow 0 0 τ (q (φ k)).curve) _
    ((hmin.comp hshift.tendsto_atTop).comp hφ.tendsto_atTop) henergy

end PoincareConjecture.AncientKappaSolution
