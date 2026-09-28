import PoincareConjecture.Proofs.M08.ChartRecovery
import PoincareConjecture.Proofs.M08.MinimizingCompactness









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set Filter Topology
open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareConjecture.M08

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem chart_density_integrable {A E : Type*} [MeasurableSpace A]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure A}
    (B : A → E →L[ℝ] E →L[ℝ] ℝ) (hB : MemLp B (⊤ : ENNReal) μ)
    (v : Lp E 2 μ) : Integrable (fun s ↦ B s (v s) (v s)) μ := by
  have hBv : MemLp (fun s ↦ B s (v s)) 2 μ :=
    by simpa only [ContinuousLinearMap.id_apply] using
      (ContinuousLinearMap.memLp_of_bilin (𝕜 := ℝ) (E := E →L[ℝ] E →L[ℝ] ℝ) (F := E)
        (G := E →L[ℝ] ℝ) 2 (ContinuousLinearMap.id ℝ (E →L[ℝ] E →L[ℝ] ℝ))
        hB (Lp.memLp v))
  exact memLp_one_iff_integrable.mp
    (ContinuousLinearMap.memLp_of_bilin (𝕜 := ℝ) (E := E →L[ℝ] ℝ) (F := E) (G := ℝ)
      1 (ContinuousLinearMap.id ℝ (E →L[ℝ] ℝ)) hBv (Lp.memLp v))

theorem quadratic_form_tendsto {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (Qk : ℕ → H →L[ℝ] H →L[ℝ] ℝ) (Q : H →L[ℝ] H →L[ℝ] ℝ)
    (v : ℕ → H) (w : H) (hQ : Tendsto Qk atTop (𝓝 Q)) (hv : Tendsto v atTop (𝓝 w)) :
    Tendsto (fun k ↦ Qk k (v k) (v k)) atTop (𝓝 (Q w w)) := by
  have heval : Continuous (fun z : (H →L[ℝ] H →L[ℝ] ℝ) × H ↦ z.1 z.2 z.2) :=
    (continuous_fst.clm_apply continuous_snd).clm_apply continuous_snd
  exact (heval.tendsto (Q, w)).comp (hQ.prodMk_nhds hv)

variable {n : ℕ} {M : Type u} [MetricSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem smooth_chart_recovery_of_lt {a b : ℝ} (hab : a < b) (x : M)
    (γ : ℝ → M) (hγ : ContinuousOn γ (Icc a b))
    (hsrc : MapsTo γ (Icc a b) (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    (w : ChartL2 (EuclideanSpace ℝ (Fin n)) a b)
    (hprimitive : ∀ s ∈ Icc a b,
      extChartAt (𝓡 n) x (γ s) = extChartAt (𝓡 n) x (γ a) + ∫ r in a..s, w r) :
    ∃ (α : ℕ → ℝ → M) (d : ℕ → ℝ → EuclideanSpace ℝ (Fin n))
      (hdLp : ∀ k, MemLp (d k) 2 (volume.restrict (Icc a b))) (K : Set M),
      IsCompact K ∧ K ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) x).source ∧
      MapsTo γ (Icc a b) K ∧
      (∀ k, ContMDiff (𝓘(ℝ, ℝ)) (𝓡 n) ∞ (α k) ∧
        α k a = γ a ∧ α k b = γ b ∧
        (α k =ᶠ[𝓝 a] fun _ ↦ γ a) ∧ (α k =ᶠ[𝓝 b] fun _ ↦ γ b) ∧
        (∀ s, s ≤ a → α k s = γ a) ∧ (∀ s, b ≤ s → α k s = γ b) ∧
        MapsTo (α k) (Icc a b) K ∧
        ∀ s, HasDerivAt ((extChartAt (𝓡 n) x) ∘ α k) (d k s) s) ∧
      TendstoUniformlyOn α γ atTop (Icc a b) ∧
      Tendsto (fun k ↦ (hdLp k).toLp (d k)) atTop (𝓝 w) := by
  classical
  let e := extChartAt (𝓡 n) x
  let u : ℝ → EuclideanSpace ℝ (Fin n) := e ∘ γ
  have hsrc' : MapsTo γ (Icc a b) e.source := by
    simpa only [e, extChartAt_source] using hsrc
  have hu : ContinuousOn u (Icc a b) :=
    (continuousOn_extChartAt (I := 𝓡 n) x).comp hγ hsrc'
  have hutarget : u '' Icc a b ⊆ e.target := by
    rintro z ⟨s, hs, rfl⟩
    exact e.map_source (hsrc' hs)
  obtain ⟨C, hC, huC, hCtarget⟩ := exists_compact_between
    (isCompact_Icc.image_of_continuousOn hu) (isOpen_extChartAt_target (I := 𝓡 n) x) hutarget
  have huC' : MapsTo u (Icc a b) C :=
    fun s hs ↦ interior_subset (huC (mem_image_of_mem u hs))
  obtain ⟨f, d, hdLp, hf, hunif, hdlim⟩ :=
    chartL2_smooth_primitive_sequence hab u w hprimitive
  obtain ⟨δ, hδ, hmargin⟩ := (isCompact_Icc.image_of_continuousOn hu).exists_cthickening_subset_open
    isOpen_interior huC
  have htail : ∀ᶠ k in atTop, MapsTo (f k) (Icc a b) C := by
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hunif δ hδ] with k hk s hs
    apply interior_subset (hmargin ?_)
    exact Metric.mem_cthickening_of_dist_le _ (u s) _ _
      (mem_image_of_mem u hs) (by simpa only [dist_comm] using (hk s hs).le)
  obtain ⟨N, hN⟩ := eventually_atTop.mp htail
  have hCglobal (k : ℕ) (s : ℝ) : f (k + N) s ∈ C := by
    by_cases hsa : s < a
    · rw [(hf (k + N)).2.2.2.2.2.2.1 s hsa.le]
      exact huC' ⟨le_rfl, hab.le⟩
    by_cases hbs : b < s
    · rw [(hf (k + N)).2.2.2.2.2.2.2 s hbs.le]
      exact huC' ⟨hab.le, le_rfl⟩
    exact hN (k + N) (Nat.le_add_left N k) ⟨le_of_not_gt hsa, le_of_not_gt hbs⟩
  let α : ℕ → ℝ → M := fun k ↦ e.symm ∘ f (k + N)
  let K := e.symm '' C
  have hKs : K ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) x).source := by
    rintro z ⟨y, hy, rfl⟩
    simpa only [e, extChartAt_source] using e.map_target (hCtarget hy)
  have hK : IsCompact K := hC.image_of_continuousOn
    ((continuousOn_extChartAt_symm (I := 𝓡 n) x).mono hCtarget)
  have hγK : MapsTo γ (Icc a b) K := by
    intro s hs
    exact ⟨u s, huC' hs, e.left_inv (hsrc' hs)⟩
  have heq (k : ℕ) : e ∘ α k = f (k + N) := by
    funext s
    exact e.right_inv (hCtarget (hCglobal k s))
  have hα (k : ℕ) : ContMDiff (𝓘(ℝ, ℝ)) (𝓡 n) ∞ (α k) := by
    rw [← contMDiffOn_univ]
    exact (contMDiffOn_extChartAt_symm (I := 𝓡 n) x).comp
      (hf (k + N)).1.contMDiff.contMDiffOn (fun s _ ↦ hCtarget (hCglobal k s))
  have hαa (k : ℕ) : α k a = γ a := by
    change e.symm (f (k + N) a) = γ a
    rw [(hf (k + N)).2.1]
    exact e.left_inv (hsrc' ⟨le_rfl, hab.le⟩)
  have hαb (k : ℕ) : α k b = γ b := by
    change e.symm (f (k + N) b) = γ b
    rw [(hf (k + N)).2.2.1]
    exact e.left_inv (hsrc' ⟨hab.le, le_rfl⟩)
  have hshift : StrictMono (fun k : ℕ ↦ k + N) := fun _ _ h ↦ Nat.add_lt_add_right h N
  have hfunif : TendstoUniformlyOn (fun k ↦ f (k + N)) u atTop (Icc a b) := by
    intro U hU
    exact hshift.tendsto_atTop.eventually (hunif U hU)
  have hαlim : TendstoUniformlyOn α γ atTop (Icc a b) := by
    have h := UniformContinuousOn.comp_tendstoUniformlyOn_eventually
      (F := fun k ↦ f (k + N)) (f := u) (g := e.symm)
      (Eventually.of_forall (fun k s _ ↦ hCglobal k s)) huC'
      (hC.uniformContinuousOn_of_continuous
        ((continuousOn_extChartAt_symm (I := 𝓡 n) x).mono hCtarget)) hfunif
    exact h.congr_right (fun s hs ↦ e.left_inv (hsrc' hs))
  refine ⟨α, fun k ↦ d (k + N), fun k ↦ hdLp (k + N), K, hK, hKs, hγK,
    ?_, hαlim, hdlim.comp hshift.tendsto_atTop⟩
  intro k
  refine ⟨hα k, hαa k, hαb k, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · filter_upwards [(hf (k + N)).2.2.2.2.1] with s hs
    change e.symm (f (k + N) s) = γ a
    rw [hs]
    exact e.left_inv (hsrc' ⟨le_rfl, hab.le⟩)
  · filter_upwards [(hf (k + N)).2.2.2.2.2.1] with s hs
    change e.symm (f (k + N) s) = γ b
    rw [hs]
    exact e.left_inv (hsrc' ⟨hab.le, le_rfl⟩)
  · intro s hs
    change e.symm (f (k + N) s) = γ a
    rw [(hf (k + N)).2.2.2.2.2.2.1 s hs]
    exact e.left_inv (hsrc' ⟨le_rfl, hab.le⟩)
  · intro s hs
    change e.symm (f (k + N) s) = γ b
    rw [(hf (k + N)).2.2.2.2.2.2.2 s hs]
    exact e.left_inv (hsrc' ⟨hab.le, le_rfl⟩)
  · intro s _
    exact mem_image_of_mem e.symm (hCglobal k s)
  · intro s
    change HasDerivAt (e ∘ α k) _ s
    rw [heq]
    exact (hf (k + N)).2.2.2.1 s

theorem smooth_chart_recovery {a b : ℝ} (hab : a ≤ b) (x : M)
    (γ : ℝ → M) (hγ : ContinuousOn γ (Icc a b))
    (hsrc : MapsTo γ (Icc a b) (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    (w : ChartL2 (EuclideanSpace ℝ (Fin n)) a b)
    (hprimitive : ∀ s ∈ Icc a b,
      extChartAt (𝓡 n) x (γ s) = extChartAt (𝓡 n) x (γ a) + ∫ r in a..s, w r) :
    ∃ (α : ℕ → ℝ → M) (d : ℕ → ℝ → EuclideanSpace ℝ (Fin n))
      (hdLp : ∀ k, MemLp (d k) 2 (volume.restrict (Icc a b))) (K : Set M),
      IsCompact K ∧ K ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) x).source ∧
      MapsTo γ (Icc a b) K ∧
      (∀ k, ContMDiff (𝓘(ℝ, ℝ)) (𝓡 n) ∞ (α k) ∧
        α k a = γ a ∧ α k b = γ b ∧
        (α k =ᶠ[𝓝 a] fun _ ↦ γ a) ∧ (α k =ᶠ[𝓝 b] fun _ ↦ γ b) ∧
        (∀ s, s ≤ a → α k s = γ a) ∧ (∀ s, b ≤ s → α k s = γ b) ∧
        MapsTo (α k) (Icc a b) K ∧
        ∀ s, HasDerivAt ((extChartAt (𝓡 n) x) ∘ α k) (d k s) s) ∧
      TendstoUniformlyOn α γ atTop (Icc a b) ∧
      Tendsto (fun k ↦ (hdLp k).toLp (d k)) atTop (𝓝 w) := by
  rcases hab.lt_or_eq with hab | rfl
  · exact smooth_chart_recovery_of_lt hab x γ hγ hsrc w hprimitive
  · have hw : w = 0 := by
      apply Lp.ext
      simp [Filter.EventuallyEq]
    have hzLp : MemLp (fun _ : ℝ ↦ (0 : EuclideanSpace ℝ (Fin n))) 2
        (volume.restrict (Icc a a)) := MemLp.zero'
    refine ⟨fun _ _ ↦ γ a, fun _ _ ↦ 0, fun _ ↦ hzLp, {γ a},
      isCompact_singleton, ?_, ?_, ?_, ?_, ?_⟩
    · simpa using hsrc (show a ∈ Icc a a from ⟨le_rfl, le_rfl⟩)
    · intro s hs
      have hs' : s = a := le_antisymm hs.2 hs.1
      simp only [hs', mem_singleton_iff]
    · intro k
      exact ⟨contMDiff_const, rfl, rfl, Filter.EventuallyEq.rfl,
        Filter.EventuallyEq.rfl, fun _ _ ↦ rfl, fun _ _ ↦ rfl,
        fun _ _ ↦ mem_singleton _, fun s ↦ hasDerivAt_const s _⟩
    · apply Metric.tendstoUniformlyOn_iff.mpr
      intro ε hε
      apply Eventually.of_forall
      intro k s hs
      have hs' : s = a := le_antisymm hs.2 hs.1
      simpa only [hs', dist_self] using hε
    · have heq : hzLp.toLp (fun _ ↦ 0) = w := by
        rw [hw]
        exact hzLp.toLp_zero
      simpa only [heq] using (tendsto_const_nhds (x := w) : Tendsto
        (fun _ : ℕ ↦ w) atTop (𝓝 w))

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem chart_piece_integrable {J : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T : ℝ) {a b : ℝ} (hab : a ≤ b)
    (x : M) (α : ℝ → M) (hα : ContinuousOn α (Icc a b))
    (hreg : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) 1 α (Ioo a b))
    (hsrc : MapsTo α (Icc a b) (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    (htime : ∀ s ∈ Icc a b, T - s ^ 2 ∈ J)
    (v : ChartL2 (EuclideanSpace ℝ (Fin n)) a b)
    (hv : (v : ℝ → EuclideanSpace ℝ (Fin n)) =ᵐ[volume.restrict (Icc a b)]
      deriv ((extChartAt (𝓡 n) x) ∘ α)) :
    IntervalIntegrable (regularizedLIntegrand F T α) volume a b := by
  let E := EuclideanSpace ℝ (Fin n)
  let μ := volume.restrict (Icc a b)
  let B : ℝ → E →L[ℝ] E →L[ℝ] ℝ := fun s ↦ regularizedChartMetric F T x (s, α s)
  have hBcont : ContinuousOn B (Icc a b) :=
    (regularizedChartMetric_continuousOn F T x htime (Subset.rfl)).comp
      (continuousOn_id.prodMk hα) (fun s hs ↦ ⟨hs, hsrc hs⟩)
  have hB : MemLp B (⊤ : ENNReal) μ :=
    continuousOn_memLp_top_Icc (f := B) (a := a) (b := b) hBcont
  have hkin : Integrable (fun s ↦ B s (v s) (v s)) μ :=
    chart_density_integrable B hB v
  let V := fun s ↦ 2 * s ^ 2 * (F.connection (T - s ^ 2)).scalarCurvature (α s)
  have hV : ContinuousOn V (Icc a b) :=
    (regularizedPotential_continuousOn F hM04 T (K := univ) htime).comp
      (continuousOn_id.prodMk hα) (fun s hs ↦ ⟨hs, mem_univ _⟩)
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
  apply (hkin.add (hV.integrableOn_Icc)).congr
  have hmem : ∀ᵐ s ∂μ, s ∈ Ioo a b := by
    dsimp only [μ]
    rw [← restrict_Ioo_eq_restrict_Icc]
    exact ae_restrict_mem measurableSet_Ioo
  filter_upwards [hv, hmem] with s hs hsI
  simp only [Pi.add_apply]
  rw [hs]
  have hdiff := ((hreg s hsI).contMDiffAt (isOpen_Ioo.mem_nhds hsI)).mdifferentiableAt
    (by norm_num)
  change (1 / 2 : ℝ) * metricInChart (F.metric (T - s ^ 2)) x (α s)
    (deriv ((extChartAt (𝓡 n) x) ∘ α) s) (deriv ((extChartAt (𝓡 n) x) ∘ α) s) + V s = _
  rw [metricInChart_deriv _ (hsrc (Ioo_subset_Icc_self hsI)) hdiff]
  exact add_comm _ _

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem chart_piece_action_tendsto {J : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T : ℝ) {a b : ℝ} (hab : a ≤ b)
    (x : M) {K : Set M} (hK : IsCompact K)
    (hsrc : K ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    (htime : ∀ s ∈ Icc a b, T - s ^ 2 ∈ J)
    (α : ℕ → ℝ → M) (γ : ℝ → M)
    (hα : ∀ k, ContinuousOn (α k) (Icc a b)) (hγ : ContinuousOn γ (Icc a b))
    (hαK : ∀ k, MapsTo (α k) (Icc a b) K) (hγK : MapsTo γ (Icc a b) K)
    (hlim : TendstoUniformlyOn α γ atTop (Icc a b))
    (v : ℕ → ChartL2 (EuclideanSpace ℝ (Fin n)) a b)
    (w : ChartL2 (EuclideanSpace ℝ (Fin n)) a b) (hv : Tendsto v atTop (𝓝 w)) :
    Tendsto (fun k ↦
      (∫ s in a..b, regularizedChartMetric F T x (s, α k s) (v k s) (v k s)) +
        ∫ s in a..b, 2 * s ^ 2 * (F.connection (T - s ^ 2)).scalarCurvature (α k s))
      atTop (𝓝 ((∫ s in a..b, regularizedChartMetric F T x (s, γ s) (w s) (w s)) +
        ∫ s in a..b, 2 * s ^ 2 * (F.connection (T - s ^ 2)).scalarCurvature (γ s))) := by
  let B k s := regularizedChartMetric F T x (s, α k s)
  let D s := regularizedChartMetric F T x (s, γ s)
  have hB (k : ℕ) : MemLp (B k) (⊤ : ENNReal) (volume.restrict (Icc a b)) :=
    continuousOn_memLp_top_Icc (f := B k) (a := a) (b := b)
      ((regularizedChartMetric_continuousOn F T x htime hsrc).comp
        (continuousOn_id.prodMk (hα k)) (fun s hs ↦ ⟨hs, hαK k hs⟩))
  have hD : MemLp D (⊤ : ENNReal) (volume.restrict (Icc a b)) :=
    continuousOn_memLp_top_Icc (f := D) (a := a) (b := b)
      ((regularizedChartMetric_continuousOn F T x htime hsrc).comp
        (continuousOn_id.prodMk hγ) (fun s hs ↦ ⟨hs, hγK hs⟩))
  let Qk k := integratedFormMap _ ((hB k).toLp (B k))
  let Q := integratedFormMap _ (hD.toLp D)
  have hQ : Tendsto Qk atTop (𝓝 Q) := by
    apply (tendsto_iff_norm_sub_tendsto_zero (f := Qk) (b := Q)).mpr
    apply integratedForm_tendsto_of_uniform B D hB hD
    exact uniform_composition_on_compact_core hK _
      (regularizedChartMetric_continuousOn F T x htime hsrc) α γ
      (Eventually.of_forall hαK) hγK hlim
  have hQeq (z : ChartL2 (EuclideanSpace ℝ (Fin n)) a b) :
      Q z z = ∫ s in a..b, D s (z s) (z s) := by
    rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc,
      integratedFormMap_apply]
    apply integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp
      (E := EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
      hD] with s hs
    rw [hs]
  have hQkeq (k : ℕ) : Qk k (v k) (v k) = ∫ s in a..b, B k s (v k s) (v k s) := by
    rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc,
      integratedFormMap_apply]
    apply integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp
      (E := EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
      (hB k)] with s hs
    rw [hs]
  have hkin : Tendsto (fun k ↦ Qk k (v k) (v k)) atTop (𝓝 (Q w w)) :=
    quadratic_form_tendsto Qk Q v w hQ hv
  let V : ℝ × M → ℝ := fun z ↦
    2 * z.1 ^ 2 * (F.connection (T - z.1 ^ 2)).scalarCurvature z.2
  have hV : ContinuousOn V (Icc a b ×ˢ K) := regularizedPotential_continuousOn F hM04 T htime
  have hpot : Tendsto (fun k ↦ ∫ s in a..b, V (s, α k s)) atTop
      (𝓝 (∫ s in a..b, V (s, γ s))) := by
    apply TendstoUniformlyOn.tendsto_intervalIntegral_of_continuousOn
    · apply Eventually.of_forall
      intro k
      rw [uIcc_of_le hab]
      exact hV.comp (continuousOn_id.prodMk (hα k)) (fun s hs ↦ ⟨hs, hαK k hs⟩)
    · rw [uIcc_of_le hab]
      exact uniform_composition_on_compact_core hK V hV α γ
        (Eventually.of_forall hαK) hγK hlim
  simpa only [hQeq, hQkeq, B, D, V] using hkin.add hpot

end PoincareConjecture.M08
