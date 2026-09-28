import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Coarea.Continuity
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.PartitionOfUnity.CompactSupport
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory TopologicalSpace
open Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Bundle Topology

private theorem tendsto_integral_outerApprox_mul
    {X Y : Type*} [MeasurableSpace X] [TopologicalSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] [HasOuterApproxClosed Y]
    {μ : Measure X} {H : X → ℝ}
    (hH : Integrable H μ) {f : X → Y} (hf : Measurable f)
    {s : Set Y} (hs : IsClosed s) :
    Tendsto (fun k : ℕ => ∫ x, (hs.apprSeq k (f x) : ℝ) * H x ∂μ)
      atTop (𝓝 (∫ x in f ⁻¹' s, H x ∂μ)) := by
  rw [← integral_indicator (hs.measurableSet.preimage hf)]
  apply tendsto_integral_of_dominated_convergence (fun x => ‖H x‖)
  · intro k
    have hmeas : Measurable (fun x => (hs.apprSeq k (f x) : ℝ)) :=
      (NNReal.continuous_coe.comp (hs.apprSeq k).continuous).measurable.comp hf
    exact hmeas.aestronglyMeasurable.mul hH.aestronglyMeasurable
  · exact hH.norm
  · intro k
    filter_upwards [] with x
    rw [norm_mul]
    apply mul_le_of_le_one_left (norm_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg (hs.apprSeq k (f x)).coe_nonneg]
    exact_mod_cast HasOuterApproxClosed.apprSeq_apply_le_one hs k (f x)
  · filter_upwards [] with x
    have ht := (NNReal.continuous_coe.tendsto _).comp
      (tendsto_pi_nhds.mp (HasOuterApproxClosed.tendsto_apprSeq hs) (f x))
    have hm := ht.mul_const (H x)
    by_cases hx : f x ∈ s <;> simpa [hx] using hm

theorem PoincareConjecture.RiemannianMetric.integral_coarea_isCompact
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [MeasurableSpace M] [BorelSpace M] [T3Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M]
    [IsManifold (𝓡 (n + 1)) ∞ M]
    (g : PoincareConjecture.RiemannianMetric (n + 1) M)
    {f : M → ℝ} (hf : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ f)
    (U : TopologicalSpace.Opens M)
    (hreg : ∀ x ∈ U, mfderiv (𝓡 (n + 1)) 𝓘(ℝ, ℝ) f x ≠ 0)
    {S : Set M} (hS : IsCompact S) (hSU : S ⊆ U) :
    Integrable (fun t : ℝ => (g.regularLevelVolume hf U hreg t).real
      {z | openLevelIncl f U t z ∈ S}) ∧
      (∫ x in S, g.tangentNorm x (g.gradient f x) ∂g.volumeMeasure) =
        ∫ t : ℝ, (g.regularLevelVolume hf U hreg t).real
          {z | openLevelIncl f U t z ∈ S} := by
  classical
  let : HasOuterApproxClosed M := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 (n + 1)) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin (n + 1)))
        (TangentSpace (𝓡 (n + 1)) : M → Type _) :=
      ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
    let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 (n + 1)) M
    infer_instance
  obtain ⟨χ, hχ, hcχ, hsχ, hχ01, hχone⟩ :=
    PoincareConjecture.exists_contMDiff_cutoff_of_isCompact (n := n + 1) hS U.isOpen hSU
  have hχS (x : M) (hx : x ∈ S) : χ x = 1 :=
    (hχone x hx).eq_of_nhds
  let χk : ℕ → M → ℝ := fun k x => (hS.isClosed.apprSeq k x : ℝ) * χ x
  have hχk (k : ℕ) : Continuous (χk k) :=
    (NNReal.continuous_coe.comp (hS.isClosed.apprSeq k).continuous).mul hχ.continuous
  have hχkc (k : ℕ) : HasCompactSupport (χk k) := hcχ.mul_left
  have hχkU (k : ℕ) : tsupport (χk k) ⊆ U :=
    tsupport_mul_subset_right.trans hsχ
  have hχkb (k : ℕ) (x : M) : 0 ≤ χk k x ∧ χk k x ≤ χ x := by
    constructor
    · exact mul_nonneg (hS.isClosed.apprSeq k x).coe_nonneg (hχ01 x).1
    · apply mul_le_of_le_one_left (hχ01 x).1
      exact_mod_cast HasOuterApproxClosed.apprSeq_apply_le_one hS.isClosed k x
  let A : ℝ → ℝ := fun t => (g.regularLevelVolume hf U hreg t).real
    {z | openLevelIncl f U t z ∈ S}
  let B : ℝ → ℝ := fun t => ∫ z, χ (openLevelIncl f U t z)
    ∂g.regularLevelVolume hf U hreg t
  let Ak : ℕ → ℝ → ℝ := fun k t => ∫ z, χk k (openLevelIncl f U t z)
    ∂g.regularLevelVolume hf U hreg t
  have hBi : Integrable B :=
    (g.continuous_regularLevelIntegral hf U hreg hχ.continuous hcχ hsχ).integrable_of_hasCompactSupport
      (g.hasCompactSupport_regularLevelIntegral hf U hreg hcχ)
  have hAki (k : ℕ) : Integrable (Ak k) :=
    (g.continuous_regularLevelIntegral hf U hreg (hχk k) (hχkc k) (hχkU k)).integrable_of_hasCompactSupport
      (g.hasCompactSupport_regularLevelIntegral hf U hreg (hχkc k))
  have hχi (t : ℝ) : Integrable (fun z => χ (openLevelIncl f U t z))
      (g.regularLevelVolume hf U hreg t) :=
    g.integrable_regularLevelVolume_of_hasCompactSupport hf U hreg t hχ.continuous hcχ hsχ
  have hχki (k : ℕ) (t : ℝ) : Integrable (fun z => χk k (openLevelIncl f U t z))
      (g.regularLevelVolume hf U hreg t) :=
    g.integrable_regularLevelVolume_of_hasCompactSupport hf U hreg t (h := χk k) (hχk k) (hχkc k) (hχkU k)
  have hAkb (k : ℕ) (t : ℝ) : 0 ≤ Ak k t ∧ Ak k t ≤ B t := by
    constructor
    · exact integral_nonneg fun z => (hχkb k _).1
    · exact integral_mono (hχki k t) (hχi t) fun z => (hχkb k _).2
  have hlim (t : ℝ) : Tendsto (fun k => Ak k t) atTop (𝓝 (A t)) := by
    have hi := tendsto_integral_outerApprox_mul (hχi t)
      (isEmbedding_openLevelIncl f U t).continuous.measurable hS.isClosed
    have heq : (∫ z in {z | openLevelIncl f U t z ∈ S},
        χ (openLevelIncl f U t z) ∂g.regularLevelVolume hf U hreg t) = A t := by
      rw [show A t = ∫ z in {z | openLevelIncl f U t z ∈ S}, (1 : ℝ)
          ∂g.regularLevelVolume hf U hreg t by simp [A]]
      apply setIntegral_congr_fun (hS.isClosed.measurableSet.preimage
        (isEmbedding_openLevelIncl f U t).continuous.measurable)
      intro z hz
      exact hχS _ hz
    exact heq ▸ hi
  have hAb (t : ℝ) : 0 ≤ A t ∧ A t ≤ B t := by
    exact ⟨ge_of_tendsto' (hlim t) (fun k => (hAkb k t).1),
      le_of_tendsto' (hlim t) (fun k => (hAkb k t).2)⟩
  have hAm : AEStronglyMeasurable A :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun k => (hAki k).aestronglyMeasurable)
      (Eventually.of_forall hlim)
  have hAi : Integrable A := hBi.mono' hAm (Eventually.of_forall fun t => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hAb t).1]
    exact (hAb t).2)
  refine ⟨hAi, ?_⟩
  have hout : Tendsto (fun k => ∫ t, Ak k t) atTop (𝓝 (∫ t, A t)) := by
    apply tendsto_integral_of_dominated_convergence B
    · exact fun k => (hAki k).aestronglyMeasurable
    · exact hBi
    · intro k
      filter_upwards [] with t
      rw [Real.norm_eq_abs, abs_of_nonneg (hAkb k t).1]
      exact (hAkb k t).2
    · exact Eventually.of_forall hlim
  have hleft := tendsto_integral_outerApprox_mul
    (g.integrable_volumeMeasure_of_hasCompactSupport
      (hχ.continuous.mul (g.continuous_tangentNorm_gradient hf)) hcχ.mul_right)
    measurable_id hS.isClosed
  have hleftval : (∫ x in S, χ x * g.tangentNorm x (g.gradient f x) ∂g.volumeMeasure) =
      ∫ x in S, g.tangentNorm x (g.gradient f x) ∂g.volumeMeasure := by
    apply setIntegral_congr_fun hS.measurableSet
    intro x hx
    dsimp only
    rw [hχS x hx, one_mul]
  have heq (k : ℕ) :
      (∫ x, (hS.isClosed.apprSeq k x : ℝ) *
        (χ x * g.tangentNorm x (g.gradient f x)) ∂g.volumeMeasure) = ∫ t, Ak k t := by
    have hcoarea := g.integral_coarea hf U hreg (hχk k) (hχkc k) (hχkU k)
    calc
      _ = ∫ x in (U : Set M), χk k x *
          g.tangentNorm x (g.gradient f x) ∂g.volumeMeasure := by
        rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
        · apply integral_congr_ae
          filter_upwards [] with x
          exact (mul_assoc _ _ _).symm
        · intro x hx
          rw [image_eq_zero_of_notMem_tsupport (fun ht => hx (hχkU k ht)), zero_mul]
      _ = _ := hcoarea
  have hleft' : Tendsto (fun k => ∫ t, Ak k t) atTop
      (𝓝 (∫ x in S, g.tangentNorm x (g.gradient f x) ∂g.volumeMeasure)) := by
    simp only [id_eq, Set.preimage_id, Pi.mul_apply] at hleft
    rw [hleftval] at hleft
    exact hleft.congr' (Eventually.of_forall heq)
  exact tendsto_nhds_unique hleft' hout
