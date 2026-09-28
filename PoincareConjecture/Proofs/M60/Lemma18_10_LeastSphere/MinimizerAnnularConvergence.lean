import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerCompactnessTarget
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.EpsilonRegularityDecay
import Mathlib.Topology.UniformSpace.CompactConvergence
import Mathlib.Topology.MetricSpace.Thickening










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric Topology
open scoped Topology Manifold ContDiff

noncomputable section

namespace PoincareConjecture.M60

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]




theorem suChartReadable_differential_injective
    {d : ℕ} {e : M → EuclideanSpace ℝ (Fin d)}
    (he : ContMDiff (𝓡 n) (𝓡 d) ∞ e) (hread : SUChartReadable (n := n) e) :
    ∀ p, Function.Injective (mfderiv (𝓡 n) (𝓡 d) e p) := by
  intro p u v huv
  obtain ⟨b, hb, L, hL⟩ := hread p
  apply (isInvertible_mfderiv_extChartAt hb).injective
  have hchain (w : TangentSpace (𝓡 n) p) :
      mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) b) p w =
        L (mfderiv (𝓡 n) (𝓡 d) e p w) := by
    rw [← hL.mfderiv_eq (I := 𝓡 n) (I' := 𝓡 n)]
    have h := mfderiv_comp_apply p
      L.hasFDerivAt.hasMFDerivAt.mdifferentiableAt ((he p).mdifferentiableAt (by simp)) w
    erw [mfderiv_eq_fderiv, L.fderiv] at h
    change (mfderiv (𝓡 n) (𝓡 n) (fun q => L (e q)) p w : EuclideanSpace ℝ (Fin n)) = _
    exact h
  rw [hchain, hchain, huv]



theorem suObservation_tendsto_compactOpen
    {d : ℕ} {e : M → EuclideanSpace ℝ (Fin d)} (he : Continuous e)
    (hei : IsEmbedding e) (f : ℕ → C(LoopPlane, M)) (v : C(LoopPlane, M))
    (hvalue : TendstoLocallyUniformly (fun j => e ∘ f j) (e ∘ v) atTop) :
    Tendsto f atTop (𝓝 v) := by
  let E : C(M, EuclideanSpace ℝ (Fin d)) := ⟨e, he⟩
  have h := ContinuousMap.tendsto_of_tendstoLocallyUniformly
    (F := fun j => E.comp (f j)) (f := E.comp v) hvalue
  exact (E.isInducing_postcomp (X := LoopPlane) hei.isInducing).tendsto_nhds_iff.mpr h




theorem suCompactOpen_eventually_pairs
    (f : ℕ → C(LoopPlane, M)) (v : C(LoopPlane, M))
    (hlim : Tendsto f atTop (𝓝 v))
    (a : C(unitInterval × LoopPlane, M))
    {K : Set (unitInterval × LoopPlane)} (hK : IsCompact K)
    {U : Set (M × M)} (hU : IsOpen U)
    (hpair : ∀ x ∈ K, (v x.2, a x) ∈ U) :
    ∀ᶠ j in atTop, ∀ x ∈ K, (f j x.2, a x) ∈ U := by
  let Φ : C(LoopPlane, M) → C(unitInterval × LoopPlane, M × M) := fun F =>
    ⟨fun x => (F x.2, a x), (F.continuous.comp continuous_snd).prodMk a.continuous⟩
  have hΦ : Continuous Φ := ContinuousMap.continuous_of_continuous_uncurry Φ
    ((continuous_eval.comp (continuous_fst.prodMk continuous_snd.snd)).prodMk
      (a.continuous.comp continuous_snd))
  exact ContinuousMap.tendsto_nhds_compactOpen.mp (hΦ.continuousAt.tendsto.comp hlim)
    K hK U hU hpair

open scoped Bundle in



theorem suObservation_metric_derivative_bound [CompactSpace M] [T2Space M]
    (g : RiemannianMetric n M) {d : ℕ} {e : M → EuclideanSpace ℝ (Fin d)}
    (he : ContMDiff (𝓡 n) (𝓡 d) ∞ e) (hread : SUChartReadable (n := n) e) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : LoopPlane → M), ContMDiff (𝓡 2) (𝓡 n) 1 f →
      ∀ z w : LoopPlane, g.tangentNorm (f z) (mfderiv (𝓡 2) (𝓡 n) f z w) ≤
        C * ‖fderiv ℝ (e ∘ f) z‖ * ‖w‖ := by
  obtain ⟨c, hc, hbound⟩ := suEmbedding_differential_lower_bound g e he
    (suChartReadable_differential_injective he hread)
  refine ⟨(Real.sqrt c)⁻¹, inv_pos.mpr (Real.sqrt_pos.mpr hc), ?_⟩
  intro f hf z w
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let W := mfderiv (𝓡 2) (𝓡 n) f z w
  have h := hbound (f z) W
  have hchain := mfderiv_comp_apply z ((he (f z)).mdifferentiableAt (by simp))
    ((hf z).mdifferentiableAt one_ne_zero) w
  rw [mfderiv_eq_fderiv] at hchain
  rw [← hchain] at h
  have hw : g.inner (f z) W W = ‖W‖ ^ 2 := real_inner_self_eq_norm_sq W
  rw [hw] at h
  have hs : Real.sqrt c * ‖W‖ ≤ ‖fderiv ℝ (e ∘ f) z w‖ := by
    have hsq : (Real.sqrt c * ‖W‖) ^ 2 ≤ ‖fderiv ℝ (e ∘ f) z w‖ ^ 2 := by
      rwa [mul_pow, Real.sq_sqrt hc.le]
    exact (sq_le_sq₀ (by positivity) (norm_nonneg _)).mp hsq
  have ho := (fderiv ℝ (e ∘ f) z).le_opNorm w
  change ‖W‖ ≤ _
  calc
    ‖W‖ ≤ (‖fderiv ℝ (e ∘ f) z‖ * ‖w‖) / Real.sqrt c :=
      (le_div_iff₀ (Real.sqrt_pos.mpr hc)).mpr (by
        simpa only [mul_comm] using hs.trans ho)
    _ = _ := by ring




theorem suObservation_eventually_metric_bound [CompactSpace M] [T2Space M]
    (g : RiemannianMetric n M) {d : ℕ} {e : M → EuclideanSpace ℝ (Fin d)}
    (he : ContMDiff (𝓡 n) (𝓡 d) ∞ e) (hread : SUChartReadable (n := n) e)
    (f : ℕ → LoopPlane → M) (hf : ∀ j, ContMDiff (𝓡 2) (𝓡 n) 1 (f j))
    {v : LoopPlane → M} (hv : ContMDiff (𝓡 2) (𝓡 n) 1 v)
    (hjet : TendstoLocallyUniformly (fun j => fderiv ℝ (e ∘ f j))
      (fderiv ℝ (e ∘ v)) atTop)
    {K : Set LoopPlane} (hK : IsCompact K) :
    ∃ L : ℝ, 0 < L ∧ ∀ᶠ j in atTop, ∀ z ∈ K, ∀ w : LoopPlane,
      g.tangentNorm (f j z) (mfderiv (𝓡 2) (𝓡 n) (f j) z w) ≤ L * ‖w‖ := by
  obtain ⟨C, hC, hbound⟩ := suObservation_metric_derivative_bound g he hread
  have hobs : ContDiff ℝ 1 (e ∘ v) :=
    contMDiff_iff_contDiff.mp ((he.of_le (by simp)).comp hv)
  obtain ⟨T, hT⟩ := hK.exists_bound_of_continuousOn
    (hobs.continuous_fderiv one_ne_zero).continuousOn
  have hu : TendstoUniformlyOn (fun j => fderiv ℝ (e ∘ f j))
      (fderiv ℝ (e ∘ v)) atTop K :=
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp
      hjet.tendstoLocallyUniformlyOn
  refine ⟨C * (max T 0 + 1), mul_pos hC (by positivity), ?_⟩
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hu 1 (by norm_num)] with j hj
  intro z hz w
  have hd := hj z hz
  have ht : ‖fderiv ℝ (e ∘ f j) z‖ ≤ max T 0 + 1 := by
    have hn := norm_le_norm_add_norm_sub (fderiv ℝ (e ∘ v) z) (fderiv ℝ (e ∘ f j) z)
    rw [dist_eq_norm] at hd
    linarith [(hT z hz).trans (le_max_left T 0)]
  exact (hbound (f j) (hf j) z w).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht hC.le) (norm_nonneg w))



theorem suObservation_metric_bound_on_compact [CompactSpace M] [T2Space M]
    (g : RiemannianMetric n M) {d : ℕ} {e : M → EuclideanSpace ℝ (Fin d)}
    (he : ContMDiff (𝓡 n) (𝓡 d) ∞ e) (hread : SUChartReadable (n := n) e)
    {f : LoopPlane → M} (hf : ContMDiff (𝓡 2) (𝓡 n) 1 f)
    {K : Set LoopPlane} (hK : IsCompact K) :
    ∃ L : ℝ, 0 < L ∧ ∀ z ∈ K, ∀ w : LoopPlane,
      g.tangentNorm (f z) (mfderiv (𝓡 2) (𝓡 n) f z w) ≤ L * ‖w‖ := by
  obtain ⟨C, hC, hbound⟩ := suObservation_metric_derivative_bound g he hread
  have hobs : ContDiff ℝ 1 (e ∘ f) :=
    contMDiff_iff_contDiff.mp ((he.of_le (by simp)).comp hf)
  obtain ⟨T, hT⟩ := hK.exists_bound_of_continuousOn
    (hobs.continuous_fderiv one_ne_zero).continuousOn
  refine ⟨C * (max T 0 + 1), mul_pos hC (by positivity), fun z hz w => ?_⟩
  exact (hbound f hf z w).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left ((hT z hz).trans (by linarith [le_max_left T 0])) hC.le)
      (norm_nonneg w))




theorem suCircle_family_neighborhood
    {Y : Type*} [TopologicalSpace Y] {F : unitInterval × LoopPlane → Y}
    (hF : Continuous F) {U : Set Y} (hU : IsOpen U) {R : ℝ} (hR : 0 < R)
    (hcircle : ∀ t : unitInterval, ∀ z : LoopPlane, ‖z‖ = R → F (t, z) ∈ U) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∀ t : unitInterval, ∀ z : LoopPlane,
      R - epsilon < ‖z‖ → ‖z‖ < R + epsilon → F (t, z) ∈ U := by
  have hc : (univ : Set unitInterval) ×ˢ sphere (0 : LoopPlane) R ⊆ F ⁻¹' U := by
    rintro ⟨t, z⟩ hz
    exact hcircle t z (by simpa only [mem_sphere_zero_iff_norm] using hz.2)
  obtain ⟨T, V, _, hV, hT, hsV, hTV⟩ := generalized_tube_lemma
    isCompact_univ (isCompact_sphere (0 : LoopPlane) R) (hU.preimage hF) hc
  obtain ⟨delta, hdelta, hdV⟩ :=
    (isCompact_sphere (0 : LoopPlane) R).exists_thickening_subset_open hV hsV
  let epsilon := min (R / 2) delta
  have hepsilon : 0 < epsilon := lt_min (half_pos hR) hdelta
  refine ⟨epsilon, hepsilon, ?_⟩
  intro t z hlo hhi
  have hr : 0 < ‖z‖ := by
    have he := min_le_left (R / 2) delta
    dsimp only [epsilon] at hlo
    linarith
  let p := (R / ‖z‖) • z
  have hp : p ∈ sphere (0 : LoopPlane) R := by
    rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_of_nonneg (div_nonneg hR.le hr.le)]
    exact div_mul_cancel₀ R hr.ne'
  have hd : dist z p = |‖z‖ - R| := by
    rw [dist_eq_norm]
    have heq : z - p = (1 - R / ‖z‖) • z := by simp only [p, sub_smul, one_smul]
    rw [heq, norm_smul, Real.norm_eq_abs, ← abs_of_pos hr, ← abs_mul]
    congr 1
    field_simp
    rw [abs_of_pos hr]
    ring
  have hdist : dist z p < delta := by
    rw [hd]
    exact (abs_lt.mpr ⟨by linarith only [hlo], by linarith only [hhi]⟩).trans_le
      (min_le_right (R / 2) delta)
  exact hTV ⟨hT (mem_univ t), hdV (Metric.mem_thickening_iff.mpr ⟨p, hp, hdist⟩)⟩

end PoincareConjecture.M60
