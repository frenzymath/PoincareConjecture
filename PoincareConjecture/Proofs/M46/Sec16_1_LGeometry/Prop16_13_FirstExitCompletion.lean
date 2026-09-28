import PoincareConjecture.Proofs.M46.Sec16_1_LGeometry.Prop16_13_EndpointEnergy
import Mathlib.Topology.UniformSpace.UniformEmbedding
import Mathlib.Topology.Order.ProjIcc











set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology ENNReal Bundle

universe u

namespace PoincareConjecture.Proofs.M46

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M] [T3Space M]

omit [T3Space M] in


theorem referenceSpeedSq_congr_of_eventuallyEq (g : RiemannianMetric n M)
    {gamma eta : ℝ → M} {r : ℝ} (h : gamma =ᶠ[𝓝 r] eta) :
    M08.referenceSpeedSq g gamma r = M08.referenceSpeedSq g eta r := by
  unfold M08.referenceSpeedSq curveVelocity
  rw [h.mfderiv_eq, h.eq_of_nhds]




theorem exists_continuous_birthCurve_extension [CompactSpace M]
    (g : RiemannianMetric n M) {gamma : ℝ → M} {a b : ℝ} (hab : a < b)
    (hgamma : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) 1 gamma (Ioo a b))
    (henergy : IntervalIntegrable (M08.referenceSpeedSq g gamma) volume a b) :
    ∃ eta : ℝ → M, Continuous eta ∧ EqOn eta gamma (Ioo a b) ∧
      ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) 1 eta (Ioo a b) ∧
      IntervalIntegrable (M08.referenceSpeedSq g eta) volume a b ∧
      (∫ t in a..b, M08.referenceSpeedSq g eta t) =
        ∫ t in a..b, M08.referenceSpeedSq g gamma t := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  let E := ∫ t in a..b, M08.referenceSpeedSq g gamma t
  have hE : 0 ≤ E := intervalIntegral.integral_nonneg hab.le
    (fun t _ => M08.referenceSpeedSq_nonneg g gamma t)
  have hordered {s t C : ℝ} (hs : s ∈ Ioo a b) (ht : t ∈ Ioo a b)
      (hst : s ≤ t) (hC : 0 < C) :
      edist (gamma s) (gamma t) ≤ ENNReal.ofReal ((E + (t - s) * C ^ 2) / (2 * C)) := by
    have hsub : Icc s t ⊆ Ioo a b := Icc_subset_Ioo hs.1 ht.2
    have hspeed : ContinuousOn (fun r =>
        g.tangentNorm (gamma r) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) gamma r 1)) (Icc s t) :=
      Real.continuous_sqrt.comp_continuousOn
        ((M08.referenceSpeedSq_continuousOn g isOpen_Ioo hgamma).mono hsub)
    have h := g.edist_le_ofReal_energy_bound hst hC (hgamma.mono hsub) hspeed
    have hsq (r : ℝ) :
        (g.tangentNorm (gamma r) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) gamma r 1)) ^ 2 =
          M08.referenceSpeedSq g gamma r :=
      Real.sq_sqrt (M08.referenceSpeedSq_nonneg g gamma r)
    simp only [hsq] at h
    apply h.trans (ENNReal.ofReal_le_ofReal ?_)
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact add_le_add (intervalIntegral.integral_mono_interval hs.1.le hst ht.2.le
      (ae_of_all _ (M08.referenceSpeedSq_nonneg g gamma)) henergy) le_rfl
  have huniform : UniformContinuousOn gamma (Ioo a b) := by
    apply EMetric.uniformContinuousOn_iff.mpr
    intro epsilon hepsilon
    obtain ⟨eps, _, heps0, heps⟩ := ENNReal.lt_iff_exists_real_btwn.mp hepsilon
    have hepsPos : 0 < eps := ENNReal.ofReal_pos.mp heps0
    let C := (E + 1) / eps
    have hC : 0 < C := div_pos (by linarith) hepsPos
    let delta := eps / C
    have hdelta : 0 < delta := div_pos hepsPos hC
    have hEC : E < eps * C := by
      dsimp only [C]
      field_simp [hepsPos.ne']
      linarith
    have hsmall {s t : ℝ} (hs : s ∈ Ioo a b) (ht : t ∈ Ioo a b)
        (hst : s ≤ t) (hdt : t - s < delta) : edist (gamma s) (gamma t) < epsilon := by
      have hdtC : (t - s) * C < eps := (lt_div_iff₀ hC).mp hdt
      have hdtC2 : (t - s) * C ^ 2 < eps * C := by
        nlinarith [mul_lt_mul_of_pos_right hdtC hC]
      have hreal : (E + (t - s) * C ^ 2) / (2 * C) < eps := by
        apply (div_lt_iff₀ (by positivity : 0 < 2 * C)).mpr
        nlinarith
      exact ((hordered hs ht hst hC).trans_lt
        ((ENNReal.ofReal_lt_ofReal_iff hepsPos).mpr hreal)).trans heps
    refine ⟨ENNReal.ofReal delta, ENNReal.ofReal_pos.mpr hdelta, ?_⟩
    intro s hs t ht hdist
    have hd : |s - t| < delta := by simpa only [Real.dist_eq] using edist_lt_ofReal.mp hdist
    rcases le_total s t with hst | hts
    · exact hsmall hs ht hst (by linarith [neg_le_abs (s - t)])
    · rw [edist_comm]
      exact hsmall ht hs hts (by linarith [le_abs_self (s - t)])
  let inclusion : Ioo a b → Icc a b := Set.inclusion Ioo_subset_Icc_self
  have hui : IsUniformInducing inclusion :=
    (isUniformEmbedding_set_inclusion Ioo_subset_Icc_self).isUniformInducing
  have hdi : DenseRange inclusion := by
    apply (denseRange_inclusion_iff Ioo_subset_Icc_self).mpr
    simpa only [closure_Ioo hab.ne] using (Subset.rfl : Icc a b ⊆ Icc a b)
  let f : Ioo a b → M := fun t => gamma t.val
  have huf : UniformContinuous f := uniformContinuousOn_iff_restrict.mp huniform
  let extension := (hui.isDenseInducing hdi).extend f
  have hext : UniformContinuous extension := uniformContinuous_uniformly_extend hui hdi huf
  let eta : ℝ → M := fun t => extension (projIcc a b hab.le t)
  have heta : Continuous eta := hext.continuous.comp continuous_projIcc
  have heq : EqOn eta gamma (Ioo a b) := by
    intro t ht
    have h := (hui.isDenseInducing hdi).extend_eq huf.continuous (⟨t, ht⟩ : Ioo a b)
    simpa only [eta, extension, f, inclusion, projIcc_of_mem hab.le
      (Ioo_subset_Icc_self ht)] using h
  have hdensity : ∀ t ∈ Ioo a b,
      M08.referenceSpeedSq g eta t = M08.referenceSpeedSq g gamma t := by
    intro t ht
    apply referenceSpeedSq_congr_of_eventuallyEq g
    filter_upwards [isOpen_Ioo.mem_nhds ht] with r hr
    exact heq hr
  refine ⟨eta, heta, heq, hgamma.congr heq, ?_, ?_⟩
  · apply henergy.congr_uIoo
    intro t ht
    rw [uIoo_of_le hab.le] at ht
    exact (hdensity t ht).symm
  · exact intervalIntegral.integral_congr_Ioo_of_le hab.le hdensity

end PoincareConjecture.Proofs.M46
