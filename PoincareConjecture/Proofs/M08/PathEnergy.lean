import PoincareConjecture.Proofs.M08.SquareEnergy
import PoincareConjecture.Proofs.M08.MetricCompactness
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Topology.MetricSpace.Equicontinuity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle intervalIntegral Topology ENNReal
open MeasureTheory Set Filter

universe u

namespace PoincareConjecture.M08

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [ConnectedSpace M] [T3Space M]

noncomputable abbrev referenceMetricSpace (g : RiemannianMetric n M) : MetricSpace M :=
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  EMetricSpace.toMetricSpace (finiteEdistMetric g)

theorem referenceMetricSpace_complete (g : RiemannianMetric n M)
    (hg : MetricComplete g) :
    letI : MetricSpace M := referenceMetricSpace g
    CompleteSpace M := by
  exact hg

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

theorem dist_le_sqrt_energy (g : RiemannianMetric n M) {α : ℝ → M}
    {a b C : ℝ} (hab : a < b) (hα : ContinuousOn α (Icc a b))
    (hreg : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) 1 α (Ioo a b))
    (hE : IntervalIntegrable (referenceSpeedSq g α) volume a b)
    (hbound : (∫ r in a..b, referenceSpeedSq g α r) ≤ C) :
    letI : MetricSpace M := referenceMetricSpace g
    ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      dist (α s) (α t) ≤ Real.sqrt C * Real.sqrt |t - s| := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  letI : MetricSpace M := EMetricSpace.toMetricSpace (finiteEdistMetric g)
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

end PoincareConjecture.M08
