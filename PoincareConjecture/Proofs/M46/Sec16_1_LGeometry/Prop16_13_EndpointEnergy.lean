import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Conjugate.Energy.Length
import PoincareConjecture.Proofs.M08.ReferenceEnergy

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology ENNReal Bundle

universe u

namespace PoincareConjecture.Proofs.M46

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M] [T3Space M]

theorem edist_le_energy_of_interior_regular (g : RiemannianMetric n M)
    {gamma : ℝ → M} {a b C : ℝ} (hab : a < b) (hC : 0 < C)
    (hgamma : ContinuousOn gamma (Icc a b))
    (hregular : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) 1 gamma (Ioo a b))
    (henergy : IntervalIntegrable (M08.referenceSpeedSq g gamma) volume a b) :
    g.edist (gamma a) (gamma b) ≤ ENNReal.ofReal
      (((∫ t in a..b, M08.referenceSpeedSq g gamma t) + (b - a) * C ^ 2) / (2 * C)) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  let bound :=
    ((∫ t in a..b, M08.referenceSpeedSq g gamma t) + (b - a) * C ^ 2) / (2 * C)
  have hordered (s t : ℝ) (hs : s ∈ Ioo a b) (ht : t ∈ Ioo a b) (hst : s ≤ t) :
      g.edist (gamma s) (gamma t) ≤ ENNReal.ofReal bound := by
    have hsub : Icc s t ⊆ Ioo a b := Icc_subset_Ioo hs.1 ht.2
    have hspeed : ContinuousOn (fun r =>
        g.tangentNorm (gamma r) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) gamma r 1)) (Icc s t) :=
      Real.continuous_sqrt.comp_continuousOn
        ((M08.referenceSpeedSq_continuousOn g isOpen_Ioo hregular).mono hsub)
    have hlength := g.edist_le_ofReal_energy_bound hst hC (hregular.mono hsub) hspeed
    have hsq (r : ℝ) :
        (g.tangentNorm (gamma r) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) gamma r 1)) ^ 2 =
          M08.referenceSpeedSq g gamma r :=
      Real.sq_sqrt (M08.referenceSpeedSq_nonneg g gamma r)
    simp only [hsq] at hlength
    apply hlength.trans (ENNReal.ofReal_le_ofReal ?_)
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply add_le_add
    · exact intervalIntegral.integral_mono_interval hs.1.le hst ht.2.le
        (ae_of_all _ (M08.referenceSpeedSq_nonneg g gamma)) henergy
    · exact mul_le_mul_of_nonneg_right (by linarith [hs.1, ht.2]) (sq_nonneg C)
  have hopen (s : ℝ) (hs : s ∈ Ioo a b) (t : ℝ) (ht : t ∈ Ioo a b) :
      edist (gamma s) (gamma t) ≤ ENNReal.ofReal bound := by
    rcases le_total s t with hst | hts
    · exact hordered s t hs ht hst
    · rw [edist_comm]
      exact hordered t s ht hs hts
  have hleft (s : ℝ) (hs : s ∈ Icc a b) (t : ℝ) (ht : t ∈ Ioo a b) :
      edist (gamma s) (gamma t) ≤ ENNReal.ofReal bound := by
    apply le_on_closure (fun r hr => hopen r hr t ht)
    · simpa only [closure_Ioo hab.ne, Function.comp_def] using
        continuous_edist.comp_continuousOn (hgamma.prodMk continuousOn_const)
    · exact continuousOn_const
    · simpa only [closure_Ioo hab.ne] using hs
  change edist (gamma a) (gamma b) ≤ ENNReal.ofReal bound
  apply le_on_closure (fun r hr => hleft a ⟨le_rfl, hab.le⟩ r hr)
  · simpa only [closure_Ioo hab.ne, Function.comp_def] using
      continuous_edist.comp_continuousOn (continuousOn_const.prodMk hgamma)
  · exact continuousOn_const
  · simp only [closure_Ioo hab.ne, mem_Icc, le_refl, and_true]
    exact hab.le

theorem sq_distance_le_duration_mul_energy (g : RiemannianMetric n M)
    {gamma : ℝ → M} {a b d : ℝ} (hab : a < b) (hd : 0 < d)
    (hgamma : ContinuousOn gamma (Icc a b))
    (hregular : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) 1 gamma (Ioo a b))
    (henergy : IntervalIntegrable (M08.referenceSpeedSq g gamma) volume a b)
    (hdistance : ENNReal.ofReal d ≤ g.edist (gamma a) (gamma b)) :
    d ^ 2 ≤ (b - a) * ∫ t in a..b, M08.referenceSpeedSq g gamma t := by
  have hduration : 0 < b - a := sub_pos.mpr hab
  have hE : 0 ≤ ∫ t in a..b, M08.referenceSpeedSq g gamma t :=
    intervalIntegral.integral_nonneg hab.le (fun t _ => M08.referenceSpeedSq_nonneg g gamma t)
  have hC : 0 < d / (b - a) := div_pos hd hduration
  have hbound := hdistance.trans
    (edist_le_energy_of_interior_regular g hab hC hgamma hregular henergy)
  have hreal := (ENNReal.ofReal_le_ofReal_iff (by positivity :
    0 ≤ ((∫ t in a..b, M08.referenceSpeedSq g gamma t) +
      (b - a) * (d / (b - a)) ^ 2) / (2 * (d / (b - a))))).mp hbound
  have h := (le_div_iff₀ (by positivity : 0 < 2 * (d / (b - a)))).mp hreal
  have hm := mul_le_mul_of_nonneg_left h hduration.le
  field_simp [hduration.ne'] at hm
  nlinarith

end PoincareConjecture.Proofs.M46
