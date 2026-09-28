import PoincareConjecture.Proofs.M35.Thm12_28.TransportedVolume
import PoincareConjecture.Proofs.M35.Thm12_28.CylinderCoordinates









set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.M35.OrdinaryRealization



theorem blowupSequence_volume_comparison (P : M35StandardCapPredecessors)
    {g₀ : StandardInitialMetric} (E : RepairedStandardCapExistenceData g₀)
    (t : ℕ → ℝ) (x : ℕ → StandardCapSpace)
    (ht : ∀ k, t k ∈ Ico 0 E.flow.base.lifetime)
    (hR : Tendsto (fun k => (E.flow.connection (t k)).scalarCurvature (x k)) atTop atTop)
    (L : GeneralizedBlowupConvergence (blowupSequence P E t x ht hR)
      (blowupBackwardInterval ⊤)) (j : ℕ)
    (U : Set L.limit.sliceCarrier.carrier) (hU : IsOpen U) (hcompact : IsCompact (closure U))
    (hUj : closure U ⊆ L.exhaustion.space j) {eta : ℝ} (heta : 0 < eta) (heta1 : eta < 1) :
    letI : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
    letI : MeasurableSpace L.limit.carrier.carrier := L.limit.carrier.measurableSpace
    letI : BorelSpace L.limit.carrier.carrier := L.limit.carrier.borelSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) L.limit.carrier.carrier :=
      L.limit.carrier.chartedSpace
    letI : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
    letI : T3Space L.limit.carrier.carrier := L.limit.carrier.t3Space
    letI : SecondCountableTopology L.limit.carrier.carrier :=
      L.limit.carrier.secondCountable
    ∃ k₀ : ℕ, j ≤ k₀ ∧ ∀ k ≥ k₀,
      let f : L.limit.sliceCarrier.carrier → StandardCapSpace :=
        fun z => ((L.embedding k).forward 0
          ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩ z).val
      let Q := (blowupSequence P E t x ht hR).scale (L.subsequence k)
      ∀ A : Set L.limit.carrier.carrier, IsOpen A → A ⊆ U →
        calibratedMetricVolume (E.flow.metric (t (L.subsequence k))) (f '' A) ≤
          ENNReal.ofReal (Real.sqrt ((1 + eta) / Q) ^ 3) *
            calibratedMetricVolume (L.limit.flow.metric 0) A ∧
        calibratedMetricVolume (L.limit.flow.metric 0) A ≤
          ENNReal.ofReal (Real.sqrt (Q / (1 - eta)) ^ 3) *
            calibratedMetricVolume (E.flow.metric (t (L.subsequence k))) (f '' A) := by
  let : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
  let : MeasurableSpace L.limit.carrier.carrier := L.limit.carrier.measurableSpace
  have : BorelSpace L.limit.carrier.carrier := L.limit.carrier.borelSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin 3)) L.limit.carrier.carrier :=
    L.limit.carrier.chartedSpace
  have : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
  have : T3Space L.limit.carrier.carrier := L.limit.carrier.t3Space
  have : SecondCountableTopology L.limit.carrier.carrier := L.limit.carrier.secondCountable
  obtain ⟨k₀, hjk₀, hcompare⟩ := blowupSequence_compact_metric_comparison
    P E t x ht hR L j (closure U) hcompact hUj eta heta
  refine ⟨k₀, hjk₀, ?_⟩
  intro k hk f Q A hA hAU
  have hQ : 0 < Q := (L.embedding k).scale_pos
  have he : 0 < 1 - eta := sub_pos.mpr heta1
  have hzero : (0 : ℝ) ∈ Icc (-L.exhaustion.time k) 0 :=
    ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩
  have htime := ((L.embedding k).forward 0 hzero L.limit.base).property
  let phi := cylinderSpatialCoordinates E.flow.base.flow (L.embedding k)
    (L.exhaustion.space_open k) 0 hzero htime
  have hsource : U ⊆ phi.source := fun _ hz =>
    L.exhaustion.space_increasing (hjk₀.trans hk) (hUj (subset_closure hz))
  constructor
  · apply calibratedVolume_image_le_of_tangentNorm_le (L.limit.flow.metric 0)
      (E.flow.metric (t (L.subsequence k))) phi hU hsource (Real.sqrt_nonneg _)
      _ hA.measurableSet hAU
    intro z hz v
    apply tangentNorm_pullback_le_of_quadratic_le (L.limit.flow.metric 0)
      (E.flow.metric (t (L.subsequence k))) phi z v hQ (by positivity)
    have h := (abs_le.mp (hcompare k hk z (subset_closure hz) v)).2
    change Q * (E.flow.metric (t (L.subsequence k))).inner (phi z)
      (mfderiv (𝓡 3) (𝓡 3) phi z v) (mfderiv (𝓡 3) (𝓡 3) phi z v) -
        (L.limit.flow.metric 0).inner z v v ≤ eta * (L.limit.flow.metric 0).inner z v v at h
    exact (sub_le_iff_le_add.mp h).trans_eq (by
      simpa only [add_mul, one_mul] using
        add_comm (eta * (L.limit.flow.metric 0).inner z v v)
          ((L.limit.flow.metric 0).inner z v v))
  · apply calibratedVolume_le_image_of_tangentNorm_lower (L.limit.flow.metric 0)
      (E.flow.metric (t (L.subsequence k))) phi hU hsource (Real.sqrt_nonneg _)
      _ hA hAU
    intro z hz v
    have h := (abs_le.mp (hcompare k hk z (subset_closure hz) v)).1
    change -(eta * (L.limit.flow.metric 0).inner z v v) ≤
      Q * (E.flow.metric (t (L.subsequence k))).inner (phi z)
        (mfderiv (𝓡 3) (𝓡 3) phi z v) (mfderiv (𝓡 3) (𝓡 3) phi z v) -
          (L.limit.flow.metric 0).inner z v v at h
    have hquad : (L.limit.flow.metric 0).inner z v v ≤ Q / (1 - eta) *
        (E.flow.metric (t (L.subsequence k))).inner (phi z)
          (mfderiv (𝓡 3) (𝓡 3) phi z v) (mfderiv (𝓡 3) (𝓡 3) phi z v) := by
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ he).mpr
      nlinarith
    exact (Real.sqrt_le_sqrt hquad).trans_eq (Real.sqrt_mul (div_nonneg hQ.le he.le) _)



theorem blowupSequence_cap_volume_bound (P : M35StandardCapPredecessors)
    {g₀ : StandardInitialMetric} (E : RepairedStandardCapExistenceData g₀)
    (t : ℕ → ℝ) (x : ℕ → StandardCapSpace)
    (ht : ∀ k, t k ∈ Ico 0 E.flow.base.lifetime)
    (hR : Tendsto (fun k => (E.flow.connection (t k)).scalarCurvature (x k)) atTop atTop)
    (L : GeneralizedBlowupConvergence (blowupSequence P E t x ht hR)
      (blowupBackwardInterval ⊤)) (j : ℕ) {eta : ℝ} (heta : 0 < eta) (heta1 : eta < 1) :
    letI : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
    letI : MeasurableSpace L.limit.carrier.carrier := L.limit.carrier.measurableSpace
    letI : BorelSpace L.limit.carrier.carrier := L.limit.carrier.borelSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) L.limit.carrier.carrier :=
      L.limit.carrier.chartedSpace
    letI : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
    letI : T3Space L.limit.carrier.carrier := L.limit.carrier.t3Space
    ∀ N : CapCertificate (L.limit.flow.metric 0), IsCompact (closure N.carrier) →
      closure N.carrier ⊆ L.exhaustion.space j →
      ∃ k₀ : ℕ, j ≤ k₀ ∧ ∀ k ≥ k₀,
        let f : L.limit.sliceCarrier.carrier → StandardCapSpace :=
          fun z => ((L.embedding k).forward 0
            ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩ z).val
        let Q := (blowupSequence P E t x ht hR).scale (L.subsequence k)
        calibratedMetricVolume (E.flow.metric (t (L.subsequence k))) (f '' N.carrier) <
          ENNReal.ofReal (Real.sqrt ((1 + eta) / Q) ^ 3) *
            (ENNReal.ofReal N.cap_constant *
              ENNReal.ofReal (scalarCurvatureSupOn (L.limit.flow.metric 0)
                N.connection N.carrier ^ (-3 / 2 : ℝ))) := by
  let : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
  let : MeasurableSpace L.limit.carrier.carrier := L.limit.carrier.measurableSpace
  have : BorelSpace L.limit.carrier.carrier := L.limit.carrier.borelSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin 3)) L.limit.carrier.carrier :=
    L.limit.carrier.chartedSpace
  have : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
  have : T3Space L.limit.carrier.carrier := L.limit.carrier.t3Space
  intro N hcompact hU
  obtain ⟨k₀, hjk₀, hvolume⟩ := blowupSequence_volume_comparison
    P E t x ht hR L j N.carrier N.carrier_open hcompact hU heta heta1
  refine ⟨k₀, hjk₀, ?_⟩
  intro k hk f Q
  have hQ : 0 < Q := (L.embedding k).scale_pos
  have hC : 0 < Real.sqrt ((1 + eta) / Q) ^ 3 :=
    pow_pos (Real.sqrt_pos.mpr (div_pos (by positivity) hQ)) 3
  exact (hvolume k hk N.carrier N.carrier_open Subset.rfl).1.trans_lt
    (ENNReal.mul_lt_mul_right (ENNReal.ofReal_pos.mpr hC).ne'
      ENNReal.ofReal_ne_top N.volume_bound)

end PoincareConjecture.M35.OrdinaryRealization
