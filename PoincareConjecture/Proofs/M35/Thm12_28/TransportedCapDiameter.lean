import PoincareConjecture.Proofs.M35.Thm12_28.TransportedCapDistance









set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.M35.OrdinaryRealization




theorem blowupSequence_cap_diameter_bound (P : M35StandardCapPredecessors)
    {g₀ : StandardInitialMetric} (E : RepairedStandardCapExistenceData g₀)
    (t : ℕ → ℝ) (x : ℕ → StandardCapSpace)
    (ht : ∀ k, t k ∈ Ico 0 E.flow.base.lifetime)
    (hR : Tendsto (fun k => (E.flow.connection (t k)).scalarCurvature (x k)) atTop atTop)
    (L : GeneralizedBlowupConvergence (blowupSequence P E t x ht hR)
      (blowupBackwardInterval ⊤)) (j : ℕ) (eta : ℝ) (heta : 0 < eta) :
    letI : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
    letI : MeasurableSpace L.limit.carrier.carrier := L.limit.carrier.measurableSpace
    letI : BorelSpace L.limit.carrier.carrier := L.limit.carrier.borelSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) L.limit.carrier.carrier :=
      L.limit.carrier.chartedSpace
    letI : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
    letI : T2Space L.limit.carrier.carrier := L.limit.carrier.t2Space
    letI : T3Space L.limit.carrier.carrier := L.limit.carrier.t3Space
    ∀ N : CapCertificate (L.limit.flow.metric 0), IsCompact (closure N.carrier) →
      closure N.carrier ⊆ L.exhaustion.space j →
      ∃ k₀ : ℕ, j ≤ k₀ ∧ ∀ k ≥ k₀,
        let f : L.limit.sliceCarrier.carrier → StandardCapSpace :=
          fun z => ((L.embedding k).forward 0
            ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩ z).val
        intrinsicDiameter (E.flow.metric (t (L.subsequence k))) (f '' N.carrier) <
          ENNReal.ofReal (Real.sqrt ((1 + eta) /
            (blowupSequence P E t x ht hR).scale (L.subsequence k)) *
              (N.cap_constant * scalarCurvatureSupOn (L.limit.flow.metric 0)
                N.connection N.carrier ^ (-1 / 2 : ℝ))) := by
  let : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
  let : MeasurableSpace L.limit.carrier.carrier := L.limit.carrier.measurableSpace
  have : BorelSpace L.limit.carrier.carrier := L.limit.carrier.borelSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin 3)) L.limit.carrier.carrier :=
    L.limit.carrier.chartedSpace
  have : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
  have : T2Space L.limit.carrier.carrier := L.limit.carrier.t2Space
  have : T3Space L.limit.carrier.carrier := L.limit.carrier.t3Space
  intro N hcompact hU
  obtain ⟨k₀, hjk₀, hcompare⟩ := blowupSequence_compact_metric_comparison
    P E t x ht hR L j (closure N.carrier) hcompact hU eta heta
  refine ⟨k₀, hjk₀, ?_⟩
  intro k hk
  let Q := (blowupSequence P E t x ht hR).scale (L.subsequence k)
  have hQ : 0 < Q := (L.embedding k).scale_pos
  let f : L.limit.sliceCarrier.carrier → StandardCapSpace :=
    fun z => ((L.embedding k).forward 0
      ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩ z).val
  have hzero : (0 : ℝ) ∈ Icc (-L.exhaustion.time k) 0 :=
    ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩
  have htime := ((L.embedding k).forward 0 hzero L.limit.base).property
  have hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f N.carrier :=
    ((sliceDiffeomorph htime).contMDiff.comp_contMDiffOn
      ((L.embedding k).forward_smooth 0 hzero)).mono
        (fun _ hy => L.exhaustion.space_increasing (hjk₀.trans hk) (hU (subset_closure hy)))
  have hA : 0 < 1 + eta := by positivity
  have hC : 0 < Real.sqrt ((1 + eta) / Q) := Real.sqrt_pos.mpr (div_pos hA hQ)
  have hspeed (y : L.limit.sliceCarrier.carrier) (hy : y ∈ N.carrier)
      (v : TangentSpace (𝓡 3) y) :
      (E.flow.metric (t (L.subsequence k))).tangentNorm (f y)
        (mfderiv (𝓡 3) (𝓡 3) f y v) ≤
          Real.sqrt ((1 + eta) / Q) * (L.limit.flow.metric 0).tangentNorm y v := by
    apply tangentNorm_pullback_le_of_quadratic_le (L.limit.flow.metric 0)
      (E.flow.metric (t (L.subsequence k))) f y v hQ hA.le
    have h := (abs_le.mp (hcompare k hk y (subset_closure hy) v)).2
    change Q * (E.flow.metric (t (L.subsequence k))).inner (f y)
      (mfderiv (𝓡 3) (𝓡 3) f y v) (mfderiv (𝓡 3) (𝓡 3) f y v) -
        (L.limit.flow.metric 0).inner y v v ≤ eta * (L.limit.flow.metric 0).inner y v v at h
    exact (sub_le_iff_le_add.mp h).trans_eq (by
      simpa only [add_mul, one_mul] using
        add_comm (eta * (L.limit.flow.metric 0).inner y v v)
          ((L.limit.flow.metric 0).inner y v v))
  have hdiam := intrinsicDiameter_image_le (L.limit.flow.metric 0)
    (E.flow.metric (t (L.subsequence k))) f N.carrier_open hf hC hspeed
  have hstrict := ENNReal.mul_lt_mul_right
    (ENNReal.ofReal_pos.mpr hC).ne' ENNReal.ofReal_ne_top N.intrinsic_diameter_bound
  exact (hdiam.trans_lt hstrict).trans_eq (ENNReal.ofReal_mul hC.le).symm

end PoincareConjecture.M35.OrdinaryRealization
