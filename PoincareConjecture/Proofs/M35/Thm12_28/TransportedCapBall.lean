import PoincareConjecture.Proofs.M35.Thm12_28.TransportedBall
import PoincareConjecture.Proofs.M35.Thm12_28.CylinderCoordinates
import PoincareConjecture.Proofs.M35.Thm12_28.CapCompactness

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.M35.OrdinaryRealization

private def restrictCoordinates {M N : Type*}
    [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
    (phi : PartialDiffeomorph (𝓡 3) (𝓡 3) M N ∞)
    (V : Set M) (hV : IsOpen V) : PartialDiffeomorph (𝓡 3) (𝓡 3) M N ∞ where
  toPartialEquiv := phi.toPartialEquiv.restr V
  open_source := phi.open_source.inter hV
  open_target := (phi.toOpenPartialHomeomorph.restrOpen V hV).open_target
  contMDiffOn_toFun := phi.contMDiffOn_toFun.mono inter_subset_left
  contMDiffOn_invFun := phi.contMDiffOn_invFun.mono inter_subset_left

theorem blowupSequence_ball_retention (P : M35StandardCapPredecessors)
    {g₀ : StandardInitialMetric} (E : RepairedStandardCapExistenceData g₀)
    (t : ℕ → ℝ) (x : ℕ → StandardCapSpace)
    (ht : ∀ k, t k ∈ Ico 0 E.flow.base.lifetime)
    (hR : Tendsto (fun k => (E.flow.connection (t k)).scalarCurvature (x k)) atTop atTop)
    (L : GeneralizedBlowupConvergence (blowupSequence P E t x ht hR)
      (blowupBackwardInterval ⊤))
    (j : ℕ) (K : Set L.limit.sliceCarrier.carrier) (hK : IsCompact K)
    (hKU : K ⊆ L.exhaustion.space j) {eta : ℝ} (heta : 0 < eta) (heta1 : eta < 1) :
    letI : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) L.limit.carrier.carrier :=
      L.limit.carrier.chartedSpace
    letI : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
    letI : T3Space L.limit.carrier.carrier := L.limit.carrier.t3Space
    ∃ k₀ : ℕ, j ≤ k₀ ∧ ∀ k ≥ k₀,
      let f : L.limit.sliceCarrier.carrier → StandardCapSpace :=
        fun z => ((L.embedding k).forward 0
          ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩ z).val
      ∀ y : L.limit.carrier.carrier, ∀ r : ℝ, 0 < r →
        closure ((L.limit.flow.metric 0).ball y r) ⊆ interior K →
        (E.flow.metric (t (L.subsequence k))).ball (f y)
          (r / Real.sqrt ((blowupSequence P E t x ht hR).scale (L.subsequence k) /
            (1 - eta))) ⊆ f '' (L.limit.flow.metric 0).ball y r := by
  let : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin 3)) L.limit.carrier.carrier :=
    L.limit.carrier.chartedSpace
  have : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
  have : T3Space L.limit.carrier.carrier := L.limit.carrier.t3Space
  obtain ⟨k₀, hjk₀, hcompare⟩ := blowupSequence_compact_metric_comparison
    P E t x ht hR L j K hK hKU eta heta
  refine ⟨k₀, hjk₀, ?_⟩
  intro k hk
  let Q := (blowupSequence P E t x ht hR).scale (L.subsequence k)
  have hQ : 0 < Q := (L.embedding k).scale_pos
  have he : 0 < 1 - eta := sub_pos.mpr heta1
  have hA : 0 < Real.sqrt (Q / (1 - eta)) := Real.sqrt_pos.mpr (div_pos hQ he)
  have hzero : (0 : ℝ) ∈ Icc (-L.exhaustion.time k) 0 :=
    ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩
  have htime := ((L.embedding k).forward 0 hzero L.limit.base).property
  let phi := cylinderSpatialCoordinates E.flow.base.flow (L.embedding k)
    (L.exhaustion.space_open k) 0 hzero htime
  let psi := restrictCoordinates phi (interior K) isOpen_interior
  intro f y r hr hball
  have hcompact : IsCompact (closure ((L.limit.flow.metric 0).ball y r)) :=
    hK.of_isClosed_subset isClosed_closure (hball.trans interior_subset)
  apply ball_subset_image_of_tangentNorm_lower (L.limit.flow.metric 0)
    (E.flow.metric (t (L.subsequence k))) psi hA hr y hcompact
  · intro z hz
    exact ⟨L.exhaustion.space_increasing (hjk₀.trans hk)
      (hKU (interior_subset (hball hz))), hball hz⟩
  · intro z hz v
    have hzK : z ∈ K := interior_subset hz.2
    have h := (abs_le.mp (hcompare k hk z hzK v)).1
    change -(eta * (L.limit.flow.metric 0).inner z v v) ≤
      Q * (E.flow.metric (t (L.subsequence k))).inner (psi z)
        (mfderiv (𝓡 3) (𝓡 3) psi z v) (mfderiv (𝓡 3) (𝓡 3) psi z v) -
          (L.limit.flow.metric 0).inner z v v at h
    have hquad : (L.limit.flow.metric 0).inner z v v ≤ Q / (1 - eta) *
        (E.flow.metric (t (L.subsequence k))).inner (psi z)
          (mfderiv (𝓡 3) (𝓡 3) psi z v) (mfderiv (𝓡 3) (𝓡 3) psi z v) := by
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ he).mpr
      nlinarith
    exact (Real.sqrt_le_sqrt hquad).trans_eq (Real.sqrt_mul (div_nonneg hQ.le he.le) _)

theorem blowupSequence_cap_core_ball_retention (P : M35StandardCapPredecessors)
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
    letI : T2Space L.limit.carrier.carrier := L.limit.carrier.t2Space
    letI : T3Space L.limit.carrier.carrier := L.limit.carrier.t3Space
    ∀ N : CapCertificate (L.limit.flow.metric 0), IsCompact (closure N.carrier) →
      closure N.carrier ⊆ L.exhaustion.space j →
      ∃ k₀ : ℕ, j ≤ k₀ ∧ ∀ k ≥ k₀,
        let f : L.limit.sliceCarrier.carrier → StandardCapSpace :=
          fun z => ((L.embedding k).forward 0
            ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩ z).val
        ∀ y ∈ N.core, (E.flow.metric (t (L.subsequence k))).ball (f y)
          (N.core_radius y / Real.sqrt
            ((blowupSequence P E t x ht hR).scale (L.subsequence k) / (1 - eta))) ⊆
              f '' N.carrier := by
  let : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
  let : MeasurableSpace L.limit.carrier.carrier := L.limit.carrier.measurableSpace
  have : BorelSpace L.limit.carrier.carrier := L.limit.carrier.borelSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin 3)) L.limit.carrier.carrier :=
    L.limit.carrier.chartedSpace
  have : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
  have : T2Space L.limit.carrier.carrier := L.limit.carrier.t2Space
  have : T3Space L.limit.carrier.carrier := L.limit.carrier.t3Space
  intro N hcompact hU
  obtain ⟨k₀, hjk₀, hball⟩ := blowupSequence_ball_retention
    P E t x ht hR L j (closure N.carrier) hcompact hU heta heta1
  refine ⟨k₀, hjk₀, ?_⟩
  intro k hk f y hy
  have hinside : N.carrier ⊆ interior (closure N.carrier) :=
    N.carrier_open.subset_interior_iff.mpr subset_closure
  exact (hball k hk y (N.core_radius y) (N.core_radius_pos y hy)
    ((N.core_ball_subset y hy).trans hinside)).trans
      (image_mono (subset_closure.trans (N.core_ball_subset y hy)))

end PoincareConjecture.M35.OrdinaryRealization
