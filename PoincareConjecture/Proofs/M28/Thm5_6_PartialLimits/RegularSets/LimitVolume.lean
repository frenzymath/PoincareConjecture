import PoincareConjecture.Proofs.M28.Generalized.MetricVolumeLipschitz
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.RegularSets.EmbeddingInverse
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.RegularSets.RelativeCompactMetric
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.Geometry.InverseOpenDistance

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology NNReal ENNReal

universe u

namespace PoincareConjecture.M28.RegularPointedMetricConvergence

variable {M : ℕ → Type u} [∀ k, TopologicalSpace (M k)]
  [∀ k, MeasurableSpace (M k)] [∀ k, BorelSpace (M k)]
  [∀ k, T2Space (M k)] [∀ k, T3Space (M k)]
  [∀ k, SecondCountableTopology (M k)]
  [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (M k)]
  [∀ k, IsManifold (𝓡 3) ∞ (M k)]
  {g : ∀ k, RiemannianMetric 3 (M k)} {p : ∀ k, M k}

theorem volumeMeasure_univ_le_of_source_bound
    (G : RegularPointedMetricConvergence g p) (V : ℝ≥0∞)
    (hV : ∀ k, (g k).volumeMeasure univ ≤ V) :
    letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.measurableSpace
    letI := G.limitCarrier.borelSpace
    letI := G.limitCarrier.t3Space
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    G.limitMetric.volumeMeasure univ ≤ 8 * V := by
  classical
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.measurableSpace
  let := G.limitCarrier.borelSpace
  let := G.limitCarrier.t3Space
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  have hmono : Monotone G.exhaustion := monotone_nat_of_le_succ
    (fun j => subset_closure.trans (G.exhaustion_step j))
  rw [← G.exhaustion_covers, hmono.measure_iUnion]
  apply iSup_le
  intro j
  obtain ⟨k, hcompare, hjk⟩ := ((G.eventually_compact_relative_inner_bounds
    (closure (G.exhaustion j)) (G.exhaustion_compactClosure j) 3 (by norm_num)).and
      (eventually_ge_atTop j)).exists
  let e := G.stageDiffeomorph k
  have hsource : G.exhaustion j ⊆ e.source := hmono hjk
  let U : TopologicalSpace.Opens (M (G.subsequence k)) :=
    ⟨e '' G.exhaustion j,
      e.toOpenPartialHomeomorph.isOpen_image_of_subset_source (G.exhaustion_open j) hsource⟩
  have hU : (U : Set (M (G.subsequence k))) ⊆ e.target := by
    rintro _ ⟨x, hx, rfl⟩
    exact e.toPartialEquiv.map_source (hsource hx)
  have hbound : ∀ y ∈ (U : Set (M (G.subsequence k))),
      ∀ v : TangentSpace (𝓡 3) (e.symm y),
        G.limitMetric.inner (e.symm y) v v ≤ (2 : ℝ) ^ 2 *
          (g (G.subsequence k)).inner (e (e.symm y))
            (mfderiv (𝓡 3) (𝓡 3) e (e.symm y) v)
            (mfderiv (𝓡 3) (𝓡 3) e (e.symm y) v) := by
    rintro _ ⟨x, hx, rfl⟩
    have hleft : e.symm (e x) = x := e.toPartialEquiv.left_inv (hsource hx)
    rw [hleft]
    intro v
    have hl := (hcompare x (subset_closure hx) v).1
    change G.limitMetric.inner x v v ≤ (2 : ℝ) ^ 2 *
      (g (G.subsequence k)).inner (G.embedding k x)
        (mfderiv (𝓡 3) (𝓡 3) (G.embedding k) x v)
        (mfderiv (𝓡 3) (𝓡 3) (G.embedding k) x v)
    norm_num at hl ⊢
    linarith only [hl]
  let f : U → G.limitCarrier.carrier := fun y => e.symm (y : M (G.subsequence k))
  have hdist : ∀ y z, G.limitMetric.edist (f y) (f z) ≤
      ((2 : ℝ≥0) : ℝ≥0∞) * (intrinsicOpenMetric (g (G.subsequence k)) U).edist y z := by
    intro y z
    simpa only [ENNReal.ofReal_ofNat, ENNReal.coe_ofNat] using
      inverse_edist_le_intrinsicOpenMetric G.limitMetric (g (G.subsequence k))
        e U hU (by norm_num : (0 : ℝ) < 2) hbound y z
  have himage : f '' univ = G.exhaustion j := by
    ext x
    constructor
    · rintro ⟨y, _, rfl⟩
      obtain ⟨z, hz, hzy⟩ := y.property
      change e.symm (y : M (G.subsequence k)) ∈ G.exhaustion j
      have hleft : e.symm (e z) = z := e.toPartialEquiv.left_inv (hsource hz)
      rw [← hzy, hleft]
      exact hz
    · intro hx
      refine ⟨⟨e x, ⟨x, hx, rfl⟩⟩, mem_univ _, ?_⟩
      exact e.toPartialEquiv.left_inv (hsource hx)
  have hv := volumeMeasure_image_le_of_edist_le
    (intrinsicOpenMetric (g (G.subsequence k)) U) G.limitMetric f 2 hdist univ
  rw [himage, intrinsicOpenMetric_volumeMeasure_univ] at hv
  norm_num at hv
  exact hv.trans (mul_le_mul_right ((measure_mono (subset_univ _)).trans
    (hV (G.subsequence k))) 8)

end PoincareConjecture.M28.RegularPointedMetricConvergence
