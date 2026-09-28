import PoincareConjecture.Proofs.M07.Geometry.Manifold.Gluing.Smooth
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Metric.Gluing.Compatibility
import PoincareConjecture.Proofs.M07.Topology.Gluing.Separation
import PoincareConjecture.Proofs.M07.Topology.Gluing.Connectedness

open Set Topology PoincareConjecture Bundle
open scoped ContDiff Manifold Topology

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Poincare.Gluing
universe u

variable {n : ℕ} {A : Type u}
variable (U : A → Set (EuclideanSpace ℝ (Fin n))) (hU : ∀ i, IsOpen (U i))
variable [∀ i, Nonempty (Piece U i)]

abbrev CanonicalMetric (i : A) :=
  letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U i) :=
    (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
  letI : IsManifold (𝓡 n) ∞ (Piece U i) :=
    (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton
  RiemannianMetric n (Piece U i)

def CompatibleMetrics (D : OverlapSystem (fun i => Piece U i))
    (g : ∀ i, CanonicalMetric U hU i) : Prop := by
  letI : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U i) :=
    fun i => (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
  letI : ∀ i, IsManifold (𝓡 n) ∞ (Piece U i) :=
    fun i => (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton
  exact ∀ i j (p : Piece U i), p ∈ (D.transition i j).source →
    ∀ a b : TangentSpace (𝓡 n) p,
      (g i).inner p a b = (g j).inner (D.transition i j p)
        (mfderiv (𝓡 n) (𝓡 n) (D.transition i j) p a)
        (mfderiv (𝓡 n) (𝓡 n) (D.transition i j) p b)

def quotientMetric
    (D : OverlapSystem (fun i => Piece U i))
    (hs : SmoothOverlap U hU D)
    (g : ∀ i, CanonicalMetric U hU i)
    (hg : CompatibleMetrics U hU D g) :
    letI := quotientChartedSpace U hU D
    letI := quotient_isManifold U hU D hs
    RiemannianMetric n (Quotient D.setoid) := by
  letI : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U i) :=
    fun i => (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
  letI : ∀ i, IsManifold (𝓡 n) ∞ (Piece U i) :=
    fun i => (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton
  letI := quotientChartedSpace U hU D
  letI := quotient_isManifold U hU D hs
  exact Classical.choose (D.exists_unique_metric_of_transition_invariance g
    (include_isLocalDiffeomorph U hU D hs) hs hg)

theorem quotientMetric_preserves
    (D : OverlapSystem (fun i => Piece U i))
    (hs : SmoothOverlap U hU D)
    (g : ∀ i, CanonicalMetric U hU i)
    (hg : CompatibleMetrics U hU D g) (i : A) :
    letI : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U i) :=
      fun i => (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI : ∀ i, IsManifold (𝓡 n) ∞ (Piece U i) :=
      fun i => (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton
    letI := quotientChartedSpace U hU D
    letI := quotient_isManifold U hU D hs
    ∀ (p : Piece U i) (a b : TangentSpace (𝓡 n) p),
      (g i).inner p a b =
        (quotientMetric U hU D hs g hg).inner (D.include i p)
          (mfderiv (𝓡 n) (𝓡 n) (D.include i) p a)
          (mfderiv (𝓡 n) (𝓡 n) (D.include i) p b) := by
  letI : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U i) :=
    fun i => (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
  letI : ∀ i, IsManifold (𝓡 n) ∞ (Piece U i) :=
    fun i => (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton
  letI := quotientChartedSpace U hU D
  letI := quotient_isManifold U hU D hs
  exact (Classical.choose_spec (D.exists_unique_metric_of_transition_invariance g
    (include_isLocalDiffeomorph U hU D hs) hs hg)).1 i

theorem riemannianManifold_from_compatibleCharts
    [Countable A] [Nonempty A]
    (D : OverlapSystem (fun i => Piece U i))
    (hs : SmoothOverlap U hU D)
    (hclosed : ∀ i j, IsClosed {p : Piece U i × Piece U j |
      D.Rel ⟨i, p.1⟩ ⟨j, p.2⟩})
    (g : ∀ i, CanonicalMetric U hU i)
    (hg : CompatibleMetrics U hU D g) :
    T2Space (Quotient D.setoid) ∧
    SecondCountableTopology (Quotient D.setoid) ∧
    Nonempty (Quotient D.setoid) ∧
    ∃ c : ChartedSpace (EuclideanSpace ℝ (Fin n)) (Quotient D.setoid),
      letI := c
      ∃ hM : IsManifold (𝓡 n) ∞ (Quotient D.setoid),
        letI := hM
        letI : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U i) :=
          fun i => (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
        letI : ∀ i, IsManifold (𝓡 n) ∞ (Piece U i) :=
          fun i => (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton
        (∀ i, Topology.IsOpenEmbedding (D.include i) ∧
          IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ (D.include i)) ∧
        (⋃ i, Set.range (D.include i)) = Set.univ ∧
        (∀ i j (x : Piece U i) (y : Piece U j),
          D.include i x = D.include j y ↔
            x ∈ (D.transition i j).source ∧ D.transition i j x = y) ∧
        (∀ i, ∃ e : OpenPartialHomeomorph (Quotient D.setoid)
            (EuclideanSpace ℝ (Fin n)),
          e ∈ atlas (EuclideanSpace ℝ (Fin n)) (Quotient D.setoid) ∧
          e.source = Set.range (D.include i) ∧ e.target = U i ∧
          ∀ x : Piece U i, e (D.include i x) = (x : EuclideanSpace ℝ (Fin n))) ∧
        ((∀ i, ConnectedSpace (Piece U i)) →
          (∃ i0, ∀ i, Relation.ReflTransGen
            (fun j k => (D.transition j k).source.Nonempty) i0 i) →
          ConnectedSpace (Quotient D.setoid)) ∧
        (∃! gQ : RiemannianMetric n (Quotient D.setoid),
          ∀ i (p : Piece U i) (a b : TangentSpace (𝓡 n) p),
            (g i).inner p a b = gQ.inner (D.include i p)
              (mfderiv (𝓡 n) (𝓡 n) (D.include i) p a)
              (mfderiv (𝓡 n) (𝓡 n) (D.include i) p b)) := by
  classical
  letI : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U i) :=
    fun i => (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
  letI : ∀ i, IsManifold (𝓡 n) ∞ (Piece U i) :=
    fun i => (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton
  letI := quotientChartedSpace U hU D
  letI := quotient_isManifold U hU D hs
  refine ⟨D.quotient_t2Space hclosed, D.quotient_secondCountableTopology,
    ?_, quotientChartedSpace U hU D, quotient_isManifold U hU D hs,
    ?_, D.include_cover, D.include_eq_iff, ?_, ?_, ?_⟩
  · let i : A := Classical.choice inferInstance
    exact ⟨D.include i (Classical.choice inferInstance)⟩
  · intro i
    exact ⟨D.include_isOpenEmbedding i, include_isLocalDiffeomorph U hU D hs i⟩
  · intro i
    refine ⟨quotientChart U hU D i, ⟨i, rfl⟩, ?_, quotientChart_target U hU D i,
      quotientChart_apply U hU D i⟩
    simpa only [Set.image_univ] using quotientChart_source U hU D i
  · intro hconn hreach
    obtain ⟨i0, hi0⟩ := hreach
    letI : ∀ i, ConnectedSpace (Piece U i) := hconn
    exact D.quotient_connectedSpace i0 hi0
  · exact D.exists_unique_metric_of_transition_invariance g
      (include_isLocalDiffeomorph U hU D hs) hs hg

end Poincare.Gluing
