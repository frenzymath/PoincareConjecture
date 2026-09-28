import PoincareConjecture.Definitions.M64Annulus
import PoincareConjecture.Statements.M63RampEstimates
import PoincareConjecture.Statements.M64Approximation
import PoincareConjecture.Statements.M64Annulus

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

def M64IntrinsicAnnulusComparison : Prop :=
  ∀ delta r K : ℝ, 0 < delta → delta < 1 / 100 → 0 < r →
    ∃ mu : ℝ, 0 < mu ∧ ∀ N : IntrinsicAnnulus,
      N.GaussianCurvatureBound K →
      r < intrinsicBoundaryLength N.metric 1 0 rampPeriod →
      N.SmallBoundaryTurning delta r →
      intrinsicAnnulusArea N.metric < mu →
        (3 / 4 : ℝ) * intrinsicBoundaryLength N.metric 1 0 rampPeriod ≤
          intrinsicBoundaryLength N.metric 2 0 rampPeriod

section Ramps

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Set.Icc a b)}

def M64RampSmallAnnulusComparison (G : M63AmbientGeometry F) : Prop :=
  3 ≤ n → ∀ r : ℝ, 0 < r → ∃ mu : ℝ, 0 < mu ∧
    ∀ circumference (h : 0 < circumference),
      let P := G.product circumference h
      ∀ t ∈ Set.Icc a b, ∀ gamma0 gamma1 : ℝ → P.charts.Point,
        Function.Periodic gamma0 curvePeriod →
        Function.Periodic gamma1 curvePeriod →
        ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) 2 gamma0 →
        ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) 2 gamma1 →
        M63IsRampAt P gamma0 t → M63IsRampAt P gamma1 t →
        r ≤ m62Length P.flow (fun x _ => gamma0 x) t →
        (∀ alpha beta : ℝ, alpha ≤ beta → beta ≤ alpha + curvePeriod →
          m63ArcLength P.flow (fun x _ => gamma0 x) t alpha beta ≤ r →
            m63ArcTotalCurvature P.flow (fun x _ => gamma0 x) t alpha beta <
              (1 / 200 : ℝ)) →
        ∀ A : M64Annulus (P.flow.metric t) gamma0 gamma1, A.area < mu →
          (3 / 4 : ℝ) * m62Length P.flow (fun x _ => gamma0 x) t ≤
            m62Length P.flow (fun x _ => gamma1 x) t

end Ramps

section Families

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {a b : ℝ} {F : RicciFlow 3 M (Set.Icc a b)}

structure M64FamilyAnnulusNet (G : M63AmbientGeometry F)
    (Gamma : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M)))
    (mu : ℝ) where
  node_count : ℕ
  nodes : Fin node_count → LoopTwoSphere
  circumference_cutoff : ℝ
  cutoff_positive : 0 < circumference_cutoff
  covers : ∀ z : LoopTwoSphere, ∃ i : Fin node_count,
    ∀ circumference (h : 0 < circumference), circumference < circumference_cutoff →
      ∃ A : M64Annulus ((G.product circumference h).flow.metric a)
        (m63CanonicalRamp (G.product circumference h) (periodicFreeLoop (Gamma z)))
        (m63CanonicalRamp (G.product circumference h)
          (periodicFreeLoop (Gamma (nodes i)))), A.area < mu

def M64FamilyAnnulusNets (G : M63AmbientGeometry F) : Prop :=
  ∀ Gamma : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M)),
    ∀ mu : ℝ, 0 < mu → Nonempty (M64FamilyAnnulusNet G Gamma mu)

end Families

structure M64FlowConclusion {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {a b : ℝ} (F : RicciFlow n M (Set.Icc a b)) where
  geometry : M63AmbientGeometry F
  evolution : M64AnnulusEvolution geometry
  ramp_comparison : M64RampSmallAnnulusComparison geometry
  projection : ∀ circumference (h : 0 < circumference), ∀ t ∈ Set.Icc a b,
    M64AnnulusProjection (geometry.product circumference h) t

structure M64ThreeDimensionalFlowConclusion {M : Type u} [TopologicalSpace M]
    [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
    {a b : ℝ} (F : RicciFlow 3 M (Set.Icc a b)) where
  flow : M64FlowConclusion F
  approximation : M64FamilyApproximationTheory F flow.geometry
  disks : ∀ circumference (h : 0 < circumference), ∀ t ∈ Set.Icc a b,
    M64DiskAreaComparison (flow.geometry.product circumference h) t
  finite_nets : M64FamilyAnnulusNets flow.geometry

def M64ComparisonTheory : Prop :=
  M64IntrinsicAnnulusComparison ∧
  (∀ (M : Type u) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g),
      IsCompact (Set.univ : Set M) → M64StaticApproximationTheory g D) ∧
  (∀ (n : ℕ) (M : Type u) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (a b : ℝ) (F : RicciFlow n M (Set.Icc a b)),
      3 ≤ n → IsCompact (Set.univ : Set M) → Nonempty (M64FlowConclusion F)) ∧
  (∀ (M : Type u) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
    (a b : ℝ) (F : RicciFlow 3 M (Set.Icc a b)),
      IsCompact (Set.univ : Set M) → Nonempty (M64ThreeDimensionalFlowConclusion F))

end PoincareConjecture
