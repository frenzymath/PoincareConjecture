import PoincareLib.Geometry.CurveShortening.Comparison.Annulus
import PoincareLib.Geometry.CurveShortening.Ramp.Estimates
import PoincareLib.Geometry.CurveShortening.Comparison.ApproximationTheory
import PoincareLib.Geometry.CurveShortening.Comparison.AnnulusTheory

/-!
# M64 intrinsic comparison, ramp comparison and finite annulus nets

These statements retain the actual metric, parameter subarcs and chosen
quotient circle products. Ramps have arbitrary positive winding degree.
The finite-net construction uses raw continuous C1 families and chooses
one node for a member before quantifying the circle circumference.

Sources: Morgan--Tian Proposition 19.35, pp. 467-481; Lemma 19.31,
pp. 462, 464-466; and the unnumbered finite-net construction, pp. 461-462.
The local proof repairs and branch-regularity inputs are recorded in
reviews/contracts/M64-round1.md and
reviews/errata/2026-09-14-m64-annulus-comparison.md.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT

/-- Proposition 19.35: sufficiently small annular area prevents a loss of
more than one quarter of the first boundary length under the displayed
absolute-turning and Gaussian upper bounds. The bound K can be any real
number; the proof uses max(K,1). The strict first-length hypothesis is the
source's hypothesis. The local Claim 19.34, focusing and final-length
repairs are specified in the M64 contract and errata record. -/
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

/-- Lemma 19.31: the same small-area threshold works for every circle
circumference, included time and pair of C2 ramps. Positive slope implies
immersion and permits every positive degree. Turning is the integral of
the actual curvature norm on parameter subarcs, with the source's strict
1/200 bound. No shrinking-flow or chosen degree-one premise is imposed.
The C2 embedded-approximation and all-positive-degree Plateau reductions
are internal obligations; see pp. 464-466 and the M64 errata record. -/
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

/-- The finite-net construction on pp. 461-462 for an arbitrary raw C1
sphere family. The nodes are actual source parameters. Each member uses
one node for all positive circumferences below the common cutoff, and
the annulus lies in the same chosen product at the initial time. Nullity
and differentiability in the sphere parameter are not required. -/
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

/-- Every raw continuous C1 family has an actual finite small-annulus net
at each positive area tolerance. Compactness is used in the construction,
not replaced by a finite-net premise. Source: pp. 461-462; the M64 contract
records the short-geodesic annulus and product-Jacobian derivation. -/
def M64FamilyAnnulusNets (G : M63AmbientGeometry F) : Prop :=
  ∀ Gamma : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M)),
    ∀ mu : ℝ, 0 < mu → Nonempty (M64FamilyAnnulusNet G Gamma mu)

end Families

/-- One actual geometry and its complete annular conclusions. Earlier
analytic theorem services occur only at the M64 proof boundary. -/
structure M64FlowConclusion {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {a b : ℝ} (F : RicciFlow n M (Set.Icc a b)) where
  geometry : M63AmbientGeometry F
  evolution : M64AnnulusEvolution geometry
  ramp_comparison : M64RampSmallAnnulusComparison geometry
  projection : ∀ circumference (h : 0 < circumference), ∀ t ∈ Set.Icc a b,
    M64AnnulusProjection (geometry.product circumference h) t

/-- All three-dimensional outputs use the exact generic flow conclusion's
geometry. M65 selects this value once and retains its actual approximation,
solution family and applied estimates. -/
structure M64ThreeDimensionalFlowConclusion {M : Type u} [TopologicalSpace M]
    [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
    {a b : ℝ} (F : RicciFlow 3 M (Set.Icc a b)) where
  flow : M64FlowConclusion F
  approximation : M64FamilyApproximationTheory F flow.geometry
  disks : ∀ circumference (h : 0 < circumference), ∀ t ∈ Set.Icc a b,
    M64DiskAreaComparison (flow.geometry.product circumference h) t
  finite_nets : M64FamilyAnnulusNets flow.geometry

/-- The complete M64 contract: intrinsic comparison, static compact-family
approximation, annular evolution in dimension at least three, and the exact
three-dimensional family/disk/net outputs used by M65. Source and local
repairs are in reviews/contracts/M64-round1.md. The returned primitive
geometry never asserts equality with an independently chosen product. -/
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

end PoincareMT
