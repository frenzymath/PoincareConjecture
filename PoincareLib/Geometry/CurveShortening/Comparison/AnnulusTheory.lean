import PoincareLib.Geometry.CurveShortening.Comparison.Annulus
import PoincareLib.Geometry.CurveShortening.Ramp.Estimates

/-!
# M64 annular infima, evolution and projected disk gluing

The supplied curves and annuli live in the same selected quotient product.
Nonempty area classes precede every geometric infimum comparison. The full
curvature norm in the forward bound is distinct from the unit-input bound
in the exponential estimate. Both disk-gluing directions retain arbitrary
positive area slack.

Source: Morgan--Tian Lemma 19.15 and Corollary 19.16, pp. 447-449,
and the disk/annulus comparisons on pp. 461-466. See the initial-homotopy,
endpoint, norm and reverse-gluing repairs in
reviews/errata/2026-09-14-m64-annulus-comparison.md.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT

section Evolution

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Set.Icc a b)}

/-- The actual annular infimum for the displayed pair at time t. -/
noncomputable def m64FlowAnnulusArea {circumference : ℝ}
    (P : M62.CircleProductData F circumference)
    (c0 c1 : ℝ → ℝ → P.charts.Point) (t : ℝ) : ℝ :=
  m64LeastAnnulusArea (P.flow.metric t) (fun x => c0 x t) (fun x => c1 x t)

/-- Lemma 19.15 and Corollary 19.16 for one actual pair of shrinking ramps.
This is a conclusion, with continuity at both included endpoints and the
upper forward difference only before the terminal time. -/
structure M64AnnulusFlowConclusion (G : M63AmbientGeometry F)
    {circumference : ℝ} (h : 0 < circumference)
    (c0 c1 : ℝ → ℝ → (G.product circumference h).charts.Point) : Prop where
  nonempty : ∀ t ∈ Set.Icc a b,
    Nonempty (M64Annulus ((G.product circumference h).flow.metric t)
      (fun x => c0 x t) (fun x => c1 x t))
  bounded_below : ∀ t ∈ Set.Icc a b,
    BddBelow (m64AnnulusAreaRange ((G.product circumference h).flow.metric t)
      (fun x => c0 x t) (fun x => c1 x t))
  nonnegative : ∀ t ∈ Set.Icc a b,
    0 <= m64FlowAnnulusArea (G.product circumference h) c0 c1 t
  continuous : ContinuousOn (m64FlowAnnulusArea (G.product circumference h) c0 c1)
    (Set.Icc a b)
  forward : ∀ t ∈ Set.Ico a b,
    AnnulusForwardDerivativeBound (m64FlowAnnulusArea (G.product circumference h) c0 c1)
      (((2 : ℝ) * n - 1) * m64CurvatureSupremum F t *
        m64FlowAnnulusArea (G.product circumference h) c0 c1 t) t
  exponential : ∀ s t : ℝ, s ∈ Set.Icc a b → t ∈ Set.Icc a b → s <= t →
    m64FlowAnnulusArea (G.product circumference h) c0 c1 t <=
      Real.exp (((2 : ℝ) * n - 1) * G.K0 * (t - s)) *
        m64FlowAnnulusArea (G.product circumference h) c0 c1 s

/-- Curvature regularity and evolution for the actual geometry. An initial
annulus is required: equal circle degree alone does not identify base free
homotopy classes. Positive degree one is imposed only for this evolution
branch, not for the later static ramp length comparison. -/
structure M64AnnulusEvolution (G : M63AmbientGeometry F) : Prop where
  curvature_bounded : ∀ t ∈ Set.Icc a b,
    BddAbove (Set.range (fun x : M => (F.connection t).curvatureTensorNorm x))
  curvature_nonnegative : ∀ t ∈ Set.Icc a b, 0 <= m64CurvatureSupremum F t
  curvature_continuous : ContinuousOn (m64CurvatureSupremum F) (Set.Icc a b)
  curves : ∀ circumference (h : 0 < circumference),
    ∀ c0 c1 : ℝ → ℝ → (G.product circumference h).charts.Point,
      M63C2ShrinkingCurveOn (G.product circumference h).flow c0 (Set.Icc a b) →
      M63C2ShrinkingCurveOn (G.product circumference h).flow c1 (Set.Icc a b) →
      M63IsRampAt (G.product circumference h) (fun x => c0 x a) a →
      M63IsRampAt (G.product circumference h) (fun x => c1 x a) a →
      (∃ L : M63PositiveDegreeLift (G.product circumference h) (fun x => c0 x a),
        L.degree = 1) →
      (∃ L : M63PositiveDegreeLift (G.product circumference h) (fun x => c1 x a),
        L.degree = 1) →
      M64Annulus ((G.product circumference h).flow.metric a)
        (fun x => c0 x a) (fun x => c1 x a) →
      M64AnnulusFlowConclusion G h c0 c1

/-- The literal projection is an admissible annulus, with the same map and
area integral, and projection does not increase area. These are conclusions
from the product identities, not premises about an arbitrary projection. -/
def M64AnnulusProjection {circumference : ℝ}
    (P : M62.CircleProductData F circumference) (t : ℝ) : Prop :=
  ∀ (c0 c1 : ℝ → P.charts.Point) (A : M64Annulus (P.flow.metric t) c0 c1),
    0 <= A.area ∧
      ∃ B : M64Annulus (F.metric t) (fun x => (c0 x).1) (fun x => (c1 x).1),
        B.map = (fun z => (A.map z).1) ∧
        B.area = m64ProjectedAnnulusArea P t A ∧ 0 <= B.area ∧ B.area <= A.area

end Evolution

section Disks

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {a b : ℝ} {F : RicciFlow 3 M (Set.Icc a b)}

/-- Both disk-gluing directions across an actual projected annulus, with
positive slack for arbitrary boundary homeomorphisms. The reverse clause
starts with an arbitrary disk for gamma1, as needed for the reverse infimum
bound. The final comparison separately requires nonempty filling classes. -/
structure M64DiskGluingConclusion {circumference : ℝ}
    (P : M62.CircleProductData F circumference) (t : ℝ)
    {c0 c1 : ℝ → P.charts.Point} (A : M64Annulus (P.flow.metric t) c0 c1)
    (gamma0 gamma1 : C1FreeLoopSpace (M := M)) : Prop where
  forward : ∀ eta : ℝ, 0 < eta → ∀ D0 : LipschitzSpanningDisk (F.metric t) gamma0,
    ∃ D1 : LipschitzSpanningDisk (F.metric t) gamma1,
      D1.area <= D0.area + m64ProjectedAnnulusArea P t A + eta
  reverse : ∀ eta : ℝ, 0 < eta → ∀ D1 : LipschitzSpanningDisk (F.metric t) gamma1,
    ∃ D0 : LipschitzSpanningDisk (F.metric t) gamma0,
      D0.area <= D1.area + m64ProjectedAnnulusArea P t A + eta
  infimum : Nonempty (LipschitzSpanningDisk (F.metric t) gamma0) →
    Nonempty (LipschitzSpanningDisk (F.metric t) gamma1) →
      |fillingArea (F.metric t) gamma1 - fillingArea (F.metric t) gamma0| <=
        m64ProjectedAnnulusArea P t A

/-- The disk comparison is applied only after identifying both actual base
boundary maps. It does not assume a differentiable boundary homeomorphism. -/
def M64DiskAreaComparison {circumference : ℝ}
    (P : M62.CircleProductData F circumference) (t : ℝ) : Prop :=
  ∀ (c0 c1 : ℝ → P.charts.Point) (A : M64Annulus (P.flow.metric t) c0 c1)
    (gamma0 gamma1 : C1FreeLoopSpace (M := M)),
      (∀ x, periodicFreeLoop gamma0 x = (c0 x).1) →
      (∀ x, periodicFreeLoop gamma1 x = (c1 x).1) →
        M64DiskGluingConclusion P t A gamma0 gamma1

end Disks

end PoincareMT
