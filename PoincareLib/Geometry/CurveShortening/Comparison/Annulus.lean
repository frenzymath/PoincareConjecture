import PoincareLib.Geometry.RicciFlow.Extinction.Width.Class.SphereArea
import PoincareLib.Geometry.CurveShortening.Ramp.Polygon
import PoincareLib.Geometry.CurveShortening.Comparison.Geometry

/-!
# M64 actual annuli and raw-boundary filling disks

An annulus is a metric Lipschitz map of the angular rectangle, periodic in
its first coordinate, with exact boundary maps and an integrable actual
Jacobian. The target can be the literal M62 quotient product; no real lift
restricts the relative winding class. Raw polygon boundaries are continuous
circle maps, without an invented C1 regularity assertion.

Source: Morgan--Tian Lemma 19.15, Claims 19.19-19.20 and Corollary 19.21,
pp. 447-451; reviews/contracts/M64-round1.md and
reviews/errata/2026-09-14-m64-annulus-comparison.md.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal

open MeasureTheory

universe u

namespace PoincareMT

/-- The fixed fundamental rectangle, with angular period 2*pi. -/
def m64AnnulusDomain : Set LoopPlane :=
  {p | 0 <= p 0 ∧ p 0 <= curvePeriod ∧ 0 <= p 1 ∧ p 1 <= 1}

section Annuli

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

/-- Area of the actual map on the fixed rectangle. Geometric uses require
the regularity and integrability of an admissible annulus. -/
noncomputable def m64AnnulusArea (g : RiemannianMetric n M)
    (f : LoopPlane → M) : ℝ :=
  ∫ p in m64AnnulusDomain, m60AreaDensity g f p

/-- An admissible annulus with literal periodic boundary maps. The Lipschitz
and a.e. derivative conditions exclude rough maps with spurious zero area. -/
structure M64Annulus (g : RiemannianMetric n M) (c0 c1 : ℝ → M) where
  map : LoopPlane → M
  continuous_on_domain : ContinuousOn map m64AnnulusDomain
  periodic : ∀ x s : ℝ,
    map (annulusPoint (x + curvePeriod) s) = map (annulusPoint x s)
  lower_boundary : ∀ x : ℝ, map (annulusPoint x 0) = c0 x
  upper_boundary : ∀ x : ℝ, map (annulusPoint x 1) = c1 x
  lipschitz_constant : ℝ
  lipschitz_nonnegative : 0 <= lipschitz_constant
  lipschitz_on_domain : ∀ x y : m64AnnulusDomain,
    g.edist (map x) (map y) <=
      ENNReal.ofReal lipschitz_constant * ENNReal.ofReal ‖(x : LoopPlane) - y‖
  ae_manifold_differentiable : ∀ᵐ z ∂volume,
    z ∈ m64AnnulusDomain → MDifferentiableAt (𝓡 2) (𝓡 n) map z
  area_integrable : IntegrableOn (m60AreaDensity g map) m64AnnulusDomain volume

noncomputable def M64Annulus.area {g : RiemannianMetric n M}
    {c0 c1 : ℝ → M} (A : M64Annulus g c0 c1) : ℝ :=
  m64AnnulusArea g A.map

/-- The full area range. Its nonemptiness is not built into the infimum. -/
def m64AnnulusAreaRange (g : RiemannianMetric n M) (c0 c1 : ℝ → M) : Set ℝ :=
  Set.range (fun A : M64Annulus g c0 c1 => A.area)

noncomputable def m64LeastAnnulusArea (g : RiemannianMetric n M)
    (c0 c1 : ℝ → M) : ℝ :=
  sInf (m64AnnulusAreaRange g c0 c1)

/-- Finite piecewise C1 regularity on actual closed angular strips. This is
an extra property of the polygonal construction, not a restriction on all
annuli in the area infimum. -/
def M64PiecewiseC1Annulus {g : RiemannianMetric n M} {c0 c1 : ℝ → M}
    (A : M64Annulus g c0 c1) : Prop :=
  ∃ k : ℕ, 0 < k ∧ ∃ cut : Fin (k + 1) → ℝ,
    StrictMono cut ∧ cut 0 = 0 ∧ cut (Fin.last k) = curvePeriod ∧
      ∀ j : Fin k, ContMDiffOn (𝓡 2) (𝓡 n) 1 A.map
        {p | cut j.castSucc <= p 0 ∧ p 0 <= cut j.succ ∧ 0 <= p 1 ∧ p 1 <= 1}

/-- Every transverse slice is the actual minimizing geodesic between its
displayed endpoints. The source's small-area interpolation has this property. -/
def M64GeodesicAnnulus {g : RiemannianMetric n M} (D : LeviCivitaData g)
    {c0 c1 : ℝ → M} (A : M64Annulus g c0 c1) : Prop :=
  ∀ x : ℝ, ∃ side : M63MinimizingGeodesicSide g D 1 (c0 x) (c1 x),
    ∀ s ∈ Set.Icc (0 : ℝ) 1, A.map (annulusPoint x s) = side.map s

end Annuli

section Product

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Set.Icc a b)} {circumference : ℝ}

/-- Area of the literal base projection at the same time and base metric. -/
noncomputable def m64ProjectedAnnulusArea
    (P : M62.CircleProductData F circumference) (t : ℝ)
    {c0 c1 : ℝ → P.charts.Point} (A : M64Annulus (P.flow.metric t) c0 c1) : ℝ :=
  m64AnnulusArea (F.metric t) (fun z => (A.map z).1)

/-- The actual full four-tensor curvature supremum, distinct from M63's
unit-input bound K0. Compactness and continuity justify its use later. -/
noncomputable def m64CurvatureSupremum (F : RicciFlow n M (Set.Icc a b))
    (t : ℝ) : ℝ :=
  sSup (Set.range (fun x : M => (F.connection t).curvatureTensorNorm x))

end Product

section Disks

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]

/-- The actual continuous boundary of an existing C1 loop. -/
def m64C1Boundary (gamma : C1FreeLoopSpace (M := M)) : ContinuousMap LoopCircle M :=
  ⟨gamma.toFun, gamma.continuous⟩

/-- Raw nullity uses an actual continuous filling, with no C1 boundary premise. -/
def M64RawNullLoop (gamma : ContinuousMap LoopCircle M) : Prop :=
  ∃ f : LoopPlane → M, Continuous f ∧ ∀ z : LoopCircle, f z = gamma z

/-- The same Lipschitz disk and Jacobian as the C1 filling class, indexed
by a continuous boundary so unsmoothed polygon corners are allowed. -/
structure M64RawSpanningDisk (g : RiemannianMetric 3 M)
    (gamma : ContinuousMap LoopCircle M) where
  map : LoopPlane → M
  continuous_on_disk : ContinuousOn map loopDiskSet
  ae_manifold_differentiable : ∀ᵐ z ∂volume,
    z ∈ loopDiskSet → MDifferentiableAt (𝓡 2) (𝓡 3) map z
  reparameterization : CircleReparameterization
  boundary_eq : ∀ z : LoopCircle, map z = gamma (reparameterization.map z)
  lipschitz_constant : ℝ
  lipschitz_nonnegative : 0 <= lipschitz_constant
  lipschitz_on_disk : ∀ x y : LoopDisk,
    g.edist (map x) (map y) <=
      ENNReal.ofReal lipschitz_constant * ENNReal.ofReal ‖(x : LoopPlane) - y‖
  area_integrable : IntegrableOn (parametrizedAreaDensity g map) loopDiskSet volume
  area_nonnegative : 0 <= parametrizedRiemannianArea g map

noncomputable def M64RawSpanningDisk.area {g : RiemannianMetric 3 M}
    {gamma : ContinuousMap LoopCircle M} (D : M64RawSpanningDisk g gamma) : ℝ :=
  parametrizedRiemannianArea g D.map

def m64RawDiskAreaRange (g : RiemannianMetric 3 M)
    (gamma : ContinuousMap LoopCircle M) : Set ℝ :=
  Set.range (fun D : M64RawSpanningDisk g gamma => D.area)

noncomputable def m64RawFillingArea (g : RiemannianMetric 3 M)
    (gamma : ContinuousMap LoopCircle M) : ℝ :=
  sInf (m64RawDiskAreaRange g gamma)

end Disks

end PoincareMT
