import PoincareConjecture.Definitions.M63Ramp
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Geometry.Polygon.Basic

set_option autoImplicit false

open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareConjecture

noncomputable def m63CellLength (N : ℕ) : ℝ := curvePeriod / (N : ℝ)

noncomputable def m63CellLeft (N : ℕ) (j : Fin N) : ℝ :=
  (j.val : ℝ) * m63CellLength N

noncomputable def m63ProfileBase (N : ℕ) (x : ℝ) : ℝ :=
  expNegInvGlue (1 - Real.cos ((N : ℝ) * x))

noncomputable def m63Profile (N : ℕ) (x : ℝ) : ℝ :=
  m63CellLength N * m63ProfileBase N x /
    (∫ s in (0 : ℝ)..m63CellLength N, m63ProfileBase N s)

noncomputable def m63Flattening (N : ℕ) (x : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..x, m63Profile N s

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

structure M63MinimizingGeodesicSide (g : RiemannianMetric n M)
    (D : LeviCivitaData g) (ell : ℝ) (p q : M) where
  map : ℝ → M
  domain : Set ℝ
  domain_open : IsOpen domain
  interval_subset : Set.Icc 0 ell ⊆ domain
  smooth : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ map domain
  start : map 0 = p
  finish : map ell = q
  speed : ℝ
  speed_nonnegative : 0 ≤ speed
  constant_speed : ∀ s ∈ Set.Icc 0 ell,
    g.tangentNorm (map s) (curveVelocity (n := n) map s) = speed
  equation : ∀ s ∈ domain,
    rampHorizontalCovariantDerivative D map
      (fun r => curveVelocity (n := n) map r) s = 0
  minimizing : g.pathELength map 0 ell = g.edist p q

structure M63GeodesicPolygon (g : RiemannianMetric n M)
    (D : LeviCivitaData g) (N : ℕ) where
  vertices : Polygon M N
  side : ∀ j : Fin N, M63MinimizingGeodesicSide g D (m63CellLength N)
    (vertices j) (vertices (finRotate N j))
  map : ℝ → M
  continuous : Continuous map
  periodic : Function.Periodic map curvePeriod
  cell_agreement : ∀ j : Fin N, ∀ s ∈ Set.Icc 0 (m63CellLength N),
    map (m63CellLeft N j + s) = (side j).map s

noncomputable def m63FlattenedPolygon {g : RiemannianMetric n M}
    {D : LeviCivitaData g} {N : ℕ} (P : M63GeodesicPolygon g D N)
    (x : ℝ) : M :=
  P.map (m63Flattening N x)

noncomputable def m63AngularFirstJet (gamma : ℝ → M) (x : ℝ) :
    TangentBundle (𝓡 n) M :=
  ⟨gamma x, curveVelocity (n := n) gamma x⟩

noncomputable def m63AngularSecondJet {g : RiemannianMetric n M}
    (D : LeviCivitaData g) (gamma : ℝ → M) (x : ℝ) :
    TangentBundle (𝓡 n) M :=
  ⟨gamma x, rampHorizontalCovariantDerivative D gamma
    (fun y => curveVelocity (n := n) gamma y) x⟩

end PoincareConjecture
