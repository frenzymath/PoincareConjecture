import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Coordinates.KoszulCoefficient
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.VectorField.LieBracket
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Geometry.ChartVectorField

/-! Generic variation constructions reused by the reduced-length theory. -/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology BigOperators

universe u

namespace PoincareMT.ReducedLength

export PoincareMT.ReducedLengthMinimum.Variation.Geometry
  (chartVectorField chartVectorField_smooth chartVectorField_at_inverse chartVectorField_bracket mvfderiv_chartVectorField)

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)

theorem chartVectorField_diagonal_koszul {g : RiemannianMetric n M}
    (D : LeviCivitaData g) (p : M) (v w : E) (x : M)
    (hx : x ∈ (chartAt E p).source) :
    2 * g.inner x
        (D.connection (chartVectorField p v) x (chartVectorField p v x))
        (chartVectorField p w x) =
      2 * mvfderiv (𝓡 n)
        (fun q ↦ g.inner q (chartVectorField p v q) (chartVectorField p w q)) x
        (chartVectorField p v x) -
      mvfderiv (𝓡 n)
        (fun q ↦ g.inner q (chartVectorField p v q) (chartVectorField p v q)) x
        (chartVectorField p w x) := by
  have hV (a : E) := ((chartVectorField_smooth p a).contMDiffAt
    ((chartAt E p).open_source.mem_nhds hx)).mdifferentiableAt (by simp)
  have h := leviCivita_koszul_at D x (chartVectorField p v) (chartVectorField p v)
    (chartVectorField p w) (hV v) (hV v) (hV w)
  rw [chartVectorField_bracket p v v x hx, chartVectorField_bracket p v w x hx] at h
  simpa only [map_zero, ContinuousLinearMap.zero_apply, add_zero, sub_zero, two_mul] using h


end PoincareMT.ReducedLength
