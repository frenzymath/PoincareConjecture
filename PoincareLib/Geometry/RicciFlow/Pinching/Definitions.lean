import PoincareLib.Geometry.Riemannian.Curvature.Basic

/-!
# Three-dimensional Hamilton--Ivey quantities

These are the library copies of the reviewed frozen definitions.  The least
sectional value is taken over actual orthonormal tangent pairs; no curvature
operator or eigenbasis is built into the definition.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT.LeviCivitaData

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

def IsOrthonormalPair (g : RiemannianMetric 3 M) (x : M)
    (u v : TangentSpace (𝓡 3) x) : Prop :=
  g.inner x u u = 1 ∧ g.inner x v v = 1 ∧ g.inner x u v = 0

noncomputable def leastSectionalCurvature (D : LeviCivitaData g) (x : M) : ℝ :=
  sInf {k : ℝ | ∃ u v : TangentSpace (𝓡 3) x,
    IsOrthonormalPair g x u v ∧ k = D.curvatureTensor x u v u v}

noncomputable def negativeCurvaturePart (D : LeviCivitaData g) (x : M) : ℝ :=
  max (-D.leastSectionalCurvature x) 0

end PoincareMT.LeviCivitaData
