import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.MetricFamily.PullbackCoefficients
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Elliptic.Dirichlet.Coefficients
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.WeakRegularity.CanonicalEquation




noncomputable section
set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology
open Poincare.Analysis.Parabolic.WeakRegularity

namespace PoincareConjecture.RicciFlow.BackwardCoordinates

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}

def domain (J : Set ℝ) (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M) :
    Set (Spacetime n) := e.source ×ˢ ((fun τ : ℝ => -τ) ⁻¹' interior J)

theorem isOpen_domain (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M) :
    IsOpen (domain J e) :=
  e.open_source.prod (isOpen_interior.preimage continuous_neg)

theorem domain_Iio_zero (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M) :
    domain (Iio 0) e = e.source ×ˢ Ioi 0 := by
  ext z
  simp [domain]

def density (F : RicciFlow n M J)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M) (z : Spacetime n) : ℝ :=
  (F.metric (-z.2)).pullbackVolumeDensity e z.1

def principal (F : RicciFlow n M J)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (i j : Fin n) (z : Spacetime n) : ℝ :=
  EuclideanSpace.proj i (((F.metric (-z.2)).pullbackCoefficients e z.1).inverse
    (EuclideanSpace.proj j))

def weightedPrincipal (F : RicciFlow n M J)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (i j : Fin n) (z : Spacetime n) : ℝ :=
  LeviCivitaData.Dirichlet.divergenceCoefficients (F.metric (-z.2)) e z.1 i j

theorem weightedPrincipal_eq (F : RicciFlow n M J)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (i j : Fin n) (z : Spacetime n) :
    weightedPrincipal F e i j z = density F e z * principal F e i j z := rfl

def drift (F : RicciFlow n M J)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (i : Fin n) (z : Spacetime n) : ℝ :=
  (density F e z)⁻¹ * ∑ j, Canonical.spatialDeriv j (weightedPrincipal F e j i) z

end PoincareConjecture.RicciFlow.BackwardCoordinates
