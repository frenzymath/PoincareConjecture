/- Adapted from Mapher `PoincareMT/Proofs/M03/ConnectionRegularity.lean` at
f927d9e1f0810042766d3b5f64d3f4da02ee93cc. See
`references/ricci-flow/mapher/local-theory/port.json`. -/

import PoincareLib.Geometry.RicciFlow.Local.Connection.Koszul
import PoincareLib.Geometry.RicciFlow.Local.Connection.Coordinates
import Mathlib.Geometry.Manifold.VectorBundle.Hom

/-!
# Local regularity of the explicit Levi-Civita connection

The first theorem uses the local Koszul identity and smooth inversion of a
positive Gram matrix, as in Morgan-Tian, Theorem 1.2 and formula (1.1),
printed pp. 3-4. The second theorem applies that result to a smooth direction
field. The imported proofs are kernel-closed; their semantic review remains
part of the M03 helper review. The aggregate audit checks the foundation
closure without weakening the module or project guards.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

/-- Smoothness of the connection on a locally smooth section. -/
theorem contMDiffOn_connection (D : LeviCivitaData g)
    {U : Set M} (hU : IsOpen U)
    (Y : (x : M) → TangentSpace (𝓡 n) x)
    (hY : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) U) :
    ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))) ∞
      (fun x ↦ Bundle.TotalSpace.mk'
        (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
        x (D.connection Y x)) U := by
  apply RicciFlow.Local.koszul_operator_contMDiffOn g (fun Y x ↦ D.connection Y x)
    ?_ hU Y hY
  intro X Y Z x hX hY hZ
  have hk := D.koszul X Y Z hX hY hZ
  linarith only [hk]

/-- Apply the local regularity obligation to a smooth direction field. -/
theorem contMDiffOn_connection_apply (D : LeviCivitaData g)
    {U : Set M} (hU : IsOpen U)
    (X Y : (x : M) → TangentSpace (𝓡 n) x)
    (hX : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) U)
    (hY : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) U) :
    ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (T% (fun x ↦ D.connection Y x (X x))) U := by
  exact (D.contMDiffOn_connection hU Y hY).clm_bundle_apply hX

end PoincareMT.LeviCivitaData
