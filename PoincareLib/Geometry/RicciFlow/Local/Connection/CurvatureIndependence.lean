/- Adapted from Mapher `PoincareMT/Proofs/Ch01/CurvatureConnection.lean` at
f927d9e1f0810042766d3b5f64d3f4da02ee93cc. See
`references/ricci-flow/mapher/local-theory/port.json`. -/

import PoincareLib.Geometry.Riemannian.Curvature.Basic
import PoincareLib.Geometry.RicciFlow.Local.Connection.Regularity

/-!
# Curvature independence from the retained connection

For one smooth metric, the curvature evaluations agree for any two retained
Levi-Civita connections. The proofs use local connection regularity and are
relative to its inventoried proof obligation. See Morgan-Tian, printed pp. 3-7.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

/-- Curvature agrees on smooth local fields for two connections of the same metric. -/
theorem curvatureOnFields_eq (D D' : LeviCivitaData g)
    {U : Set M} (hU : IsOpen U)
    (X Y Z : (x : M) → TangentSpace (𝓡 n) x)
    (hX : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) U)
    (hY : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) U)
    (hZ : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Z) U)
    {x : M} (hx : x ∈ U) :
    D.curvatureOnFields X Y Z x = D'.curvatureOnFields X Y Z x := by
  have hconn (W : (y : M) → TangentSpace (𝓡 n) y)
      (hW : ContMDiffOn (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% W) U) :
      D.connection (fun y ↦ D.connection Z y (W y)) x =
        D'.connection (fun y ↦ D'.connection Z y (W y)) x := by
    have hD := D.contMDiffOn_connection_apply hU W Z hW hZ
    have hD' := D'.contMDiffOn_connection_apply hU W Z hW hZ
    rw [D.connection_eq_at D' _
      ((hD.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp))]
    apply D'.connection.isCovariantDerivativeOn.congr_of_eqOn
      ((hD.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp))
      ((hD'.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp))
      (hU.mem_nhds hx)
    intro y hy
    rw [D.connection_eq_at D' Z
      ((hZ.contMDiffAt (hU.mem_nhds hy)).mdifferentiableAt (by simp))]
  unfold curvatureOnFields
  rw [hconn Y hY, hconn X hX, D.connection_eq_at D' Z
    ((hZ.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp))]

/-- The fixed-extension curvature is independent of the compatible connection choice. -/
theorem localTheory_curvature_eq (D D' : LeviCivitaData g) (x : M)
    (u v w : TangentSpace (𝓡 n) x) :
    D.curvature x u v w = D'.curvature x u v w := by
  obtain ⟨U, hU, hu⟩ :=
    FiberBundle.exists_contMDiffOn_extend (k := ∞) (𝓡 n) (EuclideanSpace ℝ (Fin n)) u
  obtain ⟨V, hV, hv⟩ :=
    FiberBundle.exists_contMDiffOn_extend (k := ∞) (𝓡 n) (EuclideanSpace ℝ (Fin n)) v
  obtain ⟨W, hW, hw⟩ :=
    FiberBundle.exists_contMDiffOn_extend (k := ∞) (𝓡 n) (EuclideanSpace ℝ (Fin n)) w
  obtain ⟨S, hS, hSopen, hx⟩ :=
    mem_nhds_iff.mp (Filter.inter_mem hU (Filter.inter_mem hV hW))
  exact D.curvatureOnFields_eq D' hSopen _ _ _
    (hu.mono fun _ hy ↦ (hS hy).1)
    (hv.mono fun _ hy ↦ (hS hy).2.1)
    (hw.mono fun _ hy ↦ (hS hy).2.2) hx

/-- Lowered curvature is independent of the compatible connection choice. -/
theorem localTheory_curvatureTensor_eq (D D' : LeviCivitaData g) (x : M)
    (u v w z : TangentSpace (𝓡 n) x) :
    D.curvatureTensor x u v w z = D'.curvatureTensor x u v w z := by
  unfold curvatureTensor
  rw [D.localTheory_curvature_eq D']

/-- Ricci curvature is independent of the compatible connection choice. -/
theorem ricci_eq (D D' : LeviCivitaData g) (x : M)
    (u v : TangentSpace (𝓡 n) x) :
    D.ricci x u v = D'.ricci x u v := by
  simp only [ricci, D.localTheory_curvatureTensor_eq D']

/-- Scalar curvature is independent of the compatible connection choice. -/
theorem scalarCurvature_eq (D D' : LeviCivitaData g) (x : M) :
    D.scalarCurvature x = D'.scalarCurvature x := by
  simp only [scalarCurvature, D.ricci_eq D']

/-- Sectional curvature, including totalized inputs, is independent of the connection choice. -/
theorem sectionalCurvature_eq (D D' : LeviCivitaData g) (x : M)
    (u v : TangentSpace (𝓡 n) x) :
    D.sectionalCurvature x u v = D'.sectionalCurvature x u v := by
  simp only [sectionalCurvature, D.localTheory_curvatureTensor_eq D']

/-- The full four-tensor norm is independent of the compatible connection choice. -/
theorem localTheory_curvatureTensorNorm_eq (D D' : LeviCivitaData g) (x : M) :
    D.curvatureTensorNorm x = D'.curvatureTensorNorm x := by
  simp only [curvatureTensorNorm, D.localTheory_curvatureTensor_eq D']

end PoincareMT.LeviCivitaData
