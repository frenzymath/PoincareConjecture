import PoincareConjecture.Proofs.M04.ShiCoordinateConnection

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M62

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem curvatureTensor_pairing_of_commuting (D : LeviCivitaData g)
    {U : Set M} (hU : IsOpen U)
    {X Y Z W : (x : M) → TangentSpace (𝓡 n) x}
    (hX : ContMDiffOn (𝓡 n) (𝓡 n).tangent ∞ (T% X) U)
    (hY : ContMDiffOn (𝓡 n) (𝓡 n).tangent ∞ (T% Y) U)
    (hZ : ContMDiffOn (𝓡 n) (𝓡 n).tangent ∞ (T% Z) U)
    (hW : ContMDiffOn (𝓡 n) (𝓡 n).tangent ∞ (T% W) U)
    {x : M} (hx : x ∈ U)
    (hbr : VectorField.mlieBracket (𝓡 n) X Y x = 0) :
    D.curvatureTensor x (X x) (Y x) (Z x) (W x) =
      mvfderiv (𝓡 n) (fun y => g.inner y (D.connection W y (Y y)) (Z y)) x (X x) -
        g.inner x (D.connection W x (Y x)) (D.connection Z x (X x)) -
      mvfderiv (𝓡 n) (fun y => g.inner y (D.connection W y (X y)) (Z y)) x (Y x) +
        g.inner x (D.connection W x (X x)) (D.connection Z x (Y x)) := by
  have hYW := ((M04.contMDiffOn_shi_connection D hU hY hW).contMDiffAt
    (hU.mem_nhds hx)).mdifferentiableAt (by simp)
  have hXW := ((M04.contMDiffOn_shi_connection D hU hX hW).contMDiffAt
    (hU.mem_nhds hx)).mdifferentiableAt (by simp)
  have hZd := (hZ.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)
  have h1 := M04.metric_derivative_pairing D X hYW hZd
  have h2 := M04.metric_derivative_pairing D Y hXW hZd
  change g.inner x (D.curvature x (X x) (Y x) (W x)) (Z x) = _
  rw [← M04.curvatureOnFields_eq_curvature D hU hX hY hW hx]
  simp only [LeviCivitaData.curvatureOnFields, hbr, map_zero, sub_zero, map_sub, sub_apply]
  linarith only [h1, h2]

end PoincareConjecture.M62
