import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Convex.Contractible

/-!
# Simple connectivity of factors with a contractible complement

A product with a contractible factor is homotopy equivalent to its other
factor. In particular, the surface in a simply connected sphere-line
splitting is simply connected.

Application: Morgan--Tian, Proposition 9.83, p. 236.
-/

noncomputable section
set_option autoImplicit false

namespace Poincare.Topology

/-- Taking a product with a contractible space preserves simple connectivity. -/
theorem simplyConnectedSpace_prod_contractible
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [ContractibleSpace Y] [SimplyConnectedSpace X] :
    SimplyConnectedSpace (X × Y) := by
  obtain ⟨e⟩ := ContractibleSpace.hequiv Y Unit
  let h := ((ContinuousMap.HomotopyEquiv.refl X).prodCongr e).trans
    (Homeomorph.prodUnique X Unit).toHomotopyEquiv
  exact h.simplyConnectedSpace

/-- Simple connectivity descends past a contractible product factor. -/
theorem simplyConnectedSpace_of_prod_contractible
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [ContractibleSpace Y] [SimplyConnectedSpace (X × Y)] :
    SimplyConnectedSpace X := by
  obtain ⟨e⟩ := ContractibleSpace.hequiv Y Unit
  let h := ((ContinuousMap.HomotopyEquiv.refl X).prodCongr e).trans
    (Homeomorph.prodUnique X Unit).toHomotopyEquiv
  exact h.symm.simplyConnectedSpace

/-- A product decomposition with a real-line factor of a simply connected
space has simply connected transverse factor. -/
theorem simplyConnectedSpace_of_prod_real_homeomorph
    {X M : Type*} [TopologicalSpace X] [TopologicalSpace M]
    [SimplyConnectedSpace M] (e : (X × ℝ) ≃ₜ M) :
    SimplyConnectedSpace X := by
  let : SimplyConnectedSpace (X × ℝ) := e.toHomotopyEquiv.simplyConnectedSpace
  exact simplyConnectedSpace_of_prod_contractible (X := X) (Y := ℝ)

end Poincare.Topology
