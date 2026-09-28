import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Convex.Contractible











noncomputable section
set_option autoImplicit false

namespace Poincare.Topology


theorem simplyConnectedSpace_prod_contractible
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [ContractibleSpace Y] [SimplyConnectedSpace X] :
    SimplyConnectedSpace (X × Y) := by
  obtain ⟨e⟩ := ContractibleSpace.hequiv Y Unit
  let h := ((ContinuousMap.HomotopyEquiv.refl X).prodCongr e).trans
    (Homeomorph.prodUnique X Unit).toHomotopyEquiv
  exact h.simplyConnectedSpace


theorem simplyConnectedSpace_of_prod_contractible
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [ContractibleSpace Y] [SimplyConnectedSpace (X × Y)] :
    SimplyConnectedSpace X := by
  obtain ⟨e⟩ := ContractibleSpace.hequiv Y Unit
  let h := ((ContinuousMap.HomotopyEquiv.refl X).prodCongr e).trans
    (Homeomorph.prodUnique X Unit).toHomotopyEquiv
  exact h.symm.simplyConnectedSpace



theorem simplyConnectedSpace_of_prod_real_homeomorph
    {X M : Type*} [TopologicalSpace X] [TopologicalSpace M]
    [SimplyConnectedSpace M] (e : (X × ℝ) ≃ₜ M) :
    SimplyConnectedSpace X := by
  let : SimplyConnectedSpace (X × ℝ) := e.toHomotopyEquiv.simplyConnectedSpace
  exact simplyConnectedSpace_of_prod_contractible (X := X) (Y := ℝ)

end Poincare.Topology
