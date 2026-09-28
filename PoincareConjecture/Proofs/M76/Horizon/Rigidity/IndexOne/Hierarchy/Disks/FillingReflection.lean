import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.SquareRimFilling
import Mathlib.Analysis.Convex.Contractible
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected









set_option autoImplicit false
open Set Metric

namespace PoincareConjecture.M76.Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1



theorem exists_square_filling_of_pi1_injective
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (i : C(Y, X)) (gamma : C(Q, Y))
    (hinj : Function.Injective (FundamentalGroup.map i (gamma squareRimBase)))
    (ambient : C(D, X))
    (hboundary : ∀ x : Q, ambient ⟨x, sphere_subset_closedBall x.property⟩ = i (gamma x)) :
    ∃ filling : C(D, Y),
      ∀ x : Q, filling ⟨x, sphere_subset_closedBall x.property⟩ = gamma x := by
  let : ContractibleSpace D := (convex_closedBall (0 : V2) 1).contractibleSpace
    ⟨0, mem_closedBall_self (by norm_num)⟩
  let j : C(Q, D) := ⟨fun x => ⟨x, sphere_subset_closedBall x.property⟩, by fun_prop⟩
  let rim : Path (j squareRimBase) (j squareRimBase) := squareRimLoop.map j.continuous
  have hcontract := (SimplyConnectedSpace.paths_homotopic rim
    (Path.refl (j squareRimBase))).map ambient
  have hbase : ambient (j squareRimBase) = i (gamma squareRimBase) := hboundary squareRimBase
  have hloop : (rim.map ambient.continuous).cast hbase.symm hbase.symm =
      (squareRimLoop.map gamma.continuous).map i.continuous := by
    ext t
    exact hboundary (squareRimLoop t)
  have hrefl : ((Path.refl (j squareRimBase)).map ambient.continuous).cast
      hbase.symm hbase.symm =
      Path.refl (i (gamma squareRimBase)) := by
    ext t
    exact hbase
  have hnullAmbient : ((squareRimLoop.map gamma.continuous).map i.continuous).Homotopic
      (Path.refl (i (gamma squareRimBase))) := by
    simpa only [hloop, hrefl] using hcontract.pathCast hbase.symm hbase.symm
  have hmap : FundamentalGroup.map i (gamma squareRimBase)
      (FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk (squareRimLoop.map gamma.continuous))) = 1 :=
    Path.Homotopic.Quotient.eq.mpr hnullAmbient
  have hnull : FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (squareRimLoop.map gamma.continuous)) = 1 :=
    hinj (hmap.trans (map_one (FundamentalGroup.map i (gamma squareRimBase))).symm)
  exact (nullhomotopic_of_squareRimLoop gamma
    (Path.Homotopic.Quotient.exact hnull)).exists_closedBall_extension gamma



theorem exists_square_filling_in_subset
    {X : Type*} [TopologicalSpace X] {N : Set X}
    (gamma : C(Q, N))
    (hinj : Function.Injective (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(N, X)) (gamma squareRimBase)))
    (ambient : C(D, X))
    (hboundary : ∀ x : Q, ambient ⟨x, sphere_subset_closedBall x.property⟩ = (gamma x : X)) :
    ∃ filling : C(D, N),
      ∀ x : Q, filling ⟨x, sphere_subset_closedBall x.property⟩ = gamma x :=
  exists_square_filling_of_pi1_injective
    ⟨Subtype.val, continuous_subtype_val⟩ gamma hinj ambient hboundary

end PoincareConjecture.M76.Dehn
