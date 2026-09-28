import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Topology.CircleGroups.CocycleCharacters
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.SquareRimFilling

set_option autoImplicit false

open Set Metric PoincareConjecture.M76.Dehn

namespace PreAbstractSimplicialComplex.ModTwoEdgeCocycle

local notation "Q2" => sphere (0 : Fin 2 → ℝ) 1

theorem exists_squareRim_lift_of_pathValue_eq_zero
    {ι : Type*} [Fintype ι] {A : PreAbstractSimplicialComplex ι}
    (c : A.ModTwoEdgeCocycle) (γ : C(Q2, A.barycentricSpace))
    (hγ : c.pathValue (squareRimLoop.map γ.continuous) = 0) :
    ∃ q : C(Q2, c.bundle.TotalSpace), ∀ u, c.bundle.proj (q u) = γ u := by
  let p := squareRimLoop.map γ.continuous
  let a := c.sheetPoint (γ squareRimBase) 0
  let L := c.isCoveringMap.liftPath p.toContinuousMap a p.source
  have hL (t) : c.bundle.proj (L t) = p t :=
    congr_fun (c.isCoveringMap.liftPath_lifts p.toContinuousMap a p.source) t
  have hL0 : L 0 = a := c.isCoveringMap.liftPath_zero p.toContinuousMap a p.source
  have hL1 : L 1 = a := by
    have hbase : (L 1).proj = γ squareRimBase := (hL 1).trans p.target
    have hsheet : c.sheetCoordinate (L 1) = 0 := hγ
    change (L 1 : Bundle.TotalSpace (ZMod 2) (fun _ : A.barycentricSpace => ZMod 2)) =
      ⟨γ squareRimBase, (0 : ZMod 2)⟩
    cases h : L 1 with
    | mk x b =>
      rw [h] at hbase hsheet
      change x = γ squareRimBase at hbase
      change b = (0 : ZMod 2) at hsheet
      subst x
      subst b
      rfl
  let LP : Path a a := ⟨L, hL0, hL1⟩
  obtain ⟨q, hq⟩ := exists_squareRimMap LP
  refine ⟨q, ?_⟩
  intro u
  obtain ⟨t, rfl⟩ := surjective_squareRimLoop u
  rw [hq]
  exact hL t

end PreAbstractSimplicialComplex.ModTwoEdgeCocycle
