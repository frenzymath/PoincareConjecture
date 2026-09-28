import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Compression.Frontier.MapDecrease
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Compression.Frontier.UpperDecrease
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Compression.Complement.Frontier
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Compression.SlabMap



set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1
local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "R" => latticeHandleDomain (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "B" => latticeHandleBoundary (Fin 1) (Fin 2) L
local notation "p" => (4 * (128 : ℝ))
local notation "C" => AddCircle p

theorem exists_supported_complementary_lower_frontier_decrease
    {α β : Type*} {e : α → OpenPartialHomeomorph X V3}
    {d : β → OpenPartialHomeomorph X V3}
    (hd : StandardLatticeHandleAtlas (Fin 1) (Fin 2) L d)
    {phi : C(H, H)}
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 1) (Fin 2) L phi))
    (F0 : (ContinuousMap.id H).HomotopyRel phi B)
    {c a b : ℝ} (ha : c < a) (hab : a < b) (hb : b < c + p)
    (hcomp : PLDomain e (sourceSlab phi b (a + p)))
    (hN : IsCompact (sourceSlab phi a b)) (he : PLDomain e (sourceSlab phi a b))
    (hfront : frontier (sourceSlab phi a b) = (sourceSlab phi a b ∩ frontier R) ∪
      (sourceSurface phi (a : C) ∪ sourceSurface phi (b : C)))
    (hAB : Disjoint (sourceSurface phi (a : C)) (sourceSurface phi (b : C)))
    (oldModel : FrontierResidualModel e (sourceSlab phi a b) (frontier (sourceSlab phi a b)))
    {j : V2 → X} (hj : PolyhedralPLInCharts e j D)
    (hi : Topology.IsEmbedding (fun z : D => j z)) (hjN : MapsTo j D (sourceSlab phi a b))
    (hproper : ∀ z : D, j z ∈ frontier (sourceSlab phi a b) ↔ (z : V2) ∈ Q)
    (havoid : ∀ z : D, j z ∉ frontier R)
    (rim : C(Q, frontier (sourceSlab phi a b)))
    (hrim : ∀ z : Q, (rim z : X) = j z)
    (hrimS : ∀ z : Q, j z ∈ sourceSurface phi (a : C))
    (hessential : FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (Dehn.squareRimLoop.map rim.continuous)) ≠ 1) :
    ∃ (psi : C(H, H)) (A : Set X), IsCompact A ∧ A ⊆ interior R ∧
      (∀ x : H, ((latticeHandleDomainEquiv (Fin 1) (Fin 2) L).symm x : X) ∉ interior A →
        psi x = phi x) ∧
      ChartwisePLMap e d (latticeHandleMapInDomain (Fin 1) (Fin 2) L psi) ∧
      Nonempty (phi.HomotopyRel psi B) ∧ Nonempty ((ContinuousMap.id H).HomotopyRel psi B) ∧
      IsCompact (sourceSlab psi a b) ∧ PLDomain e (sourceSlab psi a b) ∧
      frontier (sourceSlab psi a b) = (sourceSlab psi a b ∩ frontier R) ∪
        (sourceSurface psi (a : C) ∪ sourceSurface psi (b : C)) ∧
      sourceSurface psi (b : C) = sourceSurface phi (b : C) ∧
      psi ⁻¹' B = phi ⁻¹' B ∧
      IsCompact (sourceSlab psi b (a + p)) ∧ PLDomain e (sourceSlab psi b (a + p)) ∧
      frontier (sourceSlab psi b (a + p)) = (sourceSlab psi b (a + p) ∩ frontier R) ∪
        (sourceSurface psi (a : C) ∪ sourceSurface psi (b : C)) ∧
      ∃ newModel : FrontierResidualModel e (sourceSlab psi a b) (frontier (sourceSlab psi a b)),
        newModel.complexity < oldModel.complexity := by
  obtain ⟨psi, A, hA, hAR, hfixed, hpsi, hF, hF0, hc, hepsi, hf', hu, hB,
      model, hdec⟩ :=
    exists_supported_wide_sourceSlab_frontier_decrease hd hphi F0 ha hab hb hN he hfront hAB oldModel
      hj hi hjN hproper havoid rim hrim hrimS hessential
  let : T2Space ((Fin 2 → ℝ) ⧸ (hamiltonLowerPeriodLattice (Fin 2)).toAddSubgroup) :=
    (hamiltonLowerLatticePiEquiv (Fin 2)).isEmbedding.t2Space
  exact ⟨psi, A, hA, hAR, hfixed, hpsi, hF, hF0, hc, hepsi, hf', hu, hB,
    sourceSlab_isCompact psi b (a + p),
    plDomain_complementary_sourceSlab_of_supported_map phi psi ha hab hb hcomp hepsi hf'
      hA.isClosed hAR hfixed,
    frontier_complementary_sourceSlab psi ha hab hb hepsi hf', model, hdec⟩

theorem exists_supported_complementary_upper_frontier_decrease
    {α β : Type*} {e : α → OpenPartialHomeomorph X V3}
    {d : β → OpenPartialHomeomorph X V3}
    (hd : StandardLatticeHandleAtlas (Fin 1) (Fin 2) L d)
    {phi : C(H, H)}
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 1) (Fin 2) L phi))
    (F0 : (ContinuousMap.id H).HomotopyRel phi B)
    {c a b : ℝ} (ha : c < a) (hab : a < b) (hb : b < c + p)
    (hcomp : PLDomain e (sourceSlab phi b (a + p)))
    (hN : IsCompact (sourceSlab phi a b)) (he : PLDomain e (sourceSlab phi a b))
    (hfront : frontier (sourceSlab phi a b) = (sourceSlab phi a b ∩ frontier R) ∪
      (sourceSurface phi (a : C) ∪ sourceSurface phi (b : C)))
    (hAB : Disjoint (sourceSurface phi (a : C)) (sourceSurface phi (b : C)))
    (oldModel : FrontierResidualModel e (sourceSlab phi a b) (frontier (sourceSlab phi a b)))
    {j : V2 → X} (hj : PolyhedralPLInCharts e j D)
    (hi : Topology.IsEmbedding (fun z : D => j z)) (hjN : MapsTo j D (sourceSlab phi a b))
    (hproper : ∀ z : D, j z ∈ frontier (sourceSlab phi a b) ↔ (z : V2) ∈ Q)
    (havoid : ∀ z : D, j z ∉ frontier R)
    (rim : C(Q, frontier (sourceSlab phi a b)))
    (hrim : ∀ z : Q, (rim z : X) = j z)
    (hrimS : ∀ z : Q, j z ∈ sourceSurface phi (b : C))
    (hessential : FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (Dehn.squareRimLoop.map rim.continuous)) ≠ 1) :
    ∃ (psi : C(H, H)) (A : Set X), IsCompact A ∧ A ⊆ interior R ∧
      (∀ x : H, ((latticeHandleDomainEquiv (Fin 1) (Fin 2) L).symm x : X) ∉ interior A →
        psi x = phi x) ∧
      ChartwisePLMap e d (latticeHandleMapInDomain (Fin 1) (Fin 2) L psi) ∧
      Nonempty (phi.HomotopyRel psi B) ∧ Nonempty ((ContinuousMap.id H).HomotopyRel psi B) ∧
      IsCompact (sourceSlab psi a b) ∧ PLDomain e (sourceSlab psi a b) ∧
      frontier (sourceSlab psi a b) = (sourceSlab psi a b ∩ frontier R) ∪
        (sourceSurface psi (a : C) ∪ sourceSurface psi (b : C)) ∧
      sourceSurface psi (a : C) = sourceSurface phi (a : C) ∧
      psi ⁻¹' B = phi ⁻¹' B ∧
      IsCompact (sourceSlab psi b (a + p)) ∧ PLDomain e (sourceSlab psi b (a + p)) ∧
      frontier (sourceSlab psi b (a + p)) = (sourceSlab psi b (a + p) ∩ frontier R) ∪
        (sourceSurface psi (a : C) ∪ sourceSurface psi (b : C)) ∧
      ∃ newModel : FrontierResidualModel e (sourceSlab psi a b) (frontier (sourceSlab psi a b)),
        newModel.complexity < oldModel.complexity := by
  obtain ⟨psi, A, hA, hAR, hfixed, hpsi, hF, hF0, hc, hepsi, hf, hu, hB,
      model, hdec⟩ :=
    exists_supported_upper_sourceSlab_frontier_decrease hd hphi F0 ha hab hb hN he
      (by simpa only [union_comm] using hfront) hAB.symm oldModel
      hj hi hjN hproper havoid rim hrim hrimS hessential
  have hf' : frontier (sourceSlab psi a b) = (sourceSlab psi a b ∩ frontier R) ∪
      (sourceSurface psi (a : C) ∪ sourceSurface psi (b : C)) := by
    simpa only [union_comm] using hf
  let : T2Space ((Fin 2 → ℝ) ⧸ (hamiltonLowerPeriodLattice (Fin 2)).toAddSubgroup) :=
    (hamiltonLowerLatticePiEquiv (Fin 2)).isEmbedding.t2Space
  exact ⟨psi, A, hA, hAR, hfixed, hpsi, hF, hF0, hc, hepsi, hf', hu, hB,
    sourceSlab_isCompact psi b (a + p),
    plDomain_complementary_sourceSlab_of_supported_map phi psi ha hab hb hcomp hepsi hf'
      hA.isClosed hAR hfixed,
    frontier_complementary_sourceSlab psi ha hab hb hepsi hf', model, hdec⟩

end PoincareConjecture.M76.HamiltonIntervalTorus
