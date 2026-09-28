import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Compression.Frontier.ResidualDecrease
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

theorem exists_supported_wide_sourceSlab_frontier_decrease
    {α β : Type*} {e : α → OpenPartialHomeomorph X V3}
    {d : β → OpenPartialHomeomorph X V3}
    (hd : StandardLatticeHandleAtlas (Fin 1) (Fin 2) L d)
    {phi : C(H, H)}
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 1) (Fin 2) L phi))
    (F0 : (ContinuousMap.id H).HomotopyRel phi B)
    {c a b : ℝ} (ha : c < a) (hab : a < b) (hb : b < c + p)
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
      ∃ newModel : FrontierResidualModel e (sourceSlab psi a b) (frontier (sourceSlab psi a b)),
        newModel.complexity < oldModel.complexity := by
  let : T2Space ((Fin 2 → ℝ) ⧸ (hamiltonLowerPeriodLattice (Fin 2)).toAddSubgroup) :=
    (hamiltonLowerLatticePiEquiv (Fin 2)).isEmbedding.t2Space
  obtain ⟨P, psi, A, hPB, hcut, hcomp, hA, _, _, hAR, hpsi, hF, hF0, hfixed,
    hGa, hGb, hslab, hboundary, hopen, hside⟩ :=
    exists_wide_lower_source_slab_map hd hphi F0 ha hab hb hN he hfront hj hi hjN
      hproper (fun z hz => hrimS ⟨z, hz⟩) havoid
  obtain ⟨newModel, hdecrease⟩ := exists_compressed_frontier_model hN he P hopen rim hrim hessential oldModel
  obtain ⟨_, _, hcutfront, _, _, _⟩ := P.cut_geometry hN hopen
  have hnewfront : frontier (sourceSlab psi a b) = (sourceSlab psi a b ∩ frontier R) ∪
      (sourceSurface psi (a : C) ∪ sourceSurface psi (b : C)) := by
    rw [hslab, hcutfront, hfront, hGa, hGb]
    ext x
    have hR : x ∈ frontier R → x ∉ P.openStrip := by
      intro hx
      rintro ⟨z, hz, rfl⟩
      exact hPB ⟨hz.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩ hx
    have hB : x ∈ sourceSurface phi (b : C) → x ∉ P.openStrip := by
      intro hx
      rintro ⟨z, hz, rfl⟩
      have hzfull : z ∈ D ×ˢ Icc (-1 : ℝ) 1 :=
        ⟨hz.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩
      exact disjoint_left.mp hAB
        (hside z hzfull (hfront.symm.subset (Or.inr (Or.inr hx)))) hx
    change (((x ∈ sourceSlab phi a b ∧ x ∈ frontier R) ∨
        (x ∈ sourceSurface phi (a : C) ∨ x ∈ sourceSurface phi (b : C))) ∧ x ∉ P.openStrip) ∨
        x ∈ P.endDisks ↔
      ((x ∈ sourceSlab phi a b ∧ x ∉ P.openStrip) ∧ x ∈ frontier R) ∨
        (((x ∈ sourceSurface phi (a : C) ∧ x ∉ P.openStrip) ∨ x ∈ P.endDisks) ∨
          x ∈ sourceSurface phi (b : C))
    tauto
  refine ⟨psi, A, hA, hAR, hfixed, hpsi, hF, hF0, hslab.symm ▸ hcomp, hslab.symm ▸ hcut,
    hnewfront, hGb, hboundary, ?_⟩
  rw [hslab]
  exact ⟨newModel, hdecrease⟩

theorem exists_wide_sourceSlab_frontier_decrease
    {α β : Type*} {e : α → OpenPartialHomeomorph X V3}
    {d : β → OpenPartialHomeomorph X V3}
    (hd : StandardLatticeHandleAtlas (Fin 1) (Fin 2) L d)
    {phi : C(H, H)}
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 1) (Fin 2) L phi))
    (F0 : (ContinuousMap.id H).HomotopyRel phi B)
    {c a b : ℝ} (ha : c < a) (hab : a < b) (hb : b < c + p)
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
    ∃ psi : C(H, H),
      ChartwisePLMap e d (latticeHandleMapInDomain (Fin 1) (Fin 2) L psi) ∧
      Nonempty (phi.HomotopyRel psi B) ∧ Nonempty ((ContinuousMap.id H).HomotopyRel psi B) ∧
      IsCompact (sourceSlab psi a b) ∧ PLDomain e (sourceSlab psi a b) ∧
      frontier (sourceSlab psi a b) = (sourceSlab psi a b ∩ frontier R) ∪
        (sourceSurface psi (a : C) ∪ sourceSurface psi (b : C)) ∧
      sourceSurface psi (b : C) = sourceSurface phi (b : C) ∧
      psi ⁻¹' B = phi ⁻¹' B ∧
      ∃ newModel : FrontierResidualModel e (sourceSlab psi a b) (frontier (sourceSlab psi a b)),
        newModel.complexity < oldModel.complexity := by
  obtain ⟨psi, A, _, _, _, hrest⟩ :=
    exists_supported_wide_sourceSlab_frontier_decrease hd hphi F0 ha hab hb hN he hfront hAB oldModel
      hj hi hjN hproper havoid rim hrim hrimS hessential
  exact ⟨psi, hrest⟩

theorem exists_sourceSlab_frontier_decrease
    {α β : Type*} {e : α → OpenPartialHomeomorph X V3}
    {d : β → OpenPartialHomeomorph X V3}
    (hd : StandardLatticeHandleAtlas (Fin 1) (Fin 2) L d)
    {phi : C(H, H)}
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 1) (Fin 2) L phi))
    (F0 : (ContinuousMap.id H).HomotopyRel phi B)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < p) (_hshort : b - a < p / 2)
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
    ∃ psi : C(H, H),
      ChartwisePLMap e d (latticeHandleMapInDomain (Fin 1) (Fin 2) L psi) ∧
      Nonempty (phi.HomotopyRel psi B) ∧ Nonempty ((ContinuousMap.id H).HomotopyRel psi B) ∧
      IsCompact (sourceSlab psi a b) ∧ PLDomain e (sourceSlab psi a b) ∧
      frontier (sourceSlab psi a b) = (sourceSlab psi a b ∩ frontier R) ∪
        (sourceSurface psi (a : C) ∪ sourceSurface psi (b : C)) ∧
      sourceSurface psi (b : C) = sourceSurface phi (b : C) ∧
      psi ⁻¹' B = phi ⁻¹' B ∧
      ∃ newModel : FrontierResidualModel e (sourceSlab psi a b) (frontier (sourceSlab psi a b)),
        newModel.complexity < oldModel.complexity := by
  exact exists_wide_sourceSlab_frontier_decrease hd hphi F0 ha hab (by simpa using hb)
    hN he hfront hAB oldModel hj hi hjN hproper havoid rim hrim hrimS hessential

end PoincareConjecture.M76.HamiltonIntervalTorus
