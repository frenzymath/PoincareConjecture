import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Spheres.Iteration.Geometry
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Spheres.Removal

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "V3" => (Fin 3 → ℝ)
local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "R" => latticeHandleDomain (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "B" => latticeHandleBoundary (Fin 1) (Fin 2) L
local notation "p" => (4 * (128 : ℝ))
local notation "C" => AddCircle p
local notation "Q" => hamiltonOneHierarchyCoordinates
local notation "E" => latticeHandleDomainEquiv (Fin 1) (Fin 2) L

theorem PairedSourceGeometry.exists_closed_component_removal
    {α β : Type*} {e : α → OpenPartialHomeomorph X V3}
    {d : β → OpenPartialHomeomorph X V3}
    (hd : StandardLatticeHandleAtlas (Fin 1) (Fin 2) L d)
    {phi : C(H, H)}
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 1) (Fin 2) L phi))
    (hI : IsPLIrreducible e R)
    (F0 : (ContinuousMap.id H).HomotopyRel phi B)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < p)
    (geometry : PairedSourceGeometry e phi a b)
    {theta : ℝ} (htheta : theta ∈ ({a, b} : Set ℝ))
    {S : Set X} (hSne : S.Nonempty) (hS : S ⊆ sourceSurface phi (theta : C))
    (hcomponent : ∀ x ∈ S, connectedComponentIn (sourceSurface phi (theta : C)) x = S)
    (hrim : Disjoint S (frontier R)) :
    ∃ (psi : C(H, H)) (K : Set X) (T : phi.HomotopyRel psi B)
      (_F : (ContinuousMap.id H).HomotopyRel psi B),
      IsCompact K ∧ K ⊆ interior R ∧ S ⊆ interior K ∧
      ChartwisePLMap e d (latticeHandleMapInDomain (Fin 1) (Fin 2) L psi) ∧
      PairedSourceGeometry e psi a b ∧
      (∀ (t : unitInterval) (x : H), ((E).symm x : X) ∉ interior K → T (t, x) = phi x) ∧
      (∀ (t : unitInterval) (x : H), (Q (T (t, x))).1 = (Q (phi x)).1) ∧
      (∀ x : H, ((E).symm x : X) ∉ K → psi x = phi x) ∧
      psi ⁻¹' B = phi ⁻¹' B ∧ Disjoint S (sourceSurface psi (theta : C)) ∧
      (∀ s ∈ ({a, b} : Set ℝ),
        sourceSurface psi (s : C) = sourceSurface phi (s : C) \ K) ∧
      sourceSurface psi (a : C) ∪ sourceSurface psi (b : C) =
        (sourceSurface phi (a : C) ∪ sourceSurface phi (b : C)) \ K ∧
      Disjoint (sourceSurface phi (a : C) ∪ sourceSurface phi (b : C)) (frontier K) := by
  let : T2Space X := ((Homeomorph.refl (Fin 1 → ℝ)).prodCongr
    (hamiltonLowerLatticePiEquiv (Fin 2))).isEmbedding.t2Space
  have hfront' : frontier (sourceSlab phi b (a + p)) =
      (sourceSlab phi b (a + p) ∩ frontier R) ∪
        (sourceSurface phi (a : C) ∪ sourceSurface phi (b : C)) := by
    simpa only [AddCircle.coe_add_period, union_comm (sourceSurface phi (b : C))] using
      geometry.frontiers (b, a + p) (Or.inr rfl)
  obtain ⟨psi, K, T, hK, hKR, hSK, hpsi, ⟨F⟩, hfixed, hcoord, hB, hremoved,
      hphases, he, hf, he', hf', hcorners⟩ :=
    exists_closed_source_component_removal e d hd phi hphi hI F0 ha hab hb
      (geometry.domains (a, b) (Or.inl rfl))
      (geometry.domains (b, a + p) (Or.inr rfl))
      (geometry.frontiers (a, b) (Or.inl rfl)) hfront'
      geometry.ambient_injective geometry.corners htheta hSne hS hcomponent hrim
  have geometryNew : PairedSourceGeometry e psi a b := {
    domains := by
      intro uv huv
      rcases huv with rfl | rfl
      · exact he
      · exact he'
    frontiers := by
      intro uv huv
      rcases huv with rfl | rfl
      · exact hf
      · simpa only [AddCircle.coe_add_period, union_comm (sourceSurface psi (b : C))]
          using hf'
    corners := hcorners
    ambient_injective := fun s hs => (hphases s hs).2 }
  have hendpoint (x : H) (hx : ((E).symm x : X) ∉ interior K) : psi x = phi x :=
    (T.apply_one x).symm.trans (hfixed 1 x hx)
  have hfrontOne (s : ℝ) (hs : s ∈ ({a, b} : Set ℝ)) :
      Disjoint (sourceSurface phi (s : C)) (frontier K) := by
    apply disjoint_left.mpr
    intro x hx hxK
    have hxNew :=
      (sourceSurface_agrees_off_support phi psi hendpoint (s : C) x hxK.2).mpr hx
    rw [(hphases s hs).1] at hxNew
    exact hxNew.2 (hK.isClosed.frontier_subset hxK)
  refine ⟨psi, K, T, F, hK, hKR, hSK, hpsi, geometryNew, hfixed, hcoord,
    (fun x hx => hendpoint x (fun hi => hx (interior_subset hi))),
    hB, hremoved, (fun s hs => (hphases s hs).1), ?_, ?_⟩
  · rw [(hphases a (Or.inl rfl)).1, (hphases b (Or.inr rfl)).1, union_sdiff_distrib]
  · exact disjoint_union_left.mpr
      ⟨hfrontOne a (Or.inl rfl), hfrontOne b (Or.inr rfl)⟩

end PoincareConjecture.M76.HamiltonIntervalTorus
