import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Spheres.Iteration.PhaseFamily
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Spheres.Iteration.Removal

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
local notation "E" => latticeHandleDomainEquiv (Fin 1) (Fin 2) L

private def EliminationCandidate {α β : Type*}
    (e : α → OpenPartialHomeomorph X V3) (d : β → OpenPartialHomeomorph X V3)
    (phi : C(H, H)) (a b : ℝ) (n : ℕ) : Prop :=
  ∃ (eta : C(H, H)) (K : Set X), IsCompact K ∧ K ⊆ interior R ∧
    (∀ x : H, ((E).symm x : X) ∉ K → eta x = phi x) ∧
    ChartwisePLMap e d (latticeHandleMapInDomain (Fin 1) (Fin 2) L eta) ∧
    Nonempty (phi.HomotopyRel eta B) ∧ Nonempty ((ContinuousMap.id H).HomotopyRel eta B) ∧
    eta ⁻¹' B = phi ⁻¹' B ∧ PairedSourceGeometry e eta a b ∧
    ∃ M : Fin n → Set X,
      (⋃ i, M i) = sourceSurface eta (a : C) ∪ sourceSurface eta (b : C) ∧
      ∀ i, IsConnected (M i)

theorem exists_relative_source_phases_without_closed_components
    {α β : Type*} (e : α → OpenPartialHomeomorph X V3)
    (d : β → OpenPartialHomeomorph X V3)
    (hd : StandardLatticeHandleAtlas (Fin 1) (Fin 2) L d)
    (phi : C(H, H))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 1) (Fin 2) L phi))
    (hI : IsPLIrreducible e R)
    (F0 : (ContinuousMap.id H).HomotopyRel phi B) :
    ∃ a ∈ Ioo (p / 4) (p / 3), ∃ b ∈ Ioo (2 * p / 3) (3 * p / 4),
      ∃ (eta : C(H, H)) (K : Set X) (_Feta : (ContinuousMap.id H).HomotopyRel eta B),
        IsCompact K ∧ K ⊆ interior R ∧
        (∀ x : H, ((E).symm x : X) ∉ K → eta x = phi x) ∧
        ChartwisePLMap e d (latticeHandleMapInDomain (Fin 1) (Fin 2) L eta) ∧
        Nonempty (phi.HomotopyRel eta B) ∧ eta ⁻¹' B = phi ⁻¹' B ∧
        PairedSourceGeometry e eta a b ∧
        ∀ theta ∈ ({a, b} : Set ℝ), ∀ S : Set X,
          S.Nonempty → S ⊆ sourceSurface eta (theta : C) →
          (∀ x ∈ S, connectedComponentIn (sourceSurface eta (theta : C)) x = S) →
          Disjoint S (frontier R) → False := by
  classical
  let : T2Space X := ((Homeomorph.refl (Fin 1 → ℝ)).prodCongr
    (hamiltonLowerLatticePiEquiv (Fin 2))).isEmbedding.t2Space
  obtain ⟨a, haI, b, hbI, eta0, K0, hK0, hK0R, hfixed0, heta0, Heta0, ⟨Feta0⟩,
      hB0, geometry0⟩ := exists_relative_paired_source_geometry e d hd phi hphi F0
  have ha : 0 < a := by linarith [haI.1]
  have hab : a < b := by linarith [haI.2, hbI.1]
  have hb : b < p := by linarith [hbI.2]
  obtain ⟨n0, M0, hM0, hM0conn⟩ :=
    geometry0.exists_finite_connected_phase_cover heta0 Feta0 ha hab hb
  have hex : ∃ n, EliminationCandidate e d phi a b n :=
    ⟨n0, eta0, K0, hK0, hK0R, hfixed0, heta0, Heta0, ⟨Feta0⟩, hB0, geometry0,
      M0, hM0, hM0conn⟩
  obtain ⟨eta, K, hK, hKR, hfixed, heta, ⟨Heta⟩, ⟨Feta⟩, hB, geometry,
      M, hM, hMconn⟩ := Nat.find_spec hex
  refine ⟨a, haI, b, hbI, eta, K, Feta, hK, hKR, hfixed, heta, ⟨Heta⟩, hB,
    geometry, ?_⟩
  intro theta htheta S hSne hS hcomponent hrim
  obtain ⟨psi, K', T, Fpsi, hK', hK'R, hSK', hpsi, geometry', _, _, hfixed',
      hB', _, _, hphaseUnion, hfrontK'⟩ :=
    geometry.exists_closed_component_removal hd heta hI Feta ha hab hb
      htheta hSne hS hcomponent hrim
  have hmeet : ((sourceSurface eta (a : C) ∪ sourceSurface eta (b : C)) ∩ K').Nonempty := by
    obtain ⟨x, hx⟩ := hSne
    refine ⟨x, ?_, interior_subset (hSK' hx)⟩
    rcases htheta with rfl | rfl
    · exact Or.inl (hS hx)
    · exact Or.inr (hS hx)
  obtain ⟨m, U, hmn, hU, hUconn⟩ :=
    exists_finite_connected_cover_decrease M hM hMconn hK'.isClosed hfrontK' hmeet
  have hnew : EliminationCandidate e d phi a b m := by
    refine ⟨psi, K ∪ K', hK.union hK', union_subset hKR hK'R, ?_, hpsi,
      ⟨Heta.trans T⟩, ⟨Fpsi⟩, hB'.trans hB, geometry', U, hU.trans hphaseUnion.symm, hUconn⟩
    intro x hx
    exact (hfixed' x (fun h => hx (Or.inr h))).trans (hfixed x (fun h => hx (Or.inl h)))
  exact (Nat.not_lt_of_ge (Nat.find_min' hex hnew)) hmn

end PoincareConjecture.M76.HamiltonIntervalTorus
