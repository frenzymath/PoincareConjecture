import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Spheres.Iteration.Elimination
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Spheres.Iteration.TerminalAnnuli
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Hierarchy.IrreducibleSlabs

set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "V3" => (Fin 3 → ℝ)
local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "R" => latticeHandleDomain (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "B" => latticeHandleBoundary (Fin 1) (Fin 2) L
local notation "p" => (4 * (128 : ℝ))
local notation "C" => AddCircle p
local notation "Ann" => squareAnnulus 8 1

theorem exists_relative_whole_source_annuli
    {α β : Type*} (e : α → OpenPartialHomeomorph X V3)
    (d : β → OpenPartialHomeomorph X V3)
    (hd : StandardLatticeHandleAtlas (Fin 1) (Fin 2) L d)
    (phi : C(H, H))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 1) (Fin 2) L phi))
    (hI : IsPLIrreducible e R)
    (F0 : (ContinuousMap.id H).HomotopyRel phi B) :
    ∃ a ∈ Ioo (p / 4) (p / 3), ∃ b ∈ Ioo (2 * p / 3) (3 * p / 4),
      ∃ (eta : C(H, H)) (K : Set X) (Feta : (ContinuousMap.id H).HomotopyRel eta B),
        IsCompact K ∧ K ⊆ interior R ∧
        (∀ x : H, ((latticeHandleDomainEquiv (Fin 1) (Fin 2) L).symm x : X) ∉ K →
          eta x = phi x) ∧
        ChartwisePLMap e d (latticeHandleMapInDomain (Fin 1) (Fin 2) L eta) ∧
        Nonempty (phi.HomotopyRel eta B) ∧ eta ⁻¹' B = phi ⁻¹' B ∧
        PairedSourceGeometry e eta a b ∧
        (∀ uv ∈ ({(a, b), (b, a + p)} : Set (ℝ × ℝ)),
          IsPLIrreducible e (sourceSlab eta uv.1 uv.2)) ∧
        ∀ theta ∈ ({a, b} : Set ℝ),
          ∃ (A : Ann ≃ₜ sourceSurface eta (theta : C)) (q : ℝ × ℝ → X),
            PolyhedralPLInCharts e q Ann ∧ (∀ x : Ann, (A x : X) = q x) ∧
            ∀ side z, (A (Dehn.annulusRimPoint side z) : X) =
              (sourceBoundaryCircle eta (theta : C) Feta (originalIntervalEndpoint side)
                (originalIntervalEndpoint_norm side)
                (AddCircle.homeomorphAddCircle (4 * (8 : ℝ)) p
                  (by norm_num) (by norm_num) z) : X) := by
  obtain ⟨a, ha, b, hb, eta, K, Feta, hK, hKR, hfixed, heta, Heta, hB, geometry,
      noClosed⟩ := exists_relative_source_phases_without_closed_components e d hd phi hphi hI F0
  have hannuli := geometry.exists_whole_phase_annuli hd heta Feta
    (show 0 < a by linarith [ha.1]) (show a < b by linarith [ha.2, hb.1])
    (show b < p by linarith [hb.2]) noClosed
  obtain ⟨A, _, _, _, _⟩ := hannuli a (Or.inl rfl)
  obtain ⟨B', _, _, _, _⟩ := hannuli b (Or.inr rfl)
  exact ⟨a, ha, b, hb, eta, K, Feta, hK, hKR, hfixed, heta, Heta, hB,
    geometry, geometry.irreducible_slabs hI A B', hannuli⟩

end PoincareConjecture.M76.HamiltonIntervalTorus
