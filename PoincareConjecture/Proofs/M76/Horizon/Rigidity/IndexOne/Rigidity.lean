import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Hierarchy.Regluing.SlabPL
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Hierarchy.Regluing.PairedPL
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Hierarchy.Regluing.RelativeEndpoint

set_option autoImplicit false
open Set

namespace PoincareConjecture.M76
open HamiltonIntervalTorus

local notation "V3" => (Fin 3 → ℝ)
local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "R" => latticeHandleDomain (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "B" => latticeHandleBoundary (Fin 1) (Fin 2) L
local notation "p" => (4 * (128 : ℝ))

theorem exists_fixed_indexOne_rigidity
    {α β : Type*} {e : α → OpenPartialHomeomorph X V3}
    {d : β → OpenPartialHomeomorph X V3}
    (hI : IsPLIrreducible e R) (hd : StandardLatticeHandleAtlas (Fin 1) (Fin 2) L d)
    (phi : C(H, H))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 1) (Fin 2) L phi))
    (F : (ContinuousMap.id H).HomotopyRel phi B) :
    ∃ g : H ≃ₜ H,
      ChartwisePLHomeomorph e d (latticeHandleHomeomorphInDomain (Fin 1) (Fin 2) L g) ∧
      Nonempty (phi.HomotopyRel ⟨g, g.continuous⟩ B) ∧
      Nonempty ((ContinuousMap.id H).HomotopyRel ⟨g, g.continuous⟩ B) := by
  obtain ⟨M, hm⟩ := exists_original_paired_exact_meridians e d hd phi hphi hI F
  obtain ⟨m₀⟩ := hm (M.a, M.b) (by simp)
  obtain ⟨m₁⟩ := hm (M.b, M.a + p) (by simp)
  obtain ⟨S₀, S₁, E, hE₀, hE₁, hfix⟩ :=
    exists_original_paired_slab_homeomorph hd m₀ m₁
  have hE : ChartwisePLMap d e ⟨E, E.continuous⟩ := by
    apply chartwisePLMap_of_standard_paired_slabs hd hI.1 ⟨E, E.continuous⟩
      (show 0 < M.a by linarith [M.a_range.1])
      (show M.a < M.b by linarith [M.a_range.2, M.b_range.1])
      (show M.b < p by linarith [M.b_range.2])
    intro uv huv K hK q hq hmap
    rcases huv with rfl | rfl
    · exact S₀.polyhedralPL_comp_of_slab_restriction hd ⟨E, E.continuous⟩
        hE₀ K hK q hq hmap
    · exact S₁.polyhedralPL_comp_of_slab_restriction hd ⟨E, E.continuous⟩
        hE₁ K hK q hq hmap
  let Q := latticeHandleDomainEquiv (Fin 1) (Fin 2) L
  let g : H ≃ₜ H := Q.symm.trans (E.trans Q)
  have hg : latticeHandleHomeomorphInDomain (Fin 1) (Fin 2) L g = E := by
    apply Homeomorph.ext
    intro x
    change Q.symm (Q (E (Q.symm (Q x)))) = E x
    rw [Q.symm_apply_apply, Q.symm_apply_apply]
  have hboundary (x : H) (hx : x ∈ B) : g x = x := by
    have hx' : (Q.symm x : X) ∈ frontier R := by
      have hb := Set.ext_iff.mp (latticeHandleDomainEquiv_preimage_boundary
        (Fin 1) (Fin 2) L) (Q.symm x)
      apply hb.mp
      change Q (Q.symm x) ∈ B
      simpa only [Q.apply_symm_apply] using hx
    change Q (E (Q.symm x)) = x
    rw [hfix _ hx', Q.apply_symm_apply]
  apply exists_relative_endpoint_of_standard_to_source hd g ?_ hboundary phi F
  simpa only [hg] using hE

end PoincareConjecture.M76
