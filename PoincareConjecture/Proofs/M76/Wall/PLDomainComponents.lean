import PoincareConjecture.Proofs.M76.Wall.Mathlib.ClopenDomainFrontier
import PoincareConjecture.Proofs.M76.Wall.PLDomainLocalPathConnected
import PoincareConjecture.Proofs.M76.Wall.ProtectedPLIntersection










set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {P L : Set X}



theorem PLDomain.of_relative_clopen_subset (hP : PLDomain e P)
    (hLP : L ⊆ P) (hL : IsClosed L)
    (hopen : IsOpen ((Subtype.val : P → X) ⁻¹' L)) : PLDomain e L := by
  obtain ⟨U, hU, hLU⟩ := Set.exists_open_inter_of_relative_open hLP hopen
  have hfront := Set.frontier_eq_inter_of_eq_inter_open hP.closed hL hU hLU
  refine ⟨hP.cover, hP.compatible, hL, ?_⟩
  intro x hx
  rw [hfront] at hx
  have hxLU : x ∈ P ∩ U := by
    rw [← hLU]
    exact hx.1
  obtain ⟨ell, v, B, hv, hxB, hzero, hBe, hhalf⟩ := hP.halfspace x hx.2
  let H := B.restrOpen U hU
  refine ⟨ell, v, H, hv, ⟨hxB, hxLU.2⟩, hzero, ?_, ?_⟩
  · intro i
    exact (e i).piecewiseAffine_compatible_restrOpen_right B (hBe i) hU
  · intro y hy
    change y ∈ L ↔ 0 ≤ ell (B y)
    rw [hLU]
    exact ⟨fun h => (hhalf y hy.1).mp h.1,
      fun h => ⟨(hhalf y hy.1).mpr h, hy.2⟩⟩




theorem PLDomain.connectedComponentIn [T2Space X] (hP : PLDomain e P)
    (hPc : IsCompact P) {x : X} (hxP : x ∈ P) :
    PLDomain e (connectedComponentIn P x) := by
  let : LocallyPathConnectedSpace P := hP.locallyPathConnectedSpace
  exact hP.of_relative_clopen_subset (connectedComponentIn_subset P x)
    (Set.isCompact_connectedComponentIn_of_mem hPc hxP).isClosed
    (Set.isOpen_preimage_connectedComponentIn hxP)

end PoincareConjecture.M76
