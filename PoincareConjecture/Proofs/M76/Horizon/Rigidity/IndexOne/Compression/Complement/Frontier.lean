import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Compression.Complement.Preservation

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "V3" => (Fin 3 → ℝ)
local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "R" => latticeHandleDomain (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "p" => (4 * (128 : ℝ))
local notation "C" => AddCircle p

theorem sourcePhases_subset_complementarySlab
    (phi : C(H, H)) {a b : ℝ} (hgap : b < a + p) :
    sourceSurface phi (a : C) ∪ sourceSurface phi (b : C) ⊆ sourceSlab phi b (a + p) := by
  intro x hx
  rw [sourceSlab_eq_inter_phase]
  rcases hx with hx | hx
  · rw [sourceSurface_eq_inter_phase] at hx
    refine ⟨hx.1, ?_⟩
    change ambientSourcePhase phi x ∈ AddCircle.closedIntervalArc p b (a + p)
    rw [hx.2]
    exact ⟨a + p, ⟨by linarith, le_rfl⟩, AddCircle.coe_add_period p a⟩
  · rw [sourceSurface_eq_inter_phase] at hx
    refine ⟨hx.1, ?_⟩
    change ambientSourcePhase phi x ∈ AddCircle.closedIntervalArc p b (a + p)
    rw [hx.2]
    exact ⟨b, ⟨le_rfl, by linarith⟩, rfl⟩

theorem frontier_complementary_sourceSlab
    {α : Type*} {e : α → OpenPartialHomeomorph X V3}
    (phi : C(H, H)) {c a b : ℝ} (ha : c < a) (hab : a < b) (hb : b < c + p)
    (he : PLDomain e (sourceSlab phi a b))
    (hfront : frontier (sourceSlab phi a b) = (sourceSlab phi a b ∩ frontier R) ∪
      (sourceSurface phi (a : C) ∪ sourceSurface phi (b : C))) :
    frontier (sourceSlab phi b (a + p)) = (sourceSlab phi b (a + p) ∩ frontier R) ∪
      (sourceSurface phi (a : C) ∪ sourceSurface phi (b : C)) := by
  let : T2Space ((Fin 2 → ℝ) ⧸ (hamiltonLowerPeriodLattice (Fin 2)).toAddSubgroup) :=
    (hamiltonLowerLatticePiEquiv (Fin 2)).isEmbedding.t2Space
  have hclosed := (sourceSlab_isCompact phi b (a + p)).isClosed
  have hlocal (x : X) (hx : x ∈ interior R) :
      x ∈ frontier (sourceSlab phi b (a + p)) ↔ x ∈ frontier (sourceSlab phi a b) := by
    have h := mem_frontier_iff_of_open_agreement isOpen_interior
      (complementary_sourceSlab_agrees_exterior phi ha hab hb hfront) hx
    rwa [he.frontier_closed_exterior] at h
  have hold (x : X) (hx : x ∈ sourceSlab phi b (a + p)) (hxI : x ∉ interior R) :
      x ∈ frontier (sourceSlab phi b (a + p)) := by
    apply (mem_frontier_iff_notMem_interior hx).mpr
    exact fun h => hxI (interior_mono (sourceSlab_subset phi b (a + p)) h)
  apply Subset.antisymm
  · intro x hx
    by_cases hxI : x ∈ interior R
    · have hf := (hlocal x hxI).mp hx
      rw [hfront] at hf
      rcases hf with hf | hf
      · exact (disjoint_left.mp disjoint_interior_frontier hxI hf.2).elim
      · exact Or.inr hf
    · have hxM := hclosed.frontier_subset hx
      exact Or.inl ⟨hxM, (mem_frontier_iff_notMem_interior
        (sourceSlab_subset phi b (a + p) hxM)).mpr hxI⟩
  · intro x hx
    rcases hx with hx | hx
    · exact hold x hx.1 (fun h => disjoint_left.mp disjoint_interior_frontier h hx.2)
    · by_cases hxI : x ∈ interior R
      · exact (hlocal x hxI).mpr (hfront.symm.subset (Or.inr hx))
      · exact hold x (sourcePhases_subset_complementarySlab phi (by linarith : b < a + p) hx) hxI

end PoincareConjecture.M76.HamiltonIntervalTorus
