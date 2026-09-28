import PoincareConjecture.Proofs.M76.PrimeReduction.PLDomainExterior
import PoincareConjecture.Proofs.M76.Wall.ProtectedPLIntersection

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {R P : Set X}

theorem frontier_inter_eq_of_closed (hR : IsClosed R) (hP : IsClosed P) :
    frontier (R ∩ P) = (frontier R ∩ P) ∪ (R ∩ frontier P) := by
  rw [(hR.inter hP).frontier_eq, hR.frontier_eq, hP.frontier_eq, interior_inter]
  ext x
  simp only [mem_sdiff, mem_inter_iff, mem_union]
  tauto

theorem PLDomain.halfspace_inter_right (he : PLDomain e R)
    {x : X} (hx : x ∈ frontier R) (hxP : x ∈ interior P) :
    ∃ (ell : V3 →ᴬ[ℝ] ℝ) (v : V3) (B : OpenPartialHomeomorph X V3),
      ell.contLinear v = 1 ∧ x ∈ B.source ∧ ell (B x) = 0 ∧
      (∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid V3) ∧
      ∀ y ∈ B.source, y ∈ R ∩ P ↔ 0 ≤ ell (B y) := by
  obtain ⟨ell, v, B, hv, hxB, hzero, hPL, hhalf⟩ := he.halfspace x hx
  let C := B.restrOpen (interior P) isOpen_interior
  refine ⟨ell, v, C, hv, ?_, hzero, ?_, ?_⟩
  · exact ⟨hxB, hxP⟩
  · intro i
    exact (e i).piecewiseAffine_compatible_restrOpen_right B (hPL i) isOpen_interior
  · intro y hy
    change y ∈ R ∩ P ↔ 0 ≤ ell (B y)
    constructor
    · exact fun h => (hhalf y hy.1).mp h.1
    · exact fun h => ⟨(hhalf y hy.1).mpr h, interior_subset hy.2⟩

theorem PLDomain.inter_of_disjoint_frontiers (he : PLDomain e R)
    (hP : PLDomain e P) (hdisj : Disjoint (frontier R) (frontier P)) :
    PLDomain e (R ∩ P) := by
  refine ⟨he.cover, he.compatible, he.closed.inter hP.closed, ?_⟩
  intro x hx
  rw [frontier_inter_eq_of_closed he.closed hP.closed] at hx
  rcases hx with hx | hx
  · have hxP : x ∈ interior P := by
      by_contra h
      exact disjoint_left.mp hdisj hx.1 ((mem_frontier_iff_notMem_interior hx.2).mpr h)
    exact he.halfspace_inter_right hx.1 hxP
  · have hxR : x ∈ interior R := by
      by_contra h
      exact disjoint_left.mp hdisj ((mem_frontier_iff_notMem_interior hx.1).mpr h) hx.2
    simpa only [inter_comm P R] using hP.halfspace_inter_right hx.2 hxR

end PoincareConjecture.M76
