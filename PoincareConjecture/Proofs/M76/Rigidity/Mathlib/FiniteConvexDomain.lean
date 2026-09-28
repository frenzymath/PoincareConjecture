import PoincareConjecture.Proofs.M76.Triangulation.HamiltonIndexOneDomainCharts
import PoincareConjecture.Proofs.M76.Triangulation.ConvexSphereLargeDisks

set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

local notation "V3" => (Fin 3 → ℝ)

theorem plDomain_convex_of_frontier_points
    (K : SimplicialComplex ℝ V3) (hK : K.faces.Finite) {C : Set V3}
    (hC : IsCompact C) (hcv : Convex ℝ C) (hne : (interior C).Nonempty)
    (hKC : K.space = C) {p q : V3} (hp : p ∈ frontier C)
    (hq : q ∈ frontier C) (hpq : p ≠ q) :
    PoincareConjecture.M76.PLDomain
      (fun _ : Unit => (Homeomorph.refl V3).toOpenPartialHomeomorph) C := by
  let J := K.frontierSubcomplex C
  have hJ : J.faces.Finite := K.frontierSubcomplex_finite C hK
  have hJS : J.space = frontier C :=
    K.frontierSubcomplex_space hC.isClosed hcv hne hKC
  have hpatch (x : frontier C) : ∃ d r : Set V3,
      IsFinitePLBallPair (ℝ × ℝ) d r ∧ d ⊆ frontier C ∧ (x : V3) ∈ d \ r ∧
        IsOpen ((Subtype.val : frontier C → V3) ⁻¹' (d \ r)) := by
    have hpole : ∃ y : frontier C, (y : V3) ≠ (x : V3) := by
      by_cases hpx : p = (x : V3)
      · exact ⟨⟨q, hq⟩, fun h => hpq (hpx.trans h.symm)⟩
      · exact ⟨⟨p, hp⟩, hpx⟩
    obtain ⟨y, hy⟩ := hpole
    obtain ⟨d, r, hd, hds, hxd, _, hopen⟩ :=
      J.exists_convex_frontier_disk_of_compact_with_open_interior hJ hC hcv hne hJS
        (F := ℝ × ℝ) (by simp [Module.finrank_prod]) y isCompact_singleton
        (singleton_subset_iff.mpr x.property) (by simpa only [mem_singleton_iff] using hy)
    exact ⟨d, r, hd, hds, hxd (mem_singleton _), hopen⟩
  have hreg : closure (interior C) = C := by
    rw [hcv.closure_interior_eq_closure_of_nonempty_interior hne, hC.isClosed.closure_eq]
  apply PoincareConjecture.M76.HamiltonIndexOne.plDomain_of_regular_closed_local_ball_pairs
    hC.isClosed hreg J hJ hJS
  rw [hJS]
  exact hpatch

end Geometry.SimplicialComplex
