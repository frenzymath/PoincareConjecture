import PoincareConjecture.Proofs.M76.Mathlib.AlexanderRecursiveCutSide










set_option autoImplicit false

open Set

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]





theorem AlexanderCollarSlab.opposite_cut_side_of_cap_avoidance {S : Set E}
    {A : E →ᵃ[ℝ] ℝ} {q : E} {β : ℝ} (M : AlexanderCollarSlab S A q β)
    {n : ℕ} (P : Polygon E (n + 3))
    (hPe : P.HasSimplicialEdges) (hPi : Function.Injective P)
    {d s s' : Set E} (hd : IsFinitePLBallPair (ℝ × ℝ) d (P.boundary ℝ))
    (hs : IsFinitePLBallPair (ℝ × ℝ) s (P.boundary ℝ))
    (hs' : IsFinitePLBallPair (ℝ × ℝ) s' (P.boundary ℝ))
    (hunion : s ∪ s' = S) (hinter : s ∩ s' = P.boundary ℝ)
    (hP : P.boundary ℝ ⊆ S ∩ {x | A x = 0})
    (havoid : d ∩ closure ((s ∪ d) ∩ {x | 0 < A x}) ⊆ {q}) :
    ∀ p : {p : E × ℝ | p.1 ∈ S ∩ {x | A x = 0} ∧
        p.2 ∈ Icc 0 (M.upper p.1)},
      (p : E × ℝ).1 ∈ P.boundary ℝ →
        (M.chart p : E) ∈ s' ∧ ((M.chart p : E) ∈ s ↔ (p : E × ℝ).2 = 0) := by
  have hTS : M.collar ⊆ S :=
    (subset_union_left.trans M.cover.subset).trans inter_subset_left
  have hchoice := P.pointed_collar_cut_side hPe hPi M.chart M.height M.bottom hP
    M.upper_finitePL q M.apex_upper (fun x hx => M.upper_pos x (hP hx))
    hs hs' (hTS.trans hunion.symm.subset) hinter (hP.trans inter_subset_right)
  rcases hchoice with hwrong | hright
  · obtain ⟨ec⟩ := P.nonempty_boundary_homeomorph_circle hPe hPi
    obtain ⟨x, hx⟩ :=
      (isConnected_sdiff_singleton_of_homeomorph_circle (P.boundary ℝ) ec q).nonempty
    have hxclosure : x ∈ closure (s ∩ {y | 0 < A y}) :=
      M.chart.collar_bottom_mem_closure_positive M.height M.bottom (hP hx.1)
        (M.upper_pos x (hP hx.1) hx.2)
        (fun p hpx _ => (hwrong p (hpx.symm ▸ hx.1)).1)
    have hxq : x = q := havoid ⟨hd.1 hx.1,
      closure_mono (inter_subset_inter_left _ subset_union_left) hxclosure⟩
    exact (hx.2 hxq).elim
  · exact hright

end Geometry
