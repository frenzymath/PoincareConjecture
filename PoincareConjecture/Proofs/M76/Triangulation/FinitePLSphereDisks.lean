import PoincareConjecture.Proofs.M76.Triangulation.ConvexSphereLargeDisks
import PoincareConjecture.Proofs.M76.Mathlib.ConvexFrontierOtherPoint
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallPreimages











set_option autoImplicit false

open Set Geometry

namespace Homeomorph

variable {E F V : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]






theorem IsFinitePL.exists_local_ball_pairs_of_convex_frontier
    {s : Set E} {C : Set F} {e : s ≃ₜ frontier C} (he : e.IsFinitePL)
    (hC : IsCompact C) (hcv : Convex ℝ C) (hne : (interior C).Nonempty)
    (hdim : Module.finrank ℝ F = Module.finrank ℝ V + 1) (x : s) :
    ∃ d q : Set E, IsFinitePLBallPair V d q ∧ d ⊆ s ∧ (x : E) ∈ d \ q ∧
      IsOpen ((Subtype.val : s → E) ⁻¹' (d \ q)) := by
  have htri := he.symm
  obtain ⟨_, ⟨K, hK, hKC, _⟩, _⟩ := htri
  obtain ⟨p, hpx⟩ := hC.exists_ne_frontier_point hcv hne (e x)
  have hpx' : (p : F) ∉ ({(e x : F)} : Set F) :=
    fun h => hpx (Subtype.ext (mem_singleton_iff.mp h))
  obtain ⟨D, Q, hD, hDC, hxDQ, _, hopen⟩ :=
    K.exists_convex_frontier_disk_of_compact_with_open_interior hK hC hcv hne hKC
      hdim p (isCompact_singleton (x := (e x : F)))
      (singleton_subset_iff.mpr (e x).property) hpx'
  have hcopy := he
  obtain ⟨f, _, hf⟩ := hcopy
  let d := s ∩ f ⁻¹' D
  let q := s ∩ f ⁻¹' Q
  have hd : IsFinitePLBallPair V d q := he.preimage_ballPair hD hDC hf
  have hx : (x : E) ∈ d \ q := by
    have hx' := hxDQ (mem_singleton (e x : F))
    refine ⟨⟨x.property, ?_⟩, ?_⟩
    · change f x ∈ D
      rw [← hf]
      exact hx'.1
    · intro hxq
      apply hx'.2
      rw [hf x]
      exact hxq.2
  refine ⟨d, q, hd, inter_subset_left, hx, ?_⟩
  have heq : (Subtype.val : s → E) ⁻¹' (d \ q) =
      e ⁻¹' ((Subtype.val : frontier C → F) ⁻¹' (D \ Q)) := by
    ext y
    change (((y : E) ∈ s ∧ f y ∈ D) ∧ ¬ ((y : E) ∈ s ∧ f y ∈ Q)) ↔
      ((e y : F) ∈ D ∧ (e y : F) ∉ Q)
    simp only [y.property, true_and, hf]
  rw [heq]
  exact hopen.preimage e.continuous

end Homeomorph
