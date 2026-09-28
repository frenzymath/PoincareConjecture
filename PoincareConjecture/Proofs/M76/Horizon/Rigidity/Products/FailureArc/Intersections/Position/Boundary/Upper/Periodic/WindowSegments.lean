import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Boundary.Upper.Periodic.WindowGraph
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Boundary.Upper.Periodic.GraphEdges

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.PeriodicSquare

theorem exists_finite_periodic_window_segments
    {p : ℝ} (hp : 0 < p) {r : ℝ → ℝ × ℝ}
    (hr : FinitePiecewiseAffineOn r (Icc (0 : ℝ) 1))
    (hfib : ∀ s t : unitInterval,
      (((r s).1 : AddCircle p), ((r s).2 : AddCircle p)) =
        (((r t).1 : AddCircle p), ((r t).2 : AddCircle p)) ↔
      s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0))
    {W : Set (ℝ × ℝ)} (hW : IsCompact W) :
    ∃ (I : Type) (_ : Finite I) (a b : I → ℝ × ℝ),
      (∀ i, a i ≠ b i) ∧
      (∀ i j, i ≠ j →
        segment ℝ (a i) (b i) ∩ segment ℝ (a j) (b j) ⊆ {a i, b i}) ∧
      ∀ z ∈ W, ((z.1 : AddCircle p), (z.2 : AddCircle p)) ∈
        (fun t => (((r t).1 : AddCircle p), ((r t).2 : AddCircle p))) '' Icc (0 : ℝ) 1 ↔
        z ∈ ⋃ i, segment ℝ (a i) (b i) := by
  have hne : r 0 ≠ r (1 / 2) := by
    intro h
    have hh := (hfib 0 ⟨1 / 2, by constructor <;> norm_num⟩).mp
      (congrArg (fun z : ℝ × ℝ => ((z.1 : AddCircle p), (z.2 : AddCircle p))) h)
    rcases hh with hh | ⟨_, hh⟩ | ⟨hh, _⟩ <;>
      have ht := congrArg Subtype.val hh <;> norm_num at ht
  have hnontriv : (r '' Icc (0 : ℝ) 1).Nontrivial :=
    ⟨r 0, mem_image_of_mem r (by constructor <;> norm_num),
      r (1 / 2), mem_image_of_mem r (by constructor <;> norm_num), hne⟩
  obtain ⟨L, hL, hdim, hacc, hwindow⟩ := exists_finite_periodic_window_graph hp hr hnontriv hW
  obtain ⟨I, hI, a, b, hab, hspace, hself⟩ := exists_segment_family_of_preperfect L hL hdim hacc
  exact ⟨I, hI, a, b, hab, hself, fun z hz => (hwindow z hz).trans (by rw [hspace])⟩

end PoincareConjecture.M76.PeriodicSquare
