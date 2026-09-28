import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.StandardOrientation
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.NestedOrientation
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.ActualOrientation

noncomputable section
set_option autoImplicit false
open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.PlaneArcs.Terminal
open SaddleLevel
private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

variable {f : S2 → E3} {M : SphereMorseReduction f} {g : S2 → E3}
  {P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g}
  {p : S2} {e : OpenPartialHomeomorph E2 S2}

theorem exists_terminal_model_lower_slices_not_preconnected
    (d : TerminalSaddleGeometry M P p e)
    (hform : ∀ x ∈ e.source, inner Real (M.v : E3) (g (e x)) =
      inner Real (M.v : E3) (g p) - x 0 ^ 2 + x 1 ^ 2) :
    ∃ ε : Real, 0 < ε ∧ ∀ s ∈ Ioo (0 : Real) ε,
      ¬ IsPreconnected (d.B (inner Real (M.v : E3) (g p) - s)) := by
  rcases d.model_kind with hmodel | hmodel
  · refine ⟨d.scale / 4, div_pos d.scale_pos (by norm_num), ?_⟩
    intro s hs
    have ht : 0 < s / d.scale := div_pos hs.1 d.scale_pos
    have htu : s / d.scale < 1 / 4 := (div_lt_iff₀ d.scale_pos).mpr (by linarith [hs.2])
    have h := terminal_standard_lower_slice_not_preconnected d hmodel hform ht htu
    have he : d.scale * (s / d.scale) = s := by field_simp [ne_of_gt d.scale_pos]
    rwa [he] at h
  · obtain ⟨ε, hε, h⟩ := exists_terminal_nested_lower_slices_not_preconnected d hmodel hform
    refine ⟨ε, hε, ?_⟩
    intro s hs
    simpa only [sub_eq_add_neg] using h (-s) ⟨by linarith [hs.2], neg_lt_zero.mpr hs.1⟩

theorem exists_unmatched_terminal_slice_of_connected_lower_levels
    (hg : g ∈ M.tree.leaves) (d : TerminalSaddleGeometry M P p e)
    (hform : ∀ x ∈ e.source, inner Real (M.v : E3) (g (e x)) =
      inner Real (M.v : E3) (g p) - x 0 ^ 2 + x 1 ^ 2)
    {ε : Real} (hε : 0 < ε)
    (hactual : ∀ s ∈ Ioo (0 : Real) ε,
      IsPreconnected {q : S2 | inner Real (M.v : E3) (g q) =
        inner Real (M.v : E3) (g p) - s}) :
    ∃ z ∈ d.I, ¬ ∃ Q : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
      Q '' d.A z = d.B z := by
  obtain ⟨δ, hδ, hmodel⟩ := exists_terminal_model_lower_slices_not_preconnected d hform
  let s := min d.eta (min ε δ) / 2
  have hs : 0 < s := div_pos (lt_min d.eta_pos (lt_min hε hδ)) (by norm_num)
  have hsη : s < d.eta := by
    have := min_le_left d.eta (min ε δ)
    dsimp [s] at hs ⊢
    linarith
  have hsε : s < ε := by
    have := (min_le_right d.eta (min ε δ)).trans (min_le_left ε δ)
    dsimp [s] at hs ⊢
    linarith
  have hsδ : s < δ := by
    have := (min_le_right d.eta (min ε δ)).trans (min_le_right ε δ)
    dsimp [s] at hs ⊢
    linarith
  refine ⟨inner Real (M.v : E3) (g p) - s, ?_, ?_⟩
  · change d.ends.lowerCut ≤ _ ∧ _ ≤ d.ends.upperCut
    rw [d.lowerCut_eq, d.upperCut_eq]
    constructor <;> linarith [d.eta_pos]
  · rintro ⟨Q, hQ⟩
    have hA := (actual_slice_preconnected_iff hg d _).mpr (hactual s ⟨hs, hsε⟩)
    have hB := hA.image Q Q.continuous.continuousOn
    rw [hQ] at hB
    exact hmodel s ⟨hs, hsδ⟩ hB

theorem exists_unmatched_terminal_slice_of_one_lower_end
    (hg : g ∈ M.tree.leaves) (d : TerminalSaddleGeometry M P p e)
    (hunique : ∀ q ∈ P.core,
      mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => inner Real (M.v : E3) (g q)) q = 0 → q = p)
    (hform : ∀ x ∈ e.source, inner Real (M.v : E3) (g (e x)) =
      inner Real (M.v : E3) (g p) - x 0 ^ 2 + x 1 ^ 2)
    (hcount : Nat.card d.ends.LowerCutIndex = 1) :
    ∃ z ∈ d.I, ¬ ∃ Q : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
      Q '' d.A z = d.B z := by
  apply exists_unmatched_terminal_slice_of_connected_lower_levels hg d hform d.eta_pos
  intro s hs
  apply (actual_slice_preconnected_iff hg d _).mp
  have h := actual_negative_slices_preconnected_of_one_end hg d hunique hcount
    (t := -s) ⟨by linarith [hs.2], neg_lt_zero.mpr hs.1⟩
  simpa only [sub_eq_add_neg] using h

end Poincare.Manifold.Schoenflies.PlaneArcs.Terminal
