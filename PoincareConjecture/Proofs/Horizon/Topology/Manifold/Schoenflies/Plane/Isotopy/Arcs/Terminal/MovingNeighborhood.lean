import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.LevelGraph.Coordinates
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Topology.Compactness.Compact

noncomputable section
set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.PlaneArcs.Terminal

open SaddleLevel

private abbrev E2 := EuclideanSpace Real (Fin 2)

private theorem uniform_compact_image_in_open
    (F : Real × E2 → E2) (hF : Continuous F)
    {C O : Set E2} (hC : IsCompact C) (hO : IsOpen O)
    (hzero : ∀ x ∈ C, F (0, x) ∈ O) :
    ∃ δ > 0, ∀ t : Real, |t| ≤ δ → ∀ x ∈ C, F (t, x) ∈ O := by
  obtain ⟨T, V, hT, _, h0T, hCV, hTV⟩ := generalized_tube_lemma
    (isCompact_singleton : IsCompact ({0} : Set Real)) hC (hO.preimage hF)
    (by rintro ⟨t, x⟩ ⟨ht, hx⟩; have ht0 : t = 0 := ht; subst t; exact hzero x hx)
  obtain ⟨δ, hδ, hδT⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hT.mem_nhds (h0T rfl))
  refine ⟨δ, hδ, ?_⟩
  intro t ht x hx
  apply hTV (a := (t, x))
  refine ⟨hδT ?_, hCV hx⟩
  simpa only [mem_closedBall, Real.dist_eq, sub_zero] using ht

theorem exists_uniform_moving_image_subset_open
    (Q : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (hQ : Continuous (fun z : Real × E2 => Q z.1 z.2))
    {C O : Set E2} (hC : IsCompact C) (hO : IsOpen O)
    (hzero : Q 0 '' C ⊆ O) :
    ∃ δ > 0, ∀ t : Real, |t| ≤ δ → Q t '' C ⊆ O := by
  obtain ⟨δ, hδ, hδO⟩ := uniform_compact_image_in_open _ hQ hC hO
    (fun x hx => hzero (mem_image_of_mem _ hx))
  refine ⟨δ, hδ, ?_⟩
  intro t ht y hy
  obtain ⟨x, hx, rfl⟩ := hy
  exact hδO t ht x hx

theorem exists_uniform_compact_subset_moving_image
    (Q : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (hQi : Continuous (fun z : Real × E2 => (Q z.1).symm z.2))
    {C O : Set E2} (hC : IsCompact C) (hO : IsOpen O)
    (hzero : C ⊆ Q 0 '' O) :
    ∃ δ > 0, ∀ t : Real, |t| ≤ δ → C ⊆ Q t '' O := by
  obtain ⟨δ, hδ, hδO⟩ := uniform_compact_image_in_open _ hQi hC hO (by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hzero hx
    simpa only [(Q 0).symm_apply_apply] using hy)
  refine ⟨δ, hδ, ?_⟩
  intro t ht x hx
  exact ⟨(Q t).symm x, hδO t ht x hx, (Q t).apply_symm_apply x⟩

theorem exists_uniform_moving_square_and_compact_containment
    (Q : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (hQ : Continuous (fun z : Real × E2 => Q z.1 z.2))
    (hQi : Continuous (fun z : Real × E2 => (Q z.1).symm z.2))
    {r a : Real} (hr : 0 < r) (hra : r < a)
    {C : Set E2} (hC : IsCompact C) (hCinside : C ⊆ Q 0 '' openSquare a) :
    ∃ δ > 0, ∀ t : Real, |t| ≤ δ →
      Q t '' closedSquare r ⊆ Q 0 '' openSquare a ∧ C ⊆ Q t '' openSquare a := by
  have hsquare : closedSquare r ⊆ openSquare a :=
    fun x hx => ⟨hx.1.trans_lt hra, hx.2.trans_lt hra⟩
  obtain ⟨δ₁, hδ₁, hforward⟩ := exists_uniform_moving_image_subset_open Q hQ
    (isCompact_closedSquare hr.le) ((Q 0).toHomeomorph.isOpenMap _ (isOpen_openSquare a))
    (image_mono hsquare)
  obtain ⟨δ₂, hδ₂, hbackward⟩ := exists_uniform_compact_subset_moving_image Q hQi
    hC (isOpen_openSquare a) hCinside
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
  intro t ht
  exact ⟨hforward t (ht.trans (min_le_left _ _)), hbackward t (ht.trans (min_le_right _ _))⟩

theorem exists_uniform_moving_square_containment
    (Q : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (hQ : Continuous (fun z : Real × E2 => Q z.1 z.2))
    (hQi : Continuous (fun z : Real × E2 => (Q z.1).symm z.2))
    {r a : Real} (hr : 0 < r) (hra : r < a) :
    ∃ δ > 0, ∀ t : Real, |t| ≤ δ →
      Q t '' closedSquare r ⊆ Q 0 '' openSquare a ∧
        Q 0 '' closedSquare r ⊆ Q t '' openSquare a := by
  apply exists_uniform_moving_square_and_compact_containment Q hQ hQi hr hra
    ((isCompact_closedSquare hr.le).image (Q 0).continuous)
  exact image_mono (fun x hx => ⟨hx.1.trans_lt hra, hx.2.trans_lt hra⟩)

end Poincare.Manifold.Schoenflies.PlaneArcs.Terminal
