import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.LevelGraph.Resolution.Strips.Contacts



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.SaddleLevel

private abbrev E2 := EuclideanSpace Real (Fin 2)


def movingContactCoordinate {M : Type*} [TopologicalSpace M]
    (e : OpenPartialHomeomorph E2 M)
    (F : OpenPartialHomeomorph (Real × Real) M)
    (r : Real) (j : Fin 2 × Fin 2) (t : Real) : Real :=
  (F.symm (e (movingContact r t j))).1

theorem movingContactCoordinate_zero {M : Type*} [TopologicalSpace M]
    (e : OpenPartialHomeomorph E2 M)
    (F : OpenPartialHomeomorph (Real × Real) M)
    {r s : Real} (hr : 0 < r) (j : Fin 2 × Fin 2)
    (hs : (s, 0) ∈ F.source) (hcontact : F (s, 0) = e (contact r j)) :
    movingContactCoordinate e F r j 0 = s := by
  simp only [movingContactCoordinate, movingContact_zero hr, ← hcontact, F.left_inv hs]




theorem exists_movingContactCoordinate_band {M : Type*} [TopologicalSpace M]
    {h : M → Real} {c r a b s : Real}
    (e : OpenPartialHomeomorph E2 M)
    (F : OpenPartialHomeomorph (Real × Real) M)
    (hr : 0 < r) (hrs : closedSquare r ⊆ e.source)
    (hform : ∀ x ∈ e.source, h (e x) = c - x 0 ^ 2 + x 1 ^ 2)
    (hheight : ∀ z ∈ F.source, h (F z) = c + z.2)
    (j : Fin 2 × Fin 2) (hs : (s, 0) ∈ F.source)
    (has : a < s) (hsb : s < b)
    (hcontact : F (s, 0) = e (contact r j)) :
    ∃ δ : Real, 0 < δ ∧ δ < r ^ 2 ∧
      movingContactCoordinate e F r j 0 = s ∧
      ∀ t ∈ Icc (-δ) δ,
        ContinuousAt (movingContactCoordinate e F r j) t ∧
        movingContactCoordinate e F r j t ∈ Ioo a b ∧
        (movingContactCoordinate e F r j t, t) ∈ F.source ∧
        F (movingContactCoordinate e F r j t, t) = e (movingContact r t j) := by
  let q : Real → M := fun t => e (movingContact r t j)
  let u : Real → Real := movingContactCoordinate e F r j
  have hq0 : q 0 = F (s, 0) := by simp [q, movingContact_zero hr, hcontact]
  have hcsource : movingContact r 0 j ∈ e.source := by
    rw [movingContact_zero hr]
    exact hrs (contact_mem hr j).1.1
  have hqcont : ContinuousAt q 0 :=
    (e.continuousOn.continuousAt (e.open_source.mem_nhds hcsource)).comp
      (f := fun t => movingContact r t j)
      (continuous_movingContact r j).continuousAt
  have hqtarget : q 0 ∈ F.target := hq0 ▸ F.map_source hs
  have hucont : ContinuousAt u 0 :=
    ((F.continuousOn_symm.continuousAt (F.open_target.mem_nhds hqtarget)).comp hqcont).fst
  have hu0 : u 0 = s := movingContactCoordinate_zero e F hr j hs hcontact
  have hnear : ∀ᶠ t in 𝓝 (0 : Real), q t ∈ F.target ∧ u t ∈ Ioo a b := by
    filter_upwards [hqcont.eventually (F.open_target.mem_nhds hqtarget),
      hucont.eventually (isOpen_Ioo.mem_nhds (hu0 ▸ And.intro has hsb))] with t ht hu
    exact ⟨ht, hu⟩
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hnear
  let δ := min ε (r ^ 2) / 2
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
  have hδ : 0 < δ := half_pos (lt_min hε hr2)
  have hδε : δ < ε := (half_lt_self (lt_min hε hr2)).trans_le (min_le_left _ _)
  have hδr : δ < r ^ 2 := (half_lt_self (lt_min hε hr2)).trans_le (min_le_right _ _)
  refine ⟨δ, hδ, hδr, hu0, ?_⟩
  intro t ht
  have htδ : |t| ≤ δ := abs_le.mpr ht
  have htr : |t| < r ^ 2 := htδ.trans_lt hδr
  have htε : t ∈ ball (0 : Real) ε := by
    rw [mem_ball_zero_iff, Real.norm_eq_abs]
    exact htδ.trans_lt hδε
  have htnear := hεsub htε
  have htsource : movingContact r t j ∈ e.source :=
    hrs (movingContact_mem_boundary hr htr j).1
  have hqtcont : ContinuousAt q t :=
    (e.continuousOn.continuousAt (e.open_source.mem_nhds htsource)).comp
      (f := fun t => movingContact r t j)
      (continuous_movingContact r j).continuousAt
  have hutcont : ContinuousAt u t :=
    ((F.continuousOn_symm.continuousAt (F.open_target.mem_nhds htnear.1)).comp hqtcont).fst
  have hright : F (F.symm (q t)) = q t := F.right_inv htnear.1
  have hcoordsource := F.map_target htnear.1
  have hsnd : (F.symm (q t)).2 = t := by
    have hh := hheight _ hcoordsource
    rw [hright] at hh
    have hqheight : h (q t) = c + t := by
      rw [hform _ htsource]
      have hlev := movingContact_height hr htr j
      linarith
    linarith
  have hpair : F.symm (q t) = (u t, t) := Prod.ext rfl hsnd
  refine ⟨hutcont, htnear.2, ?_, ?_⟩
  · exact hpair ▸ hcoordsource
  · exact hpair ▸ hright

end Poincare.Manifold.Schoenflies.SaddleLevel
