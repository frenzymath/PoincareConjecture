import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_FittedCornerCap
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CapChordSigns

noncomputable section
set_option autoImplicit false

open Set Filter
open scoped Topology ContDiff
open Poincare.Topology.Plane.Curves

namespace PoincareConjecture

theorem m64Intrinsic_exists_convex_cap_coordinates_with_chords
    {gamma : ℝ → AnnulusCoordinates} (hg : ContDiff ℝ ∞ gamma) {T : ℝ} (hT : 0 < T)
    (hend : gamma 0 = gamma T) (hinj : InjOn gamma (Ico 0 T))
    (hregular : ∀ t ∈ Ioo (0 : ℝ) T, deriv gamma t ≠ 0)
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hdisj : Disjoint U V) (hfU : frontier U = gamma '' Icc 0 T)
    (hfV : frontier V = gamma '' Icc 0 T)
    (hray : ∀ t ∈ Ioo (0 : ℝ) T, ∀ᶠ z in 𝓝[>] (0 : ℝ),
      gamma t + z • quarterTurn (deriv gamma t) ∈ U)
    (H : OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates)
    (h0 : (0 : ℝ × ℝ) ∈ H.source) (hbase : H 0 = gamma 0)
    (hH : ContDiffOn ℝ ∞ H H.source) (hHi : ContDiffOn ℝ ∞ H.symm H.target)
    (haxis : ∀ s : ℝ, H (s, 0) = gamma s)
    (haxis' : ∀ s : ℝ, H (0, s) = gamma (T - s))
    (hside : ∀ᶠ z in 𝓝 (0 : ℝ × ℝ), H z ∈ closure U ↔ 0 ≤ z.1 ∧ 0 ≤ z.2) :
    ∃ (r : ℝ) (F : OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates)
      (W : Set AnnulusCoordinates),
      0 < r ∧ r ≤ T / 3 ∧ IsOpen W ∧ gamma 0 ∈ W ∧
      {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r} ⊆ F.source ∧
      ContDiffOn ℝ ∞ F F.source ∧ ContDiffOn ℝ ∞ F.symm F.target ∧
      (∀ s ∈ Icc (0 : ℝ) r, F (s, 0) = gamma s) ∧
      (∀ s ∈ Icc (0 : ℝ) r, F (0, s) = gamma (T - s)) ∧
      (∀ t : ℝ, F ((1 - t) * r, t * r) =
        (1 - t) • F (r, 0) + t • F (0, r)) ∧
      F '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r} ⊆ closure U ∧
      W ∩ closure U ⊆ F '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r} ∧
      0 < inner ℝ (quarterTurn (deriv gamma r)) (F (0, r) - F (r, 0)) ∧
      0 < inner ℝ (quarterTurn (deriv gamma (T - r))) (F (r, 0) - F (0, r)) := by
  obtain ⟨r, hr, hrT, F, W, hsource, hF, hFi, hfirst, hsecond, hchord,
    hsub, hW, hpW, hcover⟩ := m64Intrinsic_exists_fitted_corner_cap_coordinates_le
      H h0 hH hHi hside (show (0 : ℝ) < T / 3 by positivity)
  have hfirst' : ∀ s ∈ Icc (0 : ℝ) r, F (s, 0) = gamma s :=
    fun s hs => (hfirst s hs).trans (haxis s)
  have hsecond' : ∀ s ∈ Icc (0 : ℝ) r, F (0, s) = gamma (T - s) :=
    fun s hs => (hsecond s hs).trans (haxis' s)
  have hrI : r ∈ Icc (0 : ℝ) r := ⟨hr.le, le_rfl⟩
  have hchord' : ∀ t : ℝ, F ((1 - t) * r, t * r) =
      (1 - t) • F (r, 0) + t • F (0, r) := by
    intro t
    rw [hfirst r hrI, hsecond r hrI]
    exact hchord t
  have hsmall : r < T := hrT.trans_lt (by linarith)
  have hleft := m64Intrinsic_cap_endpoint_chord_sign hg hend hinj hregular
    hU hV hdisj hfU hfV hray hr hsmall F hsource hF hFi hchord' hsub false false hfirst'
  have hright := m64Intrinsic_cap_endpoint_chord_sign hg hend hinj hregular
    hU hV hdisj hfU hfV hray hr hsmall F hsource hF hFi hchord' hsub true true hsecond'
  exact ⟨r, F, W, hr, hrT, hW, hbase ▸ hpW, hsource, hF, hFi,
    hfirst', hsecond', hchord', hsub, hcover, hleft, hright⟩

end PoincareConjecture
