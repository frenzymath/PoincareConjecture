import PoincareLib.Geometry.CurveShortening.Comparison.IntrinsicComparison.Cap.RadialCoverage
import PoincareLib.Geometry.CurveShortening.Comparison.IntrinsicComparison.Chosen.CapGeometry

/-!
# Coverage along the original axes of a chosen cap

The literal radial boundary identities supply the original loop edge and
its interior parameter. The cap is realized without changing its map.

Morgan--Tian context: Proposition 19.35, printed pp. 467-481, including Claim 19.40,
pp. 470-471. These project constructions supply actual occupied boundary collars
and attachment coverage for the regional Gauss--Bonnet argument.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold
open PoincareMT.Topology.Surface

namespace PoincareMT

/-- The retained coordinate cap covers the actual Jordan closure near every strict interior
point of either original radial loop arc. Source:
`proof-work/tasks/M64/reports/2026-09-24-short-cap-band-join.md`. -/
theorem m64Intrinsic_chosen_cap_covers_original_axis
    {gamma : ℝ → AnnulusCoordinates} (hg : ContDiff ℝ ∞ gamma) {T r : ℝ}
    (hr : 0 < r) (hrT : r < T)
    (hend : gamma 0 = gamma T) (hinj : InjOn gamma (Ico 0 T))
    (hregular : ∀ t ∈ Ioo (0 : ℝ) T, deriv gamma t ≠ 0)
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hdisj : Disjoint U V) (hfU : frontier U = gamma '' Icc 0 T)
    (hfV : frontier V = gamma '' Icc 0 T)
    (F : OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates)
    (hsource : {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r} ⊆ F.source)
    (hF : ContDiffOn ℝ ∞ F F.source) (hFi : ContDiffOn ℝ ∞ F.symm F.target)
    (hsub : F '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r} ⊆ closure U)
    (terminal : Bool)
    (haxis : ∀ s ∈ Icc (0 : ℝ) r,
      F (if terminal then (0, s) else (s, 0)) = gamma (if terminal then T - s else s)) :
    ∀ s ∈ Ioo (0 : ℝ) r, ∃ W : Set AnnulusCoordinates,
      IsOpen W ∧ gamma (if terminal then T - s else s) ∈ W ∧
      W ∩ closure U ⊆ F '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r} := by
  obtain ⟨face, hc, _, hone, htwo, C, basis, _, _, hs, hcarrier, hboundary⟩ :=
    m64Intrinsic_exists_coordinate_face_of_chosen_cap F hr hsource hF hFi
  let k : Fin 3 := if terminal then 1 else 2
  have hedge (t : ℝ) : (face.boundary k).map t =
      F (if terminal then (0, t * r) else (t * r, 0)) := by
    cases terminal
    · exact htwo t
    · exact hone t
  have hedgeLoop : (face.boundary k).map '' Icc (0 : ℝ) 1 ⊆ gamma '' Icc 0 T := by
    rintro z ⟨t, ht, rfl⟩
    have htr : t * r ∈ Icc (0 : ℝ) r :=
      ⟨mul_nonneg ht.1 hr.le, by nlinarith [ht.2]⟩
    rw [hedge, haxis _ htr]
    refine ⟨if terminal then T - t * r else t * r, ?_, rfl⟩
    cases terminal
    · exact ⟨htr.1, htr.2.trans hrT.le⟩
    · change T - t * r ∈ Icc (0 : ℝ) T
      exact ⟨by linarith [htr.2], by linarith [htr.1]⟩
  intro s hsr
  have hp : (if terminal then T - s else s) ∈ Ioo (0 : ℝ) T := by
    cases terminal
    · exact ⟨hsr.1, hsr.2.trans hrT⟩
    · change T - s ∈ Ioo (0 : ℝ) T
      exact ⟨by linarith [hsr.2], by linarith [hsr.1]⟩
  have hparam : s / r ∈ Ioo (0 : ℝ) 1 :=
    ⟨div_pos hsr.1 hr, (div_lt_one hr).mpr hsr.2⟩
  have hpoint : (face.boundary k).map (s / r) = gamma (if terminal then T - s else s) := by
    rw [hedge, div_mul_cancel₀ _ hr.ne', haxis s (Ioo_subset_Icc_self hsr)]
  obtain ⟨W, hW, hpW, hcover⟩ := m64Intrinsic_coordinate_face_covers_loop_near_edge
    hg hend hinj hregular hp hU hV hdisj hfU hfV face C basis hs hcarrier hboundary
      (hc ▸ hsub) k hedgeLoop hparam hpoint
  exact ⟨W, hW, hpW, hc ▸ hcover⟩

end PoincareMT
