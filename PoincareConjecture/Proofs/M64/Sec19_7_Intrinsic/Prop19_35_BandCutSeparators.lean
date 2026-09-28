import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_StraightChartSeparator
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ThinGraphBands

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold
open Poincare.Topology.Plane.Curves PoincareConjecture.Topology.Surface

namespace PoincareConjecture

theorem m64Intrinsic_exists_band_cut_separator
    (L : (ℝ × ℝ) ≃L[ℝ] AnnulusCoordinates)
    {f : ℝ → ℝ} {a b ua wa ub wb ra rb : ℝ} (hab : a < b)
    (B : ObliqueBandFaces
      (collarParameterEquiv.trans L).toHomeomorph.toOpenPartialHomeomorph
      f a b ua wa ub wb ra rb)
    (right : Bool) (ell : AnnulusCoordinates →L[ℝ] ℝ)
    (hcut : ell (if right then L (ub, wb) else L (ua, wa)) = 0)
    (hpos : 0 < ell (L (1, deriv f (if right then b else a)))) :
    let p := L (if right then b else a, f (if right then b else a))
    ∃ W : Set AnnulusCoordinates, IsOpen W ∧ p ∈ W ∧
      ∀ z ∈ B.carrier ∩ W, (if right then ell else -ell) (z - p) ≤ 0 := by
  intro p
  let S := B.cuts.linearCoordinates L B.open_domain B.smooth_lower
  let t : ℝ := if right then 1 else 0
  have ht : t ∈ Icc (0 : ℝ) 1 := by cases right <;> simp [t]
  have hcoordinates (q : AnnulusCoordinates) : B.coordinates q = S (collarParameterEquiv q) := by
    change L (collarParameterEquiv (collarParameterEquiv.symm
      (B.cuts.coordinates B.open_domain B.smooth_lower (collarParameterEquiv q)))) = _
    rw [collarParameterEquiv.apply_symm_apply]
    rfl
  have hsource (q : AnnulusCoordinates) (hq : q ∈ B.band) : collarParameterEquiv q ∈ S.source :=
    ⟨(B.band_subset_source hq).1.1.2, mem_univ _⟩
  have haxis (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : (t, (0 : ℝ)) ∈ S.source :=
    B.cuts.linearCoordinates_axis_mem_source L B.open_domain B.smooth_lower
      hab B.interval_subset ht
  have hbase : S (t, 0) = p := by
    rw [B.cuts.linearCoordinates_axis]
    cases right <;> simp [t, p]
  have hS : ContDiffAt ℝ 1 S (t, 0) :=
    (((B.cuts.smooth_linearCoordinates L B.open_domain B.smooth_lower) _ (haxis t ht)).contDiffAt
      (S.open_source.mem_nhds (haxis t ht))).of_le (by simp)
  have hd : 0 < ell (fderiv ℝ S (t, 0) (1, 0)) := by
    rw [B.cuts.linearCoordinates_axis_fderiv L B.open_domain B.smooth_lower
      hab B.interval_subset ht, map_smul, smul_eq_mul]
    apply mul_pos (sub_pos.mpr hab)
    cases right <;> simpa [t] using hpos
  have hzero : ∀ᶠ z in 𝓝 (0 : ℝ), ell (S (t, z) - S (t, 0)) = 0 := by
    filter_upwards [isOpen_Ioo.mem_nhds (show (0 : ℝ) ∈ Ioo (-B.cuts.radius) B.cuts.radius from
      ⟨neg_lt_zero.mpr B.cuts.radius_pos, B.cuts.radius_pos⟩)] with z hz
    rw [hbase]
    cases right
    · change ell (S (0, z) - L (a, f a)) = 0
      change ell (L (ua, wa)) = 0 at hcut
      rw [B.cuts.linearCoordinates_left L B.open_domain B.smooth_lower hz,
        add_sub_cancel_left, map_smul, hcut, smul_zero]
    · change ell (S (1, z) - L (b, f b)) = 0
      change ell (L (ub, wb)) = 0 at hcut
      rw [B.cuts.linearCoordinates_right L B.open_domain B.smooth_lower hz,
        add_sub_cancel_left, map_smul, hcut, smul_zero]
  obtain ⟨W, hW, hpW, _, hsign⟩ := m64Intrinsic_exists_straight_chart_separator
    S (haxis t ht) hS ell hd hzero
  refine ⟨W, hW, hbase ▸ hpW, ?_⟩
  intro z hz
  obtain ⟨q, hq, rfl⟩ := B.carrier_eq_image ▸ hz.1
  have hi : (S.symm (B.coordinates q)).1 ∈ Icc (0 : ℝ) 1 := by
    rw [hcoordinates, S.left_inv (hsource q hq)]
    exact (B.band_eq_subgraph ▸ hq).1
  cases right
  · have hle := (hsign _ hz.2).2.2.mpr hi.1
    simpa only [hbase, Bool.false_eq_true, ↓reduceIte, neg_apply,
      neg_nonpos] using hle
  · have hle : ell (B.coordinates q - S (t, 0)) ≤ 0 :=
      le_of_not_gt (fun h => (not_lt_of_ge hi.2) ((hsign _ hz.2).1.mp h))
    simpa only [hbase, ↓reduceIte] using hle

end PoincareConjecture
