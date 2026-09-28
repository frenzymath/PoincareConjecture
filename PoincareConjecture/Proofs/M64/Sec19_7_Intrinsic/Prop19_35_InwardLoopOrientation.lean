import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_InwardGraphStrip
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_LoopCornerTopology
import Mathlib.Analysis.Calculus.Deriv.Shift

noncomputable section
set_option autoImplicit false

open Set Filter
open scoped Topology ContDiff
open Poincare.Topology.Plane.Curves

namespace PoincareConjecture

theorem m64Intrinsic_exists_inward_loop_orientation
    {gamma : ℝ → AnnulusCoordinates} (hg : ContDiff ℝ ∞ gamma) {T a b : ℝ}
    (hend : gamma 0 = gamma T) (hinj : InjOn gamma (Ico 0 T))
    (hab : a < b) (ha : 0 < a) (hb : b < T)
    (hregular : ∀ t ∈ Icc a b, deriv gamma t ≠ 0)
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hdisj : Disjoint U V) (hfU : frontier U = gamma '' Icc 0 T)
    (hfV : frontier V = gamma '' Icc 0 T) :
    ∃ (g : ℝ → AnnulusCoordinates) (l u : ℝ),
      (g = gamma ∨ g = fun t => gamma (T - t)) ∧
      ContDiff ℝ ∞ g ∧ g 0 = g T ∧ InjOn g (Ico 0 T) ∧
      g '' Icc 0 T = gamma '' Icc 0 T ∧
      0 < l ∧ l < u ∧ u < T ∧
      (∀ t ∈ Icc l u, deriv g t ≠ 0) ∧
      ∀ t ∈ Icc l u, ∀ᶠ r in 𝓝[>] (0 : ℝ),
        g t + r • quarterTurn (deriv g t) ∈ U := by
  obtain ⟨delta, sigma, H, hdelta, hsigma, hmap, _, _, hcollar⟩ :=
    m64Intrinsic_exists_loop_inward_normal_collar hg hend hinj hab.le ha hb hregular
      hU hV hdisj hfU hfV
  have hrsmall : ∀ᶠ r in 𝓝[>] (0 : ℝ), r ∈ Ioo (0 : ℝ) delta :=
    Ioo_mem_nhdsGT hdelta
  rcases hsigma with rfl | rfl
  · refine ⟨gamma, a, b, Or.inl rfl, hg, hend, hinj, rfl, ha, hab, hb, hregular, ?_⟩
    intro t ht
    filter_upwards [hrsmall] with r hr
    simpa only [hmap, normalStrip, one_mul] using
      (hcollar t ht r ⟨hr.1.le, hr.2.le⟩).2.2 hr.1
  · let g : ℝ → AnnulusCoordinates := fun t => gamma (T - t)
    have hT : 0 < T := ha.trans hab |>.trans hb
    have hg' : ContDiff ℝ ∞ g := hg.comp (contDiff_const.sub contDiff_id)
    have hderiv (t : ℝ) : deriv g t = -deriv gamma (T - t) :=
      deriv_comp_const_sub gamma T t
    have hinj' : InjOn g (Ico 0 T) := by
      intro x hx y hy heq
      have hxy := m64Intrinsic_loop_injOn_Ioc hT hend hinj
        ⟨by linarith [hx.2], by linarith [hx.1]⟩
        ⟨by linarith [hy.2], by linarith [hy.1]⟩ heq
      linarith
    have himage : g '' Icc 0 T = gamma '' Icc 0 T := by
      ext p
      constructor
      · rintro ⟨t, ht, rfl⟩
        exact ⟨T - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, rfl⟩
      · rintro ⟨t, ht, rfl⟩
        refine ⟨T - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, ?_⟩
        simp only [g, sub_sub_cancel]
    have hparam {t : ℝ} (ht : t ∈ Icc (T - b) (T - a)) : T - t ∈ Icc a b :=
      ⟨by linarith [ht.2], by linarith [ht.1]⟩
    refine ⟨g, T - b, T - a, Or.inr rfl, hg', ?_, hinj', himage,
      by linarith, by linarith, by linarith, ?_, ?_⟩
    · simpa only [g, sub_zero, sub_self] using hend.symm
    · intro t ht
      rw [hderiv]
      exact neg_ne_zero.mpr (hregular _ (hparam ht))
    · intro t ht
      filter_upwards [hrsmall] with r hr
      have h := (hcollar (T - t) (hparam ht) r ⟨hr.1.le, hr.2.le⟩).2.2 hr.1
      simpa only [hmap, normalStrip, g, hderiv, map_neg, smul_neg,
        neg_one_mul, neg_smul] using h

end PoincareConjecture
