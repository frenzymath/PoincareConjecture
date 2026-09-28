import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ThreeArcReverseData
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_JoinedInwardSign

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Matrix
open Poincare.Topology.Plane.Curves PoincareConjecture.Topology.Surface

namespace PoincareConjecture

theorem m64Intrinsic_exists_three_arc_triangulation
    (gamma : Bool → ℝ → AnnulusCoordinates) (sigma : ℝ → AnnulusCoordinates)
    (T : Bool → ℝ) {S speed : ℝ} (hg : ∀ e, ContDiff ℝ ∞ (gamma e))
    (hs : ContDiff ℝ ∞ sigma) (hT : ∀ e, 0 < T e) (hS : 0 < S) (hspeed : 0 < speed)
    (hinj : ∀ e, InjOn (gamma e) (Icc 0 (T e))) (hsi : InjOn sigma (Icc 0 S))
    (hstart : sigma 0 = gamma false 0) (hend : sigma S = gamma true (T true))
    (hjoin : gamma false (T false) = gamma true 0)
    (hreg : deriv (gamma false) (T false) ≠ 0)
    (htan : deriv (gamma true) 0 = speed • deriv (gamma false) (T false))
    (hab : ∀ x ∈ Icc 0 (T false), ∀ y ∈ Icc 0 (T true),
      gamma false x = gamma true y → x = T false ∧ y = 0)
    (has : ∀ x ∈ Icc 0 (T false), ∀ y ∈ Icc 0 S,
      gamma false x = sigma y → x = 0 ∧ y = 0)
    (hbs : ∀ x ∈ Icc 0 (T true), ∀ y ∈ Icc 0 S,
      gamma true x = sigma y → x = T true ∧ y = S)
    (hregular : ∀ e, ∀ t ∈ Ioo 0 (T e), deriv (gamma e) t ≠ 0)
    (hsreg : ∀ t ∈ Ioo 0 S, deriv sigma t ≠ 0)
    (hind0 : LinearIndependent ℝ
      (![deriv (gamma false) 0, deriv sigma 0] : Fin 2 → AnnulusCoordinates))
    (hind1 : LinearIndependent ℝ
      (![-deriv (gamma true) (T true), -deriv sigma S] : Fin 2 → AnnulusCoordinates))
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V)
    (hfront : frontier U = gamma false '' Icc 0 (T false) ∪
      gamma true '' Icc 0 (T true) ∪ sigma '' Icc 0 S)
    (hfV : frontier V = frontier U) (hcompact : IsCompact (closure U)) :
    ∃ R : M64IntrinsicCoordinateTriangulation (closure U),
      ∃ v0 vj v1 : Euler.CoordinateVertex R.coordinates R.basis,
        v0.1 = gamma false 0 ∧ vj.1 = gamma false (T false) ∧ v1.1 = gamma true (T true) ∧
        ∀ g : RiemannianMetric 2 AnnulusCoordinates,
          coordinateVertexAngleContribution g R.coordinates R.basis vj.1 = Real.pi := by
  have hpK : gamma false (T false) ∉ sigma '' Icc 0 S := by
    rintro ⟨y, hy, he⟩
    exact (hT false).ne' (has (T false) ⟨(hT false).le, le_rfl⟩ y hy he.symm).1
  have havoid0 (x : ℝ) (hx : x ∈ Ioo 0 (T false)) :
      gamma false x ∉ sigma '' Icc 0 S := by
    rintro ⟨y, hy, he⟩
    exact hx.1.ne' (has x (Ioo_subset_Icc_self hx) y hy he.symm).1
  have havoid1 (x : ℝ) (hx : x ∈ Ioo 0 (T true)) :
      gamma true x ∉ sigma '' Icc 0 S := by
    rintro ⟨y, hy, he⟩
    exact hx.2.ne (hbs x (Ioo_subset_Icc_self hx) y hy he.symm).1
  obtain ⟨sign, hsign, hray0, hray1⟩ := m64Intrinsic_exists_straight_join_inward_sign
    (hg false) (hg true) (hT false) (hT true) hspeed (hinj false) (hinj true)
    hjoin hreg htan hab (hregular false) (hregular true)
    (isCompact_Icc.image hs.continuous) hpK havoid0 havoid1 hU hV hUV hfront hfV
  rcases hsign with rfl | rfl
  · apply m64Intrinsic_exists_three_arc_triangulation_with_straight_fan gamma sigma T
      hg hs hT hS hspeed hinj hsi hstart hend hjoin hreg htan hab has hbs hregular hsreg
      hind0 hind1 hU hV hUV hfront hfV hcompact
    intro e
    cases e
    · simpa only [one_smul] using hray0
    · simpa only [one_smul] using hray1
  · have hray (e : Bool) : ∀ t ∈ Ioo 0 (T e), ∀ᶠ r in 𝓝[>] (0 : ℝ),
        gamma e t + r • ((-1 : ℝ) • quarterTurn (deriv (gamma e) t)) ∈ U := by
      cases e
      · exact hray0
      · exact hray1
    let g (e : Bool) (t : ℝ) := gamma (!e) (T (!e) - t)
    let s (t : ℝ) := sigma (S - t)
    let L (e : Bool) := T (!e)
    obtain ⟨hg', hs', hgi, hsi', hstart', hend', hjoin', hreg', htan', hab', has', hbs',
        hregular', hsreg', hind0', hind1', hfront', hray'⟩ :=
      m64Intrinsic_three_arc_reverse_data gamma sigma T hg hs hspeed hinj hsi
        hstart hend hjoin hreg htan hab has hbs hregular hsreg hind0 hind1 hfront hray
    obtain ⟨R, v0, vj, v1, hv0, hvj, hv1, hfan⟩ :=
      m64Intrinsic_exists_three_arc_triangulation_with_straight_fan g s L hg' hs'
        (fun e => hT (!e)) hS (inv_pos.mpr hspeed) hgi hsi' hstart' hend' hjoin' hreg'
        htan' hab' has' hbs' hregular' hsreg' hind0' hind1' hU hV hUV hfront' hfV hcompact hray'
    refine ⟨R, v1, vj, v0, ?_, ?_, ?_, hfan⟩
    · simpa only [g, L, Bool.not_true, sub_self] using hv1
    · have hjoinVertex : vj.1 = gamma true 0 := by
        simpa only [g, L, Bool.not_false, sub_self] using hvj
      exact hjoinVertex.trans hjoin.symm
    · simpa only [g, Bool.not_false, sub_zero] using hv0

end PoincareConjecture
