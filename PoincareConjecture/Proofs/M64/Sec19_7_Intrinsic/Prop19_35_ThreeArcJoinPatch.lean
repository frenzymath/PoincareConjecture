import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ThreeArcCapAvoidance
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_StraightJoinCoveredBands

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff
open Poincare.Topology.Plane.Curves PoincareConjecture.Topology.Surface

namespace PoincareConjecture

theorem m64Intrinsic_exists_three_arc_join_patch
    {alpha beta sigma : ℝ → AnnulusCoordinates}
    (ha : ContDiff ℝ ∞ alpha) (hb : ContDiff ℝ ∞ beta) (hs : Continuous sigma)
    {A B T r0 r1 c : ℝ} (hA : 0 < A) (hB : 0 < B) (hT : 0 < T) (hc : 0 < c)
    (hr0 : r0 ≤ min A T / 3) (hr1 : r1 ≤ min B T / 3)
    (hai : InjOn alpha (Icc 0 A)) (hbi : InjOn beta (Icc 0 B))
    (hend : alpha A = beta 0) (hreg : deriv alpha A ≠ 0)
    (htan : deriv beta 0 = c • deriv alpha A)
    (hab : ∀ x ∈ Icc 0 A, ∀ y ∈ Icc 0 B,
      alpha x = beta y → x = A ∧ y = 0)
    (has : ∀ x ∈ Icc 0 A, ∀ y ∈ Icc 0 T,
      alpha x = sigma y → x = 0 ∧ y = 0)
    (hbs : ∀ x ∈ Icc 0 B, ∀ y ∈ Icc 0 T,
      beta x = sigma y → x = B ∧ y = T)
    (hregular : ∀ t ∈ Ioo (0 : ℝ) A, deriv alpha t ≠ 0)
    {U V D0 D1 : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hUV : Disjoint U V)
    (hfront : frontier U = alpha '' Icc 0 A ∪ beta '' Icc 0 B ∪ sigma '' Icc 0 T)
    (hfV : frontier V = frontier U)
    (hray : ∀ t ∈ Ioo (0 : ℝ) A, ∀ᶠ r in 𝓝[>] (0 : ℝ),
      alpha t + r • quarterTurn (deriv alpha t) ∈ U)
    (hD0 : IsCompact D0) (hD1 : IsCompact D1)
    (hcontact0 : D0 ∩ frontier U ⊆ alpha '' Icc 0 r0 ∪ sigma '' Icc 0 r0)
    (hcontact1 : D1 ∩ frontier U ⊆
      (fun s => beta (B - s)) '' Icc 0 r1 ∪
      (fun s => sigma (T - s)) '' Icc 0 r1) :
    let w := quarterTurn (deriv alpha A)
    Disjoint D0 (beta '' Icc 0 B) ∧ Disjoint D1 (alpha '' Icc 0 A) ∧
    ∃ epsilon > 0, r0 < A - epsilon ∧ epsilon < B - r1 ∧
      0 < A - epsilon ∧ epsilon < B ∧
      ∃ (L R : (ℝ × ℝ) ≃L[ℝ] AnnulusCoordinates) (f g : ℝ → ℝ) (a b s t : ℝ),
        a < b ∧ s < t ∧
        L (a, f a) = alpha (A - epsilon) ∧ L (b, f b) = alpha A ∧
        R (s, g s) = alpha A ∧ R (t, g t) = beta epsilon ∧
        0 < inner ℝ (quarterTurn (deriv alpha (A - epsilon))) w ∧
        0 < inner ℝ (quarterTurn (deriv beta epsilon)) w ∧
        (∃ v : ℝ, 0 < v ∧ deriv alpha (A - epsilon) = v • L (1, deriv f a)) ∧
        (∃ v : ℝ, 0 < v ∧ deriv beta epsilon = v • R (1, deriv g t)) ∧
        ∃ cutoff > 0, ∀ ra ∈ Ioo (0 : ℝ) cutoff, ∀ r ∈ Ioo (0 : ℝ) cutoff,
          ∀ rb ∈ Ioo (0 : ℝ) cutoff,
            ∃ (C : ObliqueBandFaces
              (collarParameterEquiv.trans L).toHomeomorph.toOpenPartialHomeomorph
              f a b (L.symm w).1 (L.symm w).2 (L.symm w).1 (L.symm w).2 ra r)
              (D : ObliqueBandFaces
              (collarParameterEquiv.trans R).toHomeomorph.toOpenPartialHomeomorph
              g s t (R.symm w).1 (R.symm w).2 (R.symm w).1 (R.symm w).2 r rb),
              C.lowerArc = alpha '' Icc (A - epsilon) A ∧
              D.lowerArc = beta '' Icc 0 epsilon ∧
              C.carrier ⊆ (D0 ∪ D1 ∪ sigma '' Icc 0 T)ᶜ ∧
              D.carrier ⊆ (D0 ∪ D1 ∪ sigma '' Icc 0 T)ᶜ ∧
              C.carrier ⊆ closure U ∧ D.carrier ⊆ closure U ∧
              C.carrier \ C.lowerArc ⊆ U ∧ D.carrier \ D.lowerArc ⊆ U ∧
              C.leftCut = segment ℝ (alpha (A - epsilon)) (alpha (A - epsilon) + ra • w) ∧
              C.rightCut = segment ℝ (alpha A) (alpha A + r • w) ∧
              D.leftCut = segment ℝ (alpha A) (alpha A + r • w) ∧
              D.rightCut = segment ℝ (beta epsilon) (beta epsilon + rb • w) ∧
              C.carrier ∩ D.carrier = segment ℝ (alpha A) (alpha A + r • w) ∧
              ∃ W : Set AnnulusCoordinates, IsOpen W ∧ alpha A ∈ W ∧
                W ∩ closure U ⊆ C.carrier ∪ D.carrier := by
  intro w
  obtain ⟨hsep0, hsep1, hO, hpO⟩ := m64Intrinsic_three_arc_cap_avoidance hs hA hB hT
    hr0 hr1 hend hab has hbs hfront hD0 hD1 hcontact0 hcontact1
  have hr0A : r0 < A := by
    have := hr0.trans (div_le_div_of_nonneg_right (min_le_left A T) (by norm_num : (0 : ℝ) ≤ 3))
    linarith
  have hr1B : r1 < B := by
    have := hr1.trans (div_le_div_of_nonneg_right (min_le_left B T) (by norm_num : (0 : ℝ) ≤ 3))
    linarith
  have hpK : alpha A ∉ sigma '' Icc 0 T := by
    rintro ⟨s, hs, he⟩
    exact hA.ne' (has A ⟨hA.le, le_rfl⟩ s hs he.symm).1
  obtain ⟨epsilon, hepsilon, heBound, heA, heB, hpatch⟩ :=
    m64Intrinsic_exists_straight_join_covered_bands ha hb hA hB hc
      (lt_min (sub_pos.mpr hr0A) (sub_pos.mpr hr1B)) hai hbi hend hreg htan hab hregular
      (isCompact_Icc.image hs) hpK hU hV hUV hfront hfV hray hO hpO
  have he0 : epsilon < A - r0 := heBound.trans_le (min_le_left _ _)
  have he1 : epsilon < B - r1 := heBound.trans_le (min_le_right _ _)
  refine ⟨hsep0, hsep1, epsilon, hepsilon, by linarith, he1, heA, ?_, ?_⟩
  · simpa only [zero_add] using heB
  · simpa only [zero_add] using hpatch

end PoincareConjecture
