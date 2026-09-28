import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ContactBaseOrientation
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_LastContactRegion









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff

namespace PoincareConjecture





theorem m64Intrinsic_exists_oriented_last_contact_region
    {base alpha beta eta : ℝ → AnnulusCoordinates}
    (hb : ContDiff ℝ ∞ base) (ha : ContDiff ℝ ∞ alpha) (hc : ContDiff ℝ ∞ beta)
    (he : ContDiff ℝ ∞ eta) {D A B p u L c : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hp : p ∈ Ioo 0 D) (huL : u < L)
    (hbi : InjOn base (Icc 0 D)) (hai : InjOn alpha (Icc 0 A))
    (hci : InjOn beta (Icc 0 B)) (hei : InjOn eta (Icc u L))
    (hstartA : base 0 = alpha 0) (hstartB : base D = beta 0)
    (hmeet : alpha A = beta B) (heu : eta u = base p) (heL : eta L = alpha A)
    (hbaseA : ∀ x ∈ Icc 0 D, ∀ t ∈ Icc 0 A, base x = alpha t → x = 0 ∧ t = 0)
    (hbaseB : ∀ x ∈ Icc 0 D, ∀ t ∈ Icc 0 B, base x = beta t → x = D ∧ t = 0)
    (hcne : c ≠ 0) (htangent : deriv eta u = c • deriv base p)
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hpV : IsPreconnected V) (hbV : ¬ Bornology.IsBounded V) (hd : Disjoint U V)
    (hcover : U ∪ V = (frontier U)ᶜ) (hfV : frontier V = frontier U)
    (hfU : frontier U = base '' Icc 0 D ∪ (alpha '' Icc 0 A ∪ beta '' Icc 0 B))
    (hinside : MapsTo eta (Ioo u L) U) :
    ∃ reverse : Bool,
      let zeta : ℝ → AnnulusCoordinates := fun t => base (if reverse then D - t else t)
      let sigma := if reverse then beta else alpha
      let T := if reverse then B else A
      let q := if reverse then D - p else p
      let k := if reverse then -c else c
      0 < T ∧ 0 < k ∧ q ∈ Ioo 0 D ∧
      ContDiff ℝ ∞ zeta ∧ ContDiff ℝ ∞ sigma ∧
      InjOn zeta (Icc 0 D) ∧ InjOn sigma (Icc 0 T) ∧
      zeta 0 = sigma 0 ∧ zeta q = eta u ∧ sigma T = eta L ∧
      deriv eta u = k • deriv zeta q ∧
      zeta '' Icc 0 D = base '' Icc 0 D ∧
      zeta '' Icc 0 q = (if reverse then base '' Icc p D else base '' Icc 0 p) ∧
      (∀ x ∈ Icc 0 D, ∀ t ∈ Icc 0 T, zeta x = sigma t → x = 0 ∧ t = 0) ∧
      ∃ U' V' : Set AnnulusCoordinates,
        IsOpen U' ∧ IsOpen V' ∧ IsPathConnected U' ∧ IsPathConnected V' ∧
        Bornology.IsBounded U' ∧ ¬ Bornology.IsBounded V' ∧ Disjoint U' V' ∧
        U' ∪ V' = (frontier U')ᶜ ∧ frontier V' = frontier U' ∧
        IsCompact (closure U') ∧ closure U' ⊆ closure U ∧
        (∀ x ∈ Icc 0 q, ∀ t ∈ Icc u L, zeta x = eta t → x = q ∧ t = u) ∧
        (∀ s ∈ Icc 0 T, ∀ t ∈ Icc u L, sigma s = eta t → s = T ∧ t = L) ∧
        frontier U' = zeta '' Icc 0 q ∪ (sigma '' Icc 0 T ∪ eta '' Icc u L) := by
  obtain ⟨reverse, hk, hq, hz, hzi, hzq, hdz, hzimage, hzsubimage⟩ :=
    m64Intrinsic_exists_positive_contact_base_orientation hb hp hbi hcne htangent
  let zeta : ℝ → AnnulusCoordinates := fun t => base (if reverse then D - t else t)
  let sigma := if reverse then beta else alpha
  let T := if reverse then B else A
  let q := if reverse then D - p else p
  have hT : 0 < T := by cases reverse <;> assumption
  have hs : ContDiff ℝ ∞ sigma := by cases reverse <;> assumption
  have hsi : InjOn sigma (Icc 0 T) := by cases reverse <;> assumption
  have hstart : zeta 0 = sigma 0 := by
    cases reverse
    · exact hstartA
    · simpa only [zeta, sigma, ↓reduceIte, sub_zero] using hstartB
  have hterminal : sigma T = eta L := by
    cases reverse
    · exact heL.symm
    · exact hmeet.symm.trans heL.symm
  have hba : ∀ x ∈ Icc 0 D, ∀ t ∈ Icc 0 T,
      zeta x = sigma t → x = 0 ∧ t = 0 := by
    intro x hx t ht hxt
    cases reverse
    · exact hbaseA x hx t ht hxt
    · have hh := hbaseB (D - x)
        ⟨by linarith [hx.2], by linarith [hx.1]⟩ t ht hxt
      exact ⟨by linarith [hh.1], hh.2⟩
  have hzfront : MapsTo zeta (Icc 0 D) (frontier U) := by
    intro t ht
    rw [hfU]
    exact Or.inl (hzimage ▸ mem_image_of_mem zeta ht)
  have hsfront : MapsTo sigma (Icc 0 T) (frontier U) := by
    intro t ht
    rw [hfU]
    cases reverse
    · exact Or.inr (Or.inl (mem_image_of_mem alpha ht))
    · exact Or.inr (Or.inr (mem_image_of_mem beta ht))
  obtain ⟨U', V', hU', hV', hpU', hpV', hbU', hbV', hd', hcover', hfV',
      hK', hnest, hze, hse, hfU'⟩ :=
    m64Intrinsic_exists_last_contact_region hq hT huL hz.continuous.continuousOn
      hs.continuous he.continuous hzi hsi hei hstart (heu.trans hzq.symm)
      hterminal.symm hba hU hV hpV hbV hd hcover hfV hzfront hsfront hinside
  exact ⟨reverse, hT, hk, hq, hz, hs, hzi, hsi, hstart, hzq.trans heu.symm,
    hterminal, hdz, hzimage, hzsubimage, hba, U', V', hU', hV', hpU', hpV',
    hbU', hbV', hd', hcover', hfV', hK', hnest, hze, hse, hfU'⟩

end PoincareConjecture
