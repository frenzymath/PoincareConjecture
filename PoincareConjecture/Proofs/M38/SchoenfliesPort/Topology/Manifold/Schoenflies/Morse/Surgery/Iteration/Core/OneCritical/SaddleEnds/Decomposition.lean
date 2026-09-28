import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.OneCritical.SaddleEnds.UpperFamily
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.OneCritical.SaddleEnds.HeightBand

open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.PoincareConjecture

namespace M38Schoenflies

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

namespace SphereSurgeryCoreCap

structure AnnularEndFamily (v : E3) (g : S2 → E3) (B : Set Real) (C : Set S2) where
  caps : List (SphereSurgeryCoreCap v g B)
  caps_disjoint : caps.Pairwise (fun D E => Disjoint
    (D.chart '' closedBall 0 1) (E.chart '' closedBall 0 1))
  core_complement : C = (⋃ D ∈ caps, D.chart '' ball 0 1)ᶜ
  height : S2 → Real
  height_smooth : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ height
  height_germ : ∀ p ∈ C, height =ᶠ[𝓝 p] (fun q => inner Real v (g q))
  lowerBound : Real
  lowerCut : Real
  upperCut : Real
  upperBound : Real
  lower_lt : lowerBound < lowerCut
  cuts_lt : lowerCut < upperCut
  upper_lt : upperCut < upperBound
  core_height_bounds : ∀ p ∈ C, height p ∈ Ioo lowerBound upperBound
  lower : ∀ D ∈ caps, D.center < lowerCut → LowerAnnularEnd D C height lowerBound lowerCut
  upper : ∀ D ∈ caps, upperCut < D.center → UpperAnnularEnd D C height upperCut upperBound
  lower_disjoint : ∀ D hD hDb E hE hEb, D ≠ E →
    Disjoint (lower D hD hDb).region (lower E hE hEb).region
  upper_disjoint : ∀ D hD haD E hE haE, D ≠ E →
    Disjoint (upper D hD haD).region (upper E hE haE).region
  lower_cover : (⋃ D, ⋃ hD : D ∈ caps, ⋃ hDb : D.center < lowerCut,
    (lower D hD hDb).region) = C ∩ height ⁻¹' Iic lowerCut
  upper_cover : (⋃ D, ⋃ hD : D ∈ caps, ⋃ haD : upperCut < D.center,
    (upper D hD haD).region) = C ∩ height ⁻¹' Ici upperCut
  cap_side : ∀ D ∈ caps, D.center < lowerCut ∨ upperCut < D.center
  height_germ_on_cap : ∀ D ∈ caps, ∀ q ∈ D.chart '' ball 0 1,
    (inner Real v (g q) - D.center) / D.scale < 1 / 4 →
      height =ᶠ[𝓝 q] (fun y => inner Real v (g y))

namespace AnnularEndFamily

variable {v : E3} {g : S2 → E3} {B : Set Real} {C : Set S2}

def EndIndex (A : AnnularEndFamily v g B C) :=
  {D : {D // D ∈ A.caps} // D.1.center < A.lowerCut} ⊕
    {D : {D // D ∈ A.caps} // A.upperCut < D.1.center}

instance (A : AnnularEndFamily v g B C) : Fintype A.EndIndex := by
  classical
  unfold EndIndex
  infer_instance

def endRegion (A : AnnularEndFamily v g B C) : A.EndIndex → Set S2
  | .inl D => (A.lower D.1.1 D.1.2 D.2).region
  | .inr D => (A.upper D.1.1 D.1.2 D.2).region

def middleRegion (A : AnnularEndFamily v g B C) : Set S2 :=
  C ∩ A.height ⁻¹' Icc A.lowerCut A.upperCut

theorem lower_region_height (A : AnnularEndFamily v g B C)
    (D : SphereSurgeryCoreCap v g B) (hD : D ∈ A.caps) (hDb : D.center < A.lowerCut)
    {p : S2} (hp : p ∈ (A.lower D hD hDb).region) : A.height p ≤ A.lowerCut :=
  (A.lower_cover.subset (mem_iUnion_of_mem D (mem_iUnion_of_mem hD
    (mem_iUnion_of_mem hDb hp)))).2

theorem upper_region_height (A : AnnularEndFamily v g B C)
    (D : SphereSurgeryCoreCap v g B) (hD : D ∈ A.caps) (haD : A.upperCut < D.center)
    {p : S2} (hp : p ∈ (A.upper D hD haD).region) : A.upperCut ≤ A.height p :=
  (A.upper_cover.subset (mem_iUnion_of_mem D (mem_iUnion_of_mem hD
    (mem_iUnion_of_mem haD hp)))).2

theorem pairwise_disjoint (A : AnnularEndFamily v g B C) :
    Pairwise (fun i j : A.EndIndex => Disjoint (A.endRegion i) (A.endRegion j)) := by
  rintro (D | D) (E | E) hne
  · apply A.lower_disjoint
    intro heq
    apply hne
    congr 1
    apply Subtype.ext
    exact Subtype.ext heq
  · apply Set.disjoint_left.mpr
    intro p hpD hpE
    exact (not_le_of_gt A.cuts_lt) ((A.upper_region_height E.1.1 E.1.2 E.2 hpE).trans
      (A.lower_region_height D.1.1 D.1.2 D.2 hpD))
  · apply Set.disjoint_left.mpr
    intro p hpD hpE
    exact (not_le_of_gt A.cuts_lt) ((A.upper_region_height D.1.1 D.1.2 D.2 hpD).trans
      (A.lower_region_height E.1.1 E.1.2 E.2 hpE))
  · apply A.upper_disjoint
    intro heq
    apply hne
    congr 1
    apply Subtype.ext
    exact Subtype.ext heq

theorem endRegion_subset_core (A : AnnularEndFamily v g B C) (i : A.EndIndex) :
    A.endRegion i ⊆ C := by
  rcases i with D | D
  · exact (A.lower D.1.1 D.1.2 D.2).retained
  · exact (A.upper D.1.1 D.1.2 D.2).retained

theorem core_eq_middle_union_ends (A : AnnularEndFamily v g B C) :
    C = A.middleRegion ∪ ⋃ i, A.endRegion i := by
  apply Subset.antisymm
  · intro p hp
    by_cases hl : A.height p ≤ A.lowerCut
    · right
      have hpl := A.lower_cover.superset ⟨hp, hl⟩
      simp only [mem_iUnion] at hpl
      obtain ⟨D, hD, hDb, hpD⟩ := hpl
      exact mem_iUnion_of_mem (.inl ⟨⟨D, hD⟩, hDb⟩) hpD
    · by_cases hu : A.upperCut ≤ A.height p
      · right
        have hpu := A.upper_cover.superset ⟨hp, hu⟩
        simp only [mem_iUnion] at hpu
        obtain ⟨D, hD, haD, hpD⟩ := hpu
        exact mem_iUnion_of_mem (.inr ⟨⟨D, hD⟩, haD⟩) hpD
      · exact Or.inl ⟨hp, (lt_of_not_ge hl).le, (lt_of_not_ge hu).le⟩
  · rintro p (hp | hp)
    · exact hp.1
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hp
      exact A.endRegion_subset_core i hi

theorem range_eq_middle_union_ends_caps (A : AnnularEndFamily v g B C) :
    range g = (g '' A.middleRegion ∪ ⋃ i, g '' A.endRegion i) ∪
      ⋃ D ∈ A.caps, D.parametrization '' closedBall (0 : E2) 1 := by
  rw [range_eq_core_union_caps A.caps A.core_complement]
  conv_lhs => arg 1; rw [A.core_eq_middle_union_ends, image_union, image_iUnion]

theorem cap_height_outside_middle (A : AnnularEndFamily v g B C)
    (D : SphereSurgeryCoreCap v g B) (hD : D ∈ A.caps)
    (x : E2) (hx : x ∈ closedBall 0 1) :
    inner Real v (D.parametrization x) < A.lowerCut ∨
      A.upperCut < inner Real v (D.parametrization x) := by
  rcases A.cap_side D hD with hl | hu
  · left
    have hs := (A.lower D hD hl).scale_neg
    have hh := mul_nonpos_of_nonneg_of_nonpos (D.normalized_height_nonneg hx) hs.le
    rw [div_mul_cancel₀ _ D.scale_ne_zero] at hh
    linarith
  · right
    have hs := (A.upper D hD hu).scale_pos
    have hh := mul_nonneg (D.normalized_height_nonneg hx) hs.le
    rw [div_mul_cancel₀ _ D.scale_ne_zero] at hh
    linarith

end AnnularEndFamily

end SphereSurgeryCoreCap

namespace SphereMorseReduction

open SphereSurgeryCoreCap

theorem exists_terminal_annular_end_family
    {f : S2 → E3} (M : SphereMorseReduction f)
    {g : S2 → E3} (hg : g ∈ M.tree.leaves)
    (P : SphereSurgeryPath (M.v : E3) (fun p => M.D (f p)) g)
    (hP : P.Protects ((fun p => inner Real (M.v : E3) (M.D (f p))) ''
      {p | mfderiv (𝓡 2) 𝓘(Real, Real)
        (fun q => inner Real (M.v : E3) (M.D (f q))) p = 0}))
    (hcaps : P.PreservesCaps) {p : S2} (hp : p ∈ P.core)
    (hc : mfderiv (𝓡 2) 𝓘(Real, Real)
      (fun q => inner Real (M.v : E3) (g q)) p = 0) :
    ∃ ε : Real, 0 < ε ∧ ∀ η : Real, 0 < η → η ≤ ε →
      ∃ A : AnnularEndFamily (M.v : E3) g
        ((fun q => inner Real (M.v : E3) (M.D (f q))) ''
          {q | mfderiv (𝓡 2) 𝓘(Real, Real)
            (fun y => inner Real (M.v : E3) (M.D (f y))) q = 0}) P.core,
        A.lowerCut = inner Real (M.v : E3) (g p) - η ∧
        A.upperCut = inner Real (M.v : E3) (g p) + η := by
  obtain ⟨L, hpair, hcore, h, a, b, ε, hh, hε, ha, hb, hbounds, hgerm,
      hcritical, _, hcenters, hlow⟩ :=
    M.exists_auxiliary_band_and_cap_gap hg P hP hcaps hp hc
  let c := inner Real (M.v : E3) (g p)
  have hpc : h p = c := (hgerm p hp).eq_of_nhds
  have hbounds' (q : S2) (hq : q ∈ P.core) : h q ∈ Ioo a b := by
    rw [(hgerm q hq).eq_of_nhds]
    exact hbounds q hq
  refine ⟨ε, hε, ?_⟩
  intro η hη hηε
  have hal : a < c - η := by dsimp [c]; linarith
  have hub : c + η < b := by dsimp [c]; linarith
  have hcuts : c - η < c + η := by linarith
  have hregL : ∀ q, h q ∈ Icc a (c - η) → mfderiv (𝓡 2) 𝓘(Real, Real) h q ≠ 0 := by
    intro q hq hqcrit
    have hqp : q = p := mem_singleton_iff.mp (hcritical.subset
      ⟨⟨hq.1, by linarith [hq.2]⟩, hqcrit⟩)
    subst q
    rw [hpc] at hq
    linarith [hq.2]
  have hregU : ∀ q, h q ∈ Icc (c + η) b → mfderiv (𝓡 2) 𝓘(Real, Real) h q ≠ 0 := by
    intro q hq hqcrit
    have hqp : q = p := mem_singleton_iff.mp (hcritical.subset
      ⟨⟨by linarith [hq.1], hq.2⟩, hqcrit⟩)
    subst q
    rw [hpc] at hq
    linarith [hq.1]
  have hside (D : SphereSurgeryCoreCap (M.v : E3) g _) (hD : D ∈ L) :
      D.center < c - η ∨ c + η < D.center := by
    have hgap : η < |D.center - c| := hηε.trans_lt (hcenters D hD)
    by_cases hl : D.center < c - η
    · exact Or.inl hl
    · right
      by_contra hu
      have habs : |D.center - c| ≤ η := abs_le.mpr ⟨by linarith, by linarith⟩
      exact (not_le_of_gt hgap) habs
  obtain ⟨lower, hlpair, hlcover⟩ := exists_lower_annular_end_family L hpair hcore
    (P.isConnected_core hcaps).isPreconnected P.isClosed_core hh hgerm hal
    (fun q hq => (hbounds' q hq).1) ⟨p, hp, by rw [hpc]; linarith⟩ hregL
    (by intro D hD heq; rcases hside D hD with hl | hu <;> linarith)
  obtain ⟨upper, hupair, hucover⟩ := exists_upper_annular_end_family
    (by simpa only [mem_sphere, dist_zero_right] using M.v.property) L hpair hcore
    (P.isConnected_core hcaps).isPreconnected P.isClosed_core hh hgerm hub
    (fun q hq => (hbounds' q hq).2) ⟨p, hp, by rw [hpc]; linarith⟩ hregU
    (by intro D hD heq; rcases hside D hD with hl | hu <;> linarith)
  exact ⟨{
    caps := L
    caps_disjoint := hpair
    core_complement := hcore
    height := h
    height_smooth := hh
    height_germ := hgerm
    lowerBound := a
    lowerCut := c - η
    upperCut := c + η
    upperBound := b
    lower_lt := hal
    cuts_lt := hcuts
    upper_lt := hub
    core_height_bounds := hbounds'
    lower := lower
    upper := upper
    lower_disjoint := hlpair
    upper_disjoint := hupair
    lower_cover := hlcover
    upper_cover := hucover
    cap_side := hside
    height_germ_on_cap := hlow }, rfl, rfl⟩

end SphereMorseReduction

end Poincare.Manifold.Schoenflies

end

end M38Schoenflies
