import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_LoopCornerPatch
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_LinearBand

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold Matrix
open PoincareConjecture.Topology.Surface

namespace PoincareConjecture

theorem m64Intrinsic_exists_loop_boundary_patch
    {gamma : ℝ → AnnulusCoordinates} (hg : ContDiff ℝ ∞ gamma) {T : ℝ} (hT : 0 < T)
    (hend : gamma 0 = gamma T) (hinj : InjOn gamma (Ico 0 T))
    (hregular : ∀ t ∈ Ioo (0 : ℝ) T, deriv gamma t ≠ 0)
    (hind : LinearIndependent ℝ
      (![deriv gamma 0, -deriv gamma T] : Fin 2 → AnnulusCoordinates))
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hdisj : Disjoint U V) (hfU : frontier U = gamma '' Icc 0 T)
    (hfV : frontier V = gamma '' Icc 0 T)
    {p : AnnulusCoordinates} (hp : p ∈ gamma '' Icc 0 T) :
    ∃ (A : Set AnnulusCoordinates) (lines : List (AnnulusCoordinates →ᵃ[ℝ] ℝ))
      (W : Set AnnulusCoordinates),
      IsCompact A ∧ A ⊆ closure U ∧
      frontier A ⊆ gamma '' Icc 0 T ∪ ⋃ l ∈ lines, {z | l z = 0} ∧
      (∀ l ∈ lines, Function.Surjective l) ∧
      IsOpen W ∧ p ∈ W ∧ W ∩ closure U ⊆ A := by
  have hcorner := m64Intrinsic_exists_loop_corner_patch hg hT hend hinj hind
    hU hV hdisj hfU hfV
  obtain ⟨t, ht, rfl⟩ := hp
  by_cases hzero : t = 0
  · subst t
    exact hcorner
  by_cases htop : t = T
  · subst t
    simpa only [← hend] using hcorner
  have ht' : t ∈ Ioo (0 : ℝ) T :=
    ⟨lt_of_le_of_ne ht.1 (Ne.symm hzero), lt_of_le_of_ne ht.2 htop⟩
  obtain ⟨L, h, X, a, b, d, hab, B, lines, W, _, _, _, hcompact, hsub,
    hfront, hlines, _, _, hW, hpW, hcover⟩ :=
    m64Intrinsic_exists_loop_linear_band hg hend hinj ht' (hregular t ht')
      hU hV hdisj hfU hfV
  exact ⟨B.lower.carrier ∪ B.upper.carrier, lines, W, hcompact, hsub,
    by simpa only [hfU] using hfront, hlines, hW, hpW, hcover⟩

theorem m64Intrinsic_exists_finite_loop_boundary_cover
    {gamma : ℝ → AnnulusCoordinates} (hg : ContDiff ℝ ∞ gamma) {T : ℝ} (hT : 0 < T)
    (hend : gamma 0 = gamma T) (hinj : InjOn gamma (Ico 0 T))
    (hregular : ∀ t ∈ Ioo (0 : ℝ) T, deriv gamma t ≠ 0)
    (hind : LinearIndependent ℝ
      (![deriv gamma 0, -deriv gamma T] : Fin 2 → AnnulusCoordinates))
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hdisj : Disjoint U V) (hfU : frontier U = gamma '' Icc 0 T)
    (hfV : frontier V = gamma '' Icc 0 T) :
    ∃ (s : Finset (gamma '' Icc 0 T)) (pieces : s → Set AnnulusCoordinates)
      (lines : List (AnnulusCoordinates →ᵃ[ℝ] ℝ)),
      (∀ i, IsCompact (pieces i)) ∧ (∀ i, pieces i ⊆ closure U) ∧
      (∀ i, frontier (pieces i) ⊆ gamma '' Icc 0 T ∪ ⋃ l ∈ lines, {z | l z = 0}) ∧
      (∀ l ∈ lines, Function.Surjective l) ∧
      ∀ p ∈ frontier U, ∃ W : Set AnnulusCoordinates,
        IsOpen W ∧ p ∈ W ∧ W ∩ closure U ⊆ ⋃ i, pieces i := by
  classical
  let K := gamma '' Icc 0 T
  have hK : IsCompact K := isCompact_Icc.image hg.continuous
  choose A L W hcompact hsub hfront hlines hW hpW hcover using fun p : K =>
    m64Intrinsic_exists_loop_boundary_patch hg hT hend hinj hregular hind hU hV hdisj
      hfU hfV p.property
  have hKW : K ⊆ ⋃ p : K, W p := fun p hp => mem_iUnion.mpr ⟨⟨p, hp⟩, hpW ⟨p, hp⟩⟩
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover W hW hKW
  let pieces (i : s) := A i.val
  let lines := s.toList.flatMap L
  have hlineMem (i : s) {l : AnnulusCoordinates →ᵃ[ℝ] ℝ} (hl : l ∈ L i.val) :
      l ∈ lines := List.mem_flatMap.mpr ⟨i.val, Finset.mem_toList.mpr i.property, hl⟩
  refine ⟨s, pieces, lines, fun i => hcompact i.val, fun i => hsub i.val, ?_, ?_, ?_⟩
  · intro i z hz
    rcases hfront i.val hz with hzK | hzline
    · exact Or.inl hzK
    · obtain ⟨l, hl, hzl⟩ := mem_iUnion₂.mp hzline
      exact Or.inr (mem_iUnion₂.mpr ⟨l, hlineMem i hl, hzl⟩)
  · intro l hl
    obtain ⟨p, _, hlp⟩ := List.mem_flatMap.mp hl
    exact hlines p l hlp
  · intro p hp
    have hpK : p ∈ K := by
      change p ∈ gamma '' Icc 0 T
      rwa [← hfU]
    obtain ⟨q, hqs, hpWq⟩ := mem_iUnion₂.mp (hs hpK)
    refine ⟨W q, hW q, hpWq, ?_⟩
    intro z hz
    exact mem_iUnion.mpr ⟨⟨q, hqs⟩, hcover q hz⟩

end PoincareConjecture
