import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ThreeArcRegion
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_NestedJordanRegions










noncomputable section
set_option autoImplicit false

open Set
open scoped Topology

namespace PoincareConjecture





theorem m64Intrinsic_exists_last_contact_region
    {base alpha eta : ℝ → AnnulusCoordinates} {a b p A u L : ℝ}
    (hp : p ∈ Ioo a b) (hA : 0 < A) (huL : u < L)
    (hb : ContinuousOn base (Icc a b)) (ha : Continuous alpha) (he : Continuous eta)
    (hbi : InjOn base (Icc a b)) (hai : InjOn alpha (Icc 0 A))
    (hei : InjOn eta (Icc u L))
    (hstart : base a = alpha 0) (heu : eta u = base p) (heL : eta L = alpha A)
    (hba : ∀ x ∈ Icc a b, ∀ t ∈ Icc 0 A, base x = alpha t → x = a ∧ t = 0)
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hpV : IsPreconnected V) (hbV : ¬ Bornology.IsBounded V) (hd : Disjoint U V)
    (hcover : U ∪ V = (frontier U)ᶜ) (hfV : frontier V = frontier U)
    (hbase : MapsTo base (Icc a b) (frontier U))
    (hside : MapsTo alpha (Icc 0 A) (frontier U))
    (hinside : MapsTo eta (Ioo u L) U) :
    ∃ U' V' : Set AnnulusCoordinates,
      IsOpen U' ∧ IsOpen V' ∧ IsPathConnected U' ∧ IsPathConnected V' ∧
      Bornology.IsBounded U' ∧ ¬ Bornology.IsBounded V' ∧ Disjoint U' V' ∧
      U' ∪ V' = (frontier U')ᶜ ∧ frontier V' = frontier U' ∧
      IsCompact (closure U') ∧ closure U' ⊆ closure U ∧
      (∀ x ∈ Icc a p, ∀ t ∈ Icc u L, base x = eta t → x = p ∧ t = u) ∧
      (∀ s ∈ Icc 0 A, ∀ t ∈ Icc u L, alpha s = eta t → s = A ∧ t = L) ∧
      frontier U' = base '' Icc a p ∪ (alpha '' Icc 0 A ∪ eta '' Icc u L) := by
  have hsub : Icc a p ⊆ Icc a b := Icc_subset_Icc le_rfl hp.2.le
  have havoid (t : ℝ) (ht : t ∈ Ioo u L) : eta t ∉ frontier U := by
    intro hf
    exact (show eta t ∉ U by simpa only [hU.interior_eq] using hf.2) (hinside ht)
  have hbc : ∀ x ∈ Icc a p, ∀ t ∈ Icc u L,
      base x = eta t → x = p ∧ t = u := by
    intro x hx t ht hxt
    by_cases htu : t = u
    · refine ⟨hbi (hsub hx) (Ioo_subset_Icc_self hp) ?_, htu⟩
      simpa only [htu, heu] using hxt
    by_cases htL : t = L
    · have h := hba x (hsub hx) A ⟨hA.le, le_rfl⟩
        (by simpa only [htL, heL] using hxt)
      exact False.elim (hA.ne' h.2)
    exact False.elim (havoid t
      ⟨lt_of_le_of_ne ht.1 (Ne.symm htu), lt_of_le_of_ne ht.2 htL⟩
      (hxt ▸ hbase (hsub hx)))
  have hac : ∀ s ∈ Icc 0 A, ∀ t ∈ Icc u L,
      alpha s = eta t → s = A ∧ t = L := by
    intro s hs t ht hst
    by_cases htL : t = L
    · refine ⟨hai hs ⟨hA.le, le_rfl⟩ ?_, htL⟩
      simpa only [htL, heL] using hst
    by_cases htu : t = u
    · have h := hba p (Ioo_subset_Icc_self hp) s hs
        (by simpa only [htu, heu] using hst.symm)
      exact False.elim (hp.1.ne' h.1)
    exact False.elim (havoid t
      ⟨lt_of_le_of_ne ht.1 (Ne.symm htu), lt_of_le_of_ne ht.2 htL⟩
      (hst ▸ hside hs))
  obtain ⟨U', V', hU', hV', hpU', hpV', hbU', hbV', hd', hc', hfV', hK', hfU'⟩ :=
    m64Intrinsic_exists_three_arc_region hp.1 hA huL (hb.mono hsub) ha he
      (hbi.mono hsub) hai hei hstart heu.symm heL.symm
      (fun x hx => hba x (hsub hx)) hbc hac
  have hfront : frontier U' ⊆ closure U := by
    rw [hfU']
    rintro z (⟨x, hx, rfl⟩ | ⟨s, hs, rfl⟩ | ⟨t, ht, rfl⟩)
    · exact frontier_subset_closure (hbase (hsub hx))
    · exact frontier_subset_closure (hside hs)
    · by_cases htu : t = u
      · rw [htu, heu]
        exact frontier_subset_closure (hbase (Ioo_subset_Icc_self hp))
      by_cases htL : t = L
      · rw [htL, heL]
        exact frontier_subset_closure (hside ⟨hA.le, le_rfl⟩)
      exact subset_closure (hinside
        ⟨lt_of_le_of_ne ht.1 (Ne.symm htu), lt_of_le_of_ne ht.2 htL⟩)
  have hnest := m64Intrinsic_jordan_nested_of_frontier_subset hU hV hU' hV'
    hpV hbU' hbV hd hd' hcover hc' hfV.symm hfront
  exact ⟨U', V', hU', hV', hpU', hpV', hbU', hbV', hd', hc', hfV', hK',
    closure_mono hnest, hbc, hac, hfU'⟩

end PoincareConjecture
