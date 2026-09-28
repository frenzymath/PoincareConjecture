import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_TwoCornerCaps













noncomputable section
set_option autoImplicit false

open Set
open scoped Topology

namespace PoincareConjecture





theorem m64Intrinsic_arc_corner_contact_parameter
    {gamma : ℝ → AnnulusCoordinates} {T r t : ℝ}
    (hinj : InjOn gamma (Icc 0 T)) (hrT : r ≤ T)
    {K U C : Set AnnulusCoordinates}
    (hfront : frontier U = gamma '' Icc 0 T ∪ K)
    (ht : t ∈ Ioo (0 : ℝ) T) (havoid : gamma t ∉ K) (terminal : Bool)
    (hcontact : C ∩ frontier U ⊆
      (fun s => gamma (if terminal then T - s else s)) '' Icc 0 r ∪ K)
    (hmem : gamma t ∈ C) :
    if terminal then T - r ≤ t else t ≤ r := by
  have htf : gamma t ∈ frontier U := by
    rw [hfront]
    exact Or.inl ⟨t, ⟨ht.1.le, ht.2.le⟩, rfl⟩
  obtain ⟨s, hs, heq⟩ := (hcontact ⟨hmem, htf⟩).resolve_right havoid
  cases terminal
  · have he : s = t := hinj ⟨hs.1, hs.2.trans hrT⟩ ⟨ht.1.le, ht.2.le⟩ heq
    change t ≤ r
    simpa only [he] using hs.2
  · change gamma (T - s) = gamma t at heq
    have he : T - s = t := hinj ⟨by linarith [hs.2], by linarith [hs.1]⟩
      ⟨ht.1.le, ht.2.le⟩ heq
    change T - r ≤ t
    linarith [hs.2]





theorem m64Intrinsic_arc_trim_avoids_two_caps
    {gamma : ℝ → AnnulusCoordinates} {T : ℝ}
    (hinj : InjOn gamma (Icc 0 T)) (r : Bool → ℝ)
    (hr : ∀ e, 0 < r e) (hrT : ∀ e, r e ≤ T)
    {K U : Set AnnulusCoordinates} (C : Bool → Set AnnulusCoordinates)
    (hfront : frontier U = gamma '' Icc 0 T ∪ K)
    (havoid : ∀ t ∈ Ioo (0 : ℝ) T, gamma t ∉ K)
    (hcontact : ∀ e : Bool, C e ∩ frontier U ⊆
      (fun s => gamma (if e then T - s else s)) '' Icc 0 (r e) ∪ K) :
    ∀ t ∈ Ioo (r false) (T - r true), gamma t ∉ C false ∪ C true := by
  intro t ht hmem
  have ht' : t ∈ Ioo (0 : ℝ) T :=
    ⟨(hr false).trans ht.1, ht.2.trans (sub_lt_self T (hr true))⟩
  rcases hmem with hmem | hmem
  · exact (not_le_of_gt ht.1) (m64Intrinsic_arc_corner_contact_parameter
      hinj (hrT false) hfront ht' (havoid t ht') false (hcontact false) hmem)
  · exact (not_le_of_gt ht.2) (m64Intrinsic_arc_corner_contact_parameter
      hinj (hrT true) hfront ht' (havoid t ht') true (hcontact true) hmem)





theorem m64Intrinsic_corner_separator_union
    {C D W : Set AnnulusCoordinates} (hD : IsClosed D) (hCD : Disjoint C D)
    {p : AnnulusCoordinates} (hp : p ∈ C) (hW : IsOpen W) (hpW : p ∈ W)
    (ell : AnnulusCoordinates →L[ℝ] ℝ)
    (hsep : ∀ z ∈ W ∩ C, ell (z - p) ≤ 0) :
    ∃ O : Set AnnulusCoordinates, IsOpen O ∧ p ∈ O ∧
      ∀ z ∈ O ∩ (C ∪ D), ell (z - p) ≤ 0 := by
  refine ⟨W ∩ Dᶜ, hW.inter hD.isOpen_compl,
    ⟨hpW, fun hpd => Set.disjoint_left.mp hCD hp hpd⟩, ?_⟩
  rintro z ⟨⟨hzW, hzD⟩, hzC | hzD'⟩
  · exact hsep z ⟨hzW, hzC⟩
  · exact (hzD hzD').elim

end PoincareConjecture
