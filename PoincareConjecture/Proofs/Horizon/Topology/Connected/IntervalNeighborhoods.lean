import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith

noncomputable section
set_option autoImplicit false

open Set Filter
open scoped Topology

namespace Poincare.Topology

private theorem exists_positive_interval_margin {a b : ℝ} (hab : a ≤ b)
    {U : Set ℝ} (hU : IsOpen U) (hsub : Icc a b ⊆ U) :
    ∃ d : ℝ, 0 < d ∧ Icc (a - d) (b + d) ⊆ U := by
  obtain ⟨l, u, hau, hleft⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    (hU.mem_nhds (hsub ⟨le_rfl, hab⟩))
  obtain ⟨v, w, hbw, hright⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    (hU.mem_nhds (hsub ⟨hab, le_rfl⟩))
  obtain ⟨d, hd, hdb⟩ := exists_between (lt_min (sub_pos.mpr hau.1) (sub_pos.mpr hbw.2))
  refine ⟨d, hd, ?_⟩
  intro x hx
  have hda := hdb.trans_le (min_le_left _ _)
  have hdd := hdb.trans_le (min_le_right _ _)
  by_cases hxa : x < a
  · exact hleft ⟨by linarith [hx.1], hxa.trans hau.2⟩
  by_cases hbx : b < x
  · exact hright ⟨hbw.1.trans hbx, by linarith [hx.2]⟩
  exact hsub ⟨le_of_not_gt hxa, le_of_not_gt hbx⟩

theorem exists_closed_rectangle_subset_open_of_interval_subset
    {a b : ℝ} (hab : a ≤ b) {W : Set (ℝ × ℝ)} (hW : IsOpen W)
    (hsub : Icc a b ×ˢ ({0} : Set ℝ) ⊆ W) :
    ∃ d : ℝ, 0 < d ∧ Icc (a - d) (b + d) ×ˢ Icc (-d) d ⊆ W := by
  obtain ⟨U, V, hU, hV, hIU, h0V, hUV⟩ :=
    generalized_tube_lemma isCompact_Icc isCompact_singleton hW hsub
  obtain ⟨d, hd, hdU⟩ := exists_positive_interval_margin hab hU hIU
  obtain ⟨t, ht, htV⟩ := exists_positive_interval_margin (le_refl (0 : ℝ)) hV
    (by simpa using h0V)
  refine ⟨min d t, lt_min hd ht, ?_⟩
  intro x hx
  apply hUV
  constructor
  · apply hdU
    exact ⟨by linarith [hx.1.1, min_le_left d t],
      by linarith [hx.1.2, min_le_left d t]⟩
  · apply htV
    exact ⟨by linarith [hx.2.1, min_le_right d t],
      by linarith [hx.2.2, min_le_right d t]⟩

theorem exists_pairwise_disjoint_open_supersets_of_isCompact
    {I X : Type*} [Finite I] [TopologicalSpace X] [T2Space X]
    (K O : I → Set X) (hK : ∀ i, IsCompact (K i))
    (hdisj : Pairwise (fun i j => Disjoint (K i) (K j)))
    (hO : ∀ i, IsOpen (O i)) (hKO : ∀ i, K i ⊆ O i) :
    ∃ U : I → Set X, (∀ i, IsOpen (U i) ∧ K i ⊆ U i ∧ U i ⊆ O i) ∧
      Pairwise (fun i j => Disjoint (U i) (U j)) := by
  classical
  have hsep (i : I) : SeparatedNhds (K i) (⋃ j : {j : I // j ≠ i}, K j) := by
    apply SeparatedNhds.of_isCompact_isCompact (hK i)
      (isCompact_iUnion (fun j : {j : I // j ≠ i} => hK j))
    apply disjoint_iUnion_right.mpr
    intro j
    exact hdisj j.property.symm
  choose A B hA hB hKA hKB hAB using hsep
  let U : I → Set X := fun i => O i ∩ A i ∩ ⋂ j : {j : I // j ≠ i}, B j
  refine ⟨U, ?_, ?_⟩
  · intro i
    refine ⟨((hO i).inter (hA i)).inter (isOpen_iInter_of_finite (fun j => hB j)), ?_, ?_⟩
    · intro x hx
      refine ⟨⟨hKO i hx, hKA i hx⟩, mem_iInter.mpr ?_⟩
      intro j
      exact hKB j (mem_iUnion.mpr ⟨⟨i, j.property.symm⟩, hx⟩)
    · exact fun x hx => hx.1.1
  · intro i j hij
    apply (hAB i).mono
    · exact fun x hx => hx.1.2
    · exact fun x hx => mem_iInter.mp hx.2 ⟨i, hij⟩

theorem exists_disjoint_closed_interval_rectangles
    {I X : Type*} [Finite I] [TopologicalSpace X] [T2Space X]
    (F : I → ℝ × ℝ → X) (a b : I → ℝ) (hab : ∀ i, a i ≤ b i)
    (W : I → Set (ℝ × ℝ)) (hW : ∀ i, IsOpen (W i))
    (hFW : ∀ i, ContinuousOn (F i) (W i))
    (hcentral : ∀ i, Icc (a i) (b i) ×ˢ ({0} : Set ℝ) ⊆ W i)
    (hdisj : Pairwise (fun i j =>
      Disjoint (F i '' (Icc (a i) (b i) ×ˢ ({0} : Set ℝ)))
        (F j '' (Icc (a j) (b j) ×ˢ ({0} : Set ℝ)))))
    (O : I → Set X) (hO : ∀ i, IsOpen (O i))
    (hFO : ∀ i, F i '' (Icc (a i) (b i) ×ˢ ({0} : Set ℝ)) ⊆ O i) :
    ∃ d : ℝ, 0 < d ∧ ∃ U : I → Set X,
      (∀ i, IsOpen (U i) ∧ U i ⊆ O i ∧
        F i '' (Icc (a i) (b i) ×ˢ ({0} : Set ℝ)) ⊆ U i) ∧
      Pairwise (fun i j => Disjoint (U i) (U j)) ∧
      ∀ i, Icc (a i - d) (b i + d) ×ˢ Icc (-d) d ⊆ W i ∧
        F i '' (Icc (a i - d) (b i + d) ×ˢ Icc (-d) d) ⊆ U i := by
  let K : I → Set X := fun i => F i '' (Icc (a i) (b i) ×ˢ ({0} : Set ℝ))
  have hK (i : I) : IsCompact (K i) :=
    (isCompact_Icc.prod isCompact_singleton).image_of_continuousOn
      ((hFW i).mono (hcentral i))
  obtain ⟨U, hU, hUdisj⟩ :=
    exists_pairwise_disjoint_open_supersets_of_isCompact K O hK hdisj hO hFO
  have hrect (i : I) : ∃ d : ℝ, 0 < d ∧
      Icc (a i - d) (b i + d) ×ˢ Icc (-d) d ⊆ W i ∩ (F i) ⁻¹' U i := by
    apply exists_closed_rectangle_subset_open_of_interval_subset (hab i)
      ((hFW i).isOpen_inter_preimage (hW i) (hU i).1)
    intro x hx
    exact ⟨hcentral i hx, (hU i).2.1 (mem_image_of_mem (F i) hx)⟩
  choose d hd hdrect using hrect
  have hN : IsOpen (⋂ i, Iio (d i)) := isOpen_iInter_of_finite (fun _ => isOpen_Iio)
  have h0N : (0 : ℝ) ∈ ⋂ i, Iio (d i) := mem_iInter.mpr hd
  obtain ⟨l, u, hlu, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hN.mem_nhds h0N)
  obtain ⟨ε, hε, hεu⟩ := exists_between hlu.2
  have hεd (i : I) : ε < d i :=
    mem_iInter.mp (hsub ⟨hlu.1.trans hε, hεu⟩) i
  refine ⟨ε, hε, U, fun i => ⟨(hU i).1, (hU i).2.2, (hU i).2.1⟩, hUdisj, ?_⟩
  intro i
  have hsmall : Icc (a i - ε) (b i + ε) ×ˢ Icc (-ε) ε ⊆
      Icc (a i - d i) (b i + d i) ×ˢ Icc (-d i) (d i) := by
    intro x hx
    exact ⟨⟨by linarith [(hεd i), hx.1.1], by linarith [(hεd i), hx.1.2]⟩,
      ⟨by linarith [(hεd i), hx.2.1], by linarith [(hεd i), hx.2.2]⟩⟩
  refine ⟨fun x hx => (hdrect i (hsmall hx)).1, ?_⟩
  rintro x ⟨y, hy, rfl⟩
  exact (hdrect i (hsmall hy)).2

end Poincare.Topology
