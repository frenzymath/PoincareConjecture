


import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Data.Fintype.Order
import Mathlib.Data.Finite.Sum









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology

namespace Poincare.Topology.Plane.Curves



theorem exists_pos_le_finite_family {ι : Type*} [Finite ι]
    (r : ι → ℝ) (hr : ∀ i, 0 < r i) : ∃ δ > 0, ∀ i, δ ≤ r i := by
  classical
  let := Fintype.ofFinite ι
  by_cases h : Nonempty ι
  · let := h
    obtain ⟨i, _, hi⟩ := Finset.univ.exists_min_image r Finset.univ_nonempty
    exact ⟨r i, hr i, fun j => hi j (Finset.mem_univ j)⟩
  · exact ⟨1, zero_lt_one, fun i => False.elim (h ⟨i⟩)⟩

variable {E : Type*} [TopologicalSpace E]


theorem exists_strip_source_width (F : OpenPartialHomeomorph (ℝ × ℝ) E)
    (haxis : ∀ t ∈ Icc (0 : ℝ) 1, (t, (0 : ℝ)) ∈ F.source) :
    ∃ δ > 0, Icc (0 : ℝ) 1 ×ˢ Ioo (-δ) δ ⊆ F.source := by
  have hsub : Icc (0 : ℝ) 1 ×ˢ {(0 : ℝ)} ⊆ F.source := by
    rintro ⟨t, z⟩ ⟨ht, hz⟩
    have hz0 : z = 0 := hz
    subst z
    exact haxis t ht
  obtain ⟨U, V, _, hV, hIU, h0V, hUV⟩ :=
    generalized_tube_lemma isCompact_Icc isCompact_singleton F.open_source hsub
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp
    (hV.mem_nhds (h0V (mem_singleton (0 : ℝ))))
  refine ⟨δ, hδ, ?_⟩
  rintro ⟨t, z⟩ ⟨ht, hz⟩
  apply hUV ⟨hIU ht, hball ?_⟩
  simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using abs_lt.mpr hz

variable [T2Space E]



theorem exists_disjoint_strip_separation
    (F G : OpenPartialHomeomorph (ℝ × ℝ) E)
    (hFs : ∀ t ∈ Icc (0 : ℝ) 1, (t, (0 : ℝ)) ∈ F.source)
    (hGs : ∀ t ∈ Icc (0 : ℝ) 1, (t, (0 : ℝ)) ∈ G.source)
    (hbase : Disjoint ((fun t => F (t, 0)) '' Icc (0 : ℝ) 1)
      ((fun t => G (t, 0)) '' Icc (0 : ℝ) 1)) :
    ∃ δ > 0, ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
      ∀ z w : ℝ, |z| < δ → |w| < δ →
        (t, z) ∈ F.source ∧ (s, w) ∈ G.source ∧ F (t, z) ≠ G (s, w) := by
  let U : Set ((ℝ × ℝ) × (ℝ × ℝ)) :=
    {q | (q.1.1, q.2.1) ∈ F.source ∧ (q.1.2, q.2.2) ∈ G.source}
  have hU : IsOpen U :=
    (F.open_source.preimage (by fun_prop)).inter (G.open_source.preimage (by fun_prop))
  have hFc : ContinuousOn (fun q : (ℝ × ℝ) × (ℝ × ℝ) => F (q.1.1, q.2.1)) U :=
    F.continuousOn.comp (by fun_prop) (fun _ hq => hq.1)
  have hGc : ContinuousOn (fun q : (ℝ × ℝ) × (ℝ × ℝ) => G (q.1.2, q.2.2)) U :=
    G.continuousOn.comp (by fun_prop) (fun _ hq => hq.2)
  let W : Set ((ℝ × ℝ) × (ℝ × ℝ)) :=
    U ∩ (fun q => (F (q.1.1, q.2.1), G (q.1.2, q.2.2))) ⁻¹' (diagonal E)ᶜ
  have hW : IsOpen W := (hFc.prodMk hGc).isOpen_inter_preimage hU isClosed_diagonal.isOpen_compl
  have hsub : (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) ×ˢ {(0 : ℝ × ℝ)} ⊆ W := by
    rintro ⟨⟨t, s⟩, v⟩ ⟨⟨ht, hs⟩, hv⟩
    have hv0 : v = 0 := hv
    subst v
    refine ⟨⟨hFs t ht, hGs s hs⟩, ?_⟩
    change F (t, 0) ≠ G (s, 0)
    intro he
    exact disjoint_left.mp hbase ⟨t, ht, he⟩ ⟨s, hs, rfl⟩
  obtain ⟨V, Z, _, hZ, hIV, h0Z, hVZ⟩ := generalized_tube_lemma
    (isCompact_Icc.prod isCompact_Icc) isCompact_singleton hW hsub
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp
    (hZ.mem_nhds (h0Z (mem_singleton (0 : ℝ × ℝ))))
  refine ⟨δ, hδ, fun t ht s hs z w hz hw => ?_⟩
  have hzw : (z, w) ∈ Z := hball (by
    simpa only [Metric.mem_ball, dist_zero_right, Prod.norm_def, Real.norm_eq_abs, max_lt_iff]
      using And.intro hz hw)
  have hmem : ((t, s), (z, w)) ∈ W := hVZ ⟨hIV ⟨ht, hs⟩, hzw⟩
  exact ⟨hmem.1.1, hmem.1.2, hmem.2⟩




theorem exists_finite_disjoint_strip_width
    {ι : Type*} [Finite ι] (F : ι → OpenPartialHomeomorph (ℝ × ℝ) E)
    (haxis : ∀ i, ∀ t ∈ Icc (0 : ℝ) 1, (t, (0 : ℝ)) ∈ (F i).source)
    (separate : ι → ι → Prop)
    (hbase : ∀ i j, separate i j →
      Disjoint ((fun t => F i (t, 0)) '' Icc (0 : ℝ) 1)
        ((fun t => F j (t, 0)) '' Icc (0 : ℝ) 1))
    (bound : ι → ℝ) (hbound : ∀ i, 0 < bound i) :
    ∃ δ > 0, (∀ i, δ ≤ bound i) ∧
      (∀ i, Icc (0 : ℝ) 1 ×ˢ Ioo (-δ) δ ⊆ (F i).source) ∧
      ∀ i j, separate i j →
        Disjoint (F i '' (Icc (0 : ℝ) 1 ×ˢ Ioo (-δ) δ))
          (F j '' (Icc (0 : ℝ) 1 ×ˢ Ioo (-δ) δ)) := by
  classical
  let J := {p : ι × ι // separate p.1 p.2}
  have hsources : ∀ i, ∃ δ > 0, Icc (0 : ℝ) 1 ×ˢ Ioo (-δ) δ ⊆ (F i).source :=
    fun i => exists_strip_source_width (F i) (haxis i)
  choose source hsource_pos hsource using hsources
  have hpairs : ∀ p : J, ∃ δ > 0, ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
      ∀ z w : ℝ, |z| < δ → |w| < δ →
        (t, z) ∈ (F p.1.1).source ∧ (s, w) ∈ (F p.1.2).source ∧
          F p.1.1 (t, z) ≠ F p.1.2 (s, w) :=
    fun p => exists_disjoint_strip_separation (F p.1.1) (F p.1.2)
      (haxis p.1.1) (haxis p.1.2) (hbase p.1.1 p.1.2 p.2)
  choose pair hpair_pos hpair using hpairs
  let bounds : ι ⊕ J → ℝ := Sum.elim (fun i => min (bound i) (source i)) pair
  have hbounds : ∀ i, 0 < bounds i := by
    rintro (i | p)
    · exact lt_min (hbound i) (hsource_pos i)
    · exact hpair_pos p
  obtain ⟨δ, hδ, hle⟩ := exists_pos_le_finite_family bounds hbounds
  refine ⟨δ, hδ, fun i => (hle (Sum.inl i)).trans (min_le_left _ _), ?_, ?_⟩
  · intro i q hq
    have hδs : δ ≤ source i := (hle (Sum.inl i)).trans (min_le_right _ _)
    exact hsource i ⟨hq.1, ⟨by linarith [hq.2.1], hq.2.2.trans_le hδs⟩⟩
  · intro i j hij
    apply disjoint_left.mpr
    rintro y ⟨⟨t, z⟩, ⟨ht, hz⟩, hty⟩ ⟨⟨s, w⟩, ⟨hs, hw⟩, hsy⟩
    let p : J := ⟨(i, j), hij⟩
    have hδp : δ ≤ pair p := hle (Sum.inr p)
    exact (hpair p t ht s hs z w ((abs_lt.mpr hz).trans_le hδp)
      ((abs_lt.mpr hw).trans_le hδp)).2.2 (hty.trans hsy.symm)

end Poincare.Topology.Plane.Curves
