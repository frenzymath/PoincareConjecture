import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CrossRayRegion
import Mathlib.Combinatorics.SimpleGraph.Paths

noncomputable section
set_option autoImplicit false

open Set Function
open scoped Topology

namespace PoincareConjecture

theorem m64Intrinsic_exists_oriented_embedded_arc
    {alpha : ℝ → AnnulusCoordinates} {a b : AnnulusCoordinates}
    (hcont : ContinuousOn alpha (Icc 0 1)) (hinj : InjOn alpha (Icc 0 1))
    (hends : (alpha 0 = a ∧ alpha 1 = b) ∨ (alpha 0 = b ∧ alpha 1 = a)) :
    ∃ beta : ℝ → AnnulusCoordinates,
      ContinuousOn beta (Icc 0 1) ∧ InjOn beta (Icc 0 1) ∧
      beta 0 = a ∧ beta 1 = b ∧ beta '' Icc 0 1 = alpha '' Icc 0 1 := by
  rcases hends with hab | hba
  · exact ⟨alpha, hcont, hinj, hab.1, hab.2, rfl⟩
  · let beta : ℝ → AnnulusCoordinates := fun t => alpha (1 - t)
    have hparam (t : ℝ) (ht : t ∈ Icc 0 1) : 1 - t ∈ Icc 0 1 :=
      ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have hbc : ContinuousOn beta (Icc 0 1) :=
      hcont.comp (continuous_const.sub continuous_id).continuousOn hparam
    have hbi : InjOn beta (Icc 0 1) := by
      intro s hs t ht hst
      have heq := hinj (hparam s hs) (hparam t ht) hst
      linarith
    refine ⟨beta, hbc, hbi, ?_, ?_, ?_⟩
    · simpa only [beta, sub_zero] using hba.2
    · simpa only [beta, sub_self] using hba.1
    · change (alpha ∘ fun t => 1 - t) '' Icc (0 : ℝ) 1 = _
      rw [image_comp, image_const_sub_Icc]
      norm_num

private theorem m64_dart_image_union_cons {V : Type*} {G : SimpleGraph V}
    (arc : G.Dart → ℝ → AnnulusCoordinates) {u v w : V} (h : G.Adj u v)
    (p : G.Walk v w) :
    (⋃ d ∈ (SimpleGraph.Walk.cons h p).darts, arc d '' Icc 0 1) =
      arc ⟨(u, v), h⟩ '' Icc 0 1 ∪ ⋃ d ∈ p.darts, arc d '' Icc 0 1 := by
  ext z
  simp

theorem m64Intrinsic_exists_embedded_graph_path
    {V : Type*} {G : SimpleGraph V}
    (point : V → AnnulusCoordinates) (hpoint : Injective point)
    (arc : G.Dart → ℝ → AnnulusCoordinates)
    (hcont : ∀ d, ContinuousOn (arc d) (Icc 0 1))
    (hinj : ∀ d, InjOn (arc d) (Icc 0 1))
    (hstart : ∀ d, arc d 0 = point d.fst)
    (hend : ∀ d, arc d 1 = point d.snd)
    (hmeet : ∀ d e, d.edge ≠ e.edge →
      (arc d '' Icc 0 1 ∩ arc e '' Icc 0 1) ⊆
        {point d.fst, point d.snd} ∩ {point e.fst, point e.snd})
    {u v : V} (p : G.Walk u v) (hp : p.IsPath) (hne : ¬ p.Nil) :
    ∃ gamma : ℝ → AnnulusCoordinates,
      ContinuousOn gamma (Icc 0 1) ∧ InjOn gamma (Icc 0 1) ∧
      gamma 0 = point u ∧ gamma 1 = point v ∧
      gamma '' Icc 0 1 = ⋃ d ∈ p.darts, arc d '' Icc 0 1 := by
  induction p with
  | nil => exact (hne .nil).elim
  | @cons u v w h p ih =>
    have hpath : p.IsPath := hp.of_cons
    have hu : u ∉ p.support := (SimpleGraph.Walk.cons_isPath_iff h p |>.mp hp).2
    let d : G.Dart := ⟨(u, v), h⟩
    by_cases hnil : p.Nil
    · cases p with
      | nil =>
        refine ⟨arc d, hcont d, hinj d, hstart d, hend d, ?_⟩
        simp [d]
      | cons h' p' => exact (SimpleGraph.Walk.not_nil_cons hnil).elim
    · obtain ⟨beta, hbc, hbi, hb0, hb1, hbimage⟩ := ih hpath hnil
      have hjoin : arc d 1 = beta 0 := (hend d).trans hb0.symm
      have hjoinmeet : ∀ s ∈ Icc 0 1, ∀ t ∈ Icc 0 1,
          arc d s = beta t → s = 1 ∧ t = 0 := by
        intro s hs t ht hst
        have htimage : beta t ∈ ⋃ e ∈ p.darts, arc e '' Icc 0 1 :=
          hbimage ▸ mem_image_of_mem beta ht
        obtain ⟨e, heimage⟩ := mem_iUnion.mp htimage
        obtain ⟨he, r, hr, her⟩ := mem_iUnion.mp heimage
        have hef : e.fst ∈ p.support := p.dart_fst_mem_support_of_mem_darts he
        have hes : e.snd ∈ p.support := p.dart_snd_mem_support_of_mem_darts he
        have hde : d.edge ≠ e.edge := by
          intro heq
          have heq' : e.edge = s(u, v) := heq.symm
          rcases SimpleGraph.dart_edge_eq_mk'_iff'.mp heq' with hh | hh
          · exact hu (hh.1 ▸ hef)
          · exact hu (hh.2 ▸ hes)
        have hends := hmeet d e hde
          ⟨mem_image_of_mem (arc d) hs, ⟨r, hr, her.trans hst.symm⟩⟩
        simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff] at hends
        have hsv : arc d s = point v := by
          rcases hends.1 with hsu | hsv
          · have hpu : arc d s = point u := hsu
            rcases hends.2 with hsef | hses
            · exact (hu ((hpoint (hpu.symm.trans hsef)).symm ▸ hef)).elim
            · exact (hu ((hpoint (hpu.symm.trans hses)).symm ▸ hes)).elim
          · exact hsv
        exact ⟨hinj d hs (by norm_num) (hsv.trans (hend d).symm),
          hbi ht (by norm_num) (hst.symm.trans (hsv.trans hb0.symm))⟩
      obtain ⟨gamma, hgc, hgi, hg0, hg1, hgimage⟩ :=
        m64Intrinsic_exists_embedded_join (hcont d) hbc (hinj d) hbi hjoin hjoinmeet
      refine ⟨gamma, hgc, hgi, hg0.trans (hstart d), hg1.trans hb1, ?_⟩
      rw [hgimage, hbimage, m64_dart_image_union_cons]

theorem m64Intrinsic_exists_region_between_graph_path_and_arc
    {V : Type*} {G : SimpleGraph V}
    (point : V → AnnulusCoordinates) (hpoint : Injective point)
    (arc : G.Dart → ℝ → AnnulusCoordinates)
    (hcont : ∀ d, ContinuousOn (arc d) (Icc 0 1))
    (hinj : ∀ d, InjOn (arc d) (Icc 0 1))
    (hstart : ∀ d, arc d 0 = point d.fst)
    (hend : ∀ d, arc d 1 = point d.snd)
    (hmeet : ∀ d e, d.edge ≠ e.edge →
      (arc d '' Icc 0 1 ∩ arc e '' Icc 0 1) ⊆
        {point d.fst, point d.snd} ∩ {point e.fst, point e.snd})
    {u v : V} (p : G.Walk u v) (hp : p.IsPath) (hne : ¬ p.Nil)
    {base : ℝ → AnnulusCoordinates}
    (hbase : ContinuousOn base (Icc 0 1)) (hbaseinj : InjOn base (Icc 0 1))
    (hbase0 : base 0 = point u) (hbase1 : base 1 = point v)
    (hbasemeet : ∀ d ∈ p.darts,
      base '' Icc 0 1 ∩ arc d '' Icc 0 1 ⊆ {point u, point v}) :
    ∃ U W : Set AnnulusCoordinates,
      IsOpen U ∧ IsOpen W ∧ IsPathConnected U ∧ IsPathConnected W ∧
      Bornology.IsBounded U ∧ ¬ Bornology.IsBounded W ∧ Disjoint U W ∧
      U ∪ W = (base '' Icc 0 1 ∪ (⋃ d ∈ p.darts, arc d '' Icc 0 1))ᶜ ∧
      frontier U = base '' Icc 0 1 ∪ (⋃ d ∈ p.darts, arc d '' Icc 0 1) ∧
      frontier W = base '' Icc 0 1 ∪ (⋃ d ∈ p.darts, arc d '' Icc 0 1) ∧
      IsCompact (closure U) := by
  obtain ⟨gamma, hgc, hgi, hg0, hg1, hgimage⟩ :=
    m64Intrinsic_exists_embedded_graph_path point hpoint arc hcont hinj hstart hend
      hmeet p hp hne
  have hbasegamma : ∀ s ∈ Icc 0 1, ∀ t ∈ Icc 0 1,
      base s = gamma t → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1) := by
    intro s hs t ht hst
    have htimage : gamma t ∈ ⋃ d ∈ p.darts, arc d '' Icc 0 1 :=
      hgimage ▸ mem_image_of_mem gamma ht
    obtain ⟨d, hdimage⟩ := mem_iUnion.mp htimage
    obtain ⟨hd, r, hr, hdr⟩ := mem_iUnion.mp hdimage
    have hends := hbasemeet d hd
      ⟨mem_image_of_mem base hs, ⟨r, hr, hdr.trans hst.symm⟩⟩
    simp only [mem_insert_iff, mem_singleton_iff] at hends
    rcases hends with hzero | hone
    · exact Or.inl
        ⟨hbaseinj hs (by norm_num) (hzero.trans hbase0.symm),
          hgi ht (by norm_num) (hst.symm.trans (hzero.trans hg0.symm))⟩
    · exact Or.inr
        ⟨hbaseinj hs (by norm_num) (hone.trans hbase1.symm),
          hgi ht (by norm_num) (hst.symm.trans (hone.trans hg1.symm))⟩
  simpa only [hgimage] using m64Intrinsic_exists_region_between_arcs hbase hgc
    hbaseinj hgi (hbase0.trans hg0.symm) (hbase1.trans hg1.symm) hbasegamma

end PoincareConjecture
