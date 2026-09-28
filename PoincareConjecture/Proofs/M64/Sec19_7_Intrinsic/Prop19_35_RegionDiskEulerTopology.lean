import PoincareConjecture.Proofs.M64.Mathlib.SupportMinimal
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RegionDiskEulerCycles
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RegionDiskEulerPaths
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RegionDiskEulerColoring












noncomputable section
set_option autoImplicit false

open Set Function
open PoincareConjecture.Surface.Combinatorial.Incidence

namespace PoincareConjecture





theorem m64Intrinsic_midpoint_mem_selected_edge_union
    {X E : Type*} (edge : E → ℝ → X)
    (hinj : ∀ e, InjOn (edge e) (Icc 0 1))
    (hmeet : ∀ e f, e ≠ f →
      edge e '' Icc 0 1 ∩ edge f '' Icc 0 1 ⊆ {edge e 0, edge e 1})
    (S : Set E) (e : E) :
    edge e (1 / 2) ∈ (⋃ f ∈ S, edge f '' Icc 0 1) ↔ e ∈ S := by
  constructor
  · intro hmem
    obtain ⟨f, hf⟩ := mem_iUnion.mp hmem
    obtain ⟨hfS, hpf⟩ := mem_iUnion.mp hf
    by_cases hef : e = f
    · simpa only [hef] using hfS
    · have hpends := hmeet e f hef
        ⟨mem_image_of_mem (edge e) (by norm_num : (1 / 2 : ℝ) ∈ Icc 0 1), hpf⟩
      rcases hpends with hp0 | hp1
      · have := hinj e (by norm_num : (1 / 2 : ℝ) ∈ Icc 0 1) (by norm_num) hp0
        norm_num at this
      · have := hinj e (by norm_num : (1 / 2 : ℝ) ∈ Icc 0 1) (by norm_num)
          (mem_singleton_iff.mp hp1)
        norm_num at this
  · intro he
    exact mem_iUnion.mpr ⟨e, mem_iUnion.mpr ⟨he,
      mem_image_of_mem (edge e) (by norm_num : (1 / 2 : ℝ) ∈ Icc 0 1)⟩⟩






theorem m64Intrinsic_plane_graph_cycle_fill
    {V E I : Type*} [Finite V] [Fintype E] [Fintype I]
    (ends : E → V × V) (point : V → AnnulusCoordinates) (hpoint : Injective point)
    (edge : E → ℝ → AnnulusCoordinates)
    (hcont : ∀ e, ContinuousOn (edge e) (Icc 0 1))
    (hinj : ∀ e, InjOn (edge e) (Icc 0 1))
    (hstart : ∀ e, edge e 0 = point (ends e).1)
    (hend : ∀ e, edge e 1 = point (ends e).2)
    (hmeet : ∀ e f, e ≠ f →
      edge e '' Icc 0 1 ∩ edge f '' Icc 0 1 ⊆ {edge e 0, edge e 1})
    (A : I → Set AnnulusCoordinates) (hclosed : ∀ i, IsClosed (A i))
    (hregular : ∀ i, closure (interior (A i)) = A i)
    (hconnected : ∀ i, IsPreconnected (interior (A i)))
    (hcover : (⋃ i, A i) = univ)
    (havoid : ∀ i, Disjoint (interior (A i)) (⋃ e, edge e '' Icc 0 1))
    (adjacent : E → I × I)
    (hinc : ∀ e i, edge e (1 / 2) ∈ A i ↔ i = (adjacent e).1 ∨ i = (adjacent e).2) :
    LinearMap.ker (incidenceMatrix ends).transpose.mulVecLin ≤
      LinearMap.range (incidenceMatrix adjacent).mulVecLin := by
  classical
  apply Submodule.le_of_mem_of_support_minimal
  intro x hx hnonzero hminimal
  obtain ⟨e0, hx0⟩ : ∃ e, x e ≠ 0 := by
    by_contra h
    apply hnonzero
    funext e
    push Not at h
    exact h e
  have he0 : (ends e0).1 ≠ (ends e0).2 := by
    intro heq
    have h01 : edge e0 0 = edge e0 1 := by rw [hstart, hend, heq]
    have := hinj e0 (by norm_num) (by norm_num) h01
    norm_num at this
  obtain ⟨p, hp, chosen, hchosen, hsupport⟩ :=
    m64Intrinsic_minimal_cycle_eq_edge_union_path ends x e0 (LinearMap.mem_ker.mp hx)
      hx0 he0 (fun y hy => hminimal y (LinearMap.mem_ker.mpr hy))
  let G := m64SelectedEdgeDeletionGraph ends x e0
  have horient (d : G.Dart) :
      ∃ alpha : ℝ → AnnulusCoordinates,
        ContinuousOn alpha (Icc 0 1) ∧ InjOn alpha (Icc 0 1) ∧
        alpha 0 = point d.fst ∧ alpha 1 = point d.snd ∧
        alpha '' Icc 0 1 = edge (chosen d) '' Icc 0 1 := by
    apply m64Intrinsic_exists_oriented_embedded_arc (hcont (chosen d)) (hinj (chosen d))
    rcases (hchosen d).2.2 with h | h
    · exact Or.inl ⟨(hstart _).trans (congrArg point h.1),
        (hend _).trans (congrArg point h.2)⟩
    · exact Or.inr ⟨(hstart _).trans (congrArg point h.1),
        (hend _).trans (congrArg point h.2)⟩
  choose arc harcc harci harc0 harc1 harcimage using horient
  have hpair (d : G.Dart) :
      ({edge (chosen d) 0, edge (chosen d) 1} : Set AnnulusCoordinates) =
        {point d.fst, point d.snd} := by
    rw [hstart, hend]
    rcases (hchosen d).2.2 with h | h
    · rw [h.1, h.2]
    · rw [h.1, h.2, pair_comm]
  have hdedge (d : G.Dart) : d.edge = s((ends (chosen d)).1, (ends (chosen d)).2) := by
    change s(d.fst, d.snd) = _
    rcases (hchosen d).2.2 with h | h
    · rw [h.1, h.2]
    · rw [h.1, h.2]
      exact Sym2.eq_swap
  have harcmeet (d f : G.Dart) (hdf : d.edge ≠ f.edge) :
      arc d '' Icc 0 1 ∩ arc f '' Icc 0 1 ⊆
        {point d.fst, point d.snd} ∩ {point f.fst, point f.snd} := by
    have hchosen_ne : chosen d ≠ chosen f := by
      intro h
      apply hdf
      rw [hdedge d, hdedge f, h]
    rw [harcimage d, harcimage f, ← hpair d, ← hpair f]
    intro z hz
    exact ⟨hmeet _ _ hchosen_ne hz, hmeet _ _ hchosen_ne.symm ⟨hz.2, hz.1⟩⟩
  have hbasemeet (d : G.Dart) (_hd : d ∈ p.darts) :
      edge e0 '' Icc 0 1 ∩ arc d '' Icc 0 1 ⊆
        {point (ends e0).1, point (ends e0).2} := by
    rw [harcimage d, ← hstart e0, ← hend e0]
    exact hmeet _ _ (hchosen d).1.symm
  obtain ⟨U, W, hU, hW, _, _, _, _, hdisjoint, hpartition, hfrontU, hfrontW, _⟩ :=
    m64Intrinsic_exists_region_between_graph_path_and_arc point hpoint arc harcc harci
      harc0 harc1 harcmeet p hp (SimpleGraph.Walk.not_nil_of_ne he0)
      (hcont e0) (hinj e0) (hstart e0) (hend e0) hbasemeet
  let K := edge e0 '' Icc 0 1 ∪ ⋃ d ∈ p.darts, arc d '' Icc 0 1
  have hKimage : K = ⋃ e ∈ Function.support x, edge e '' Icc 0 1 := by
    apply subset_antisymm
    · intro z hz
      rcases hz with hz | hz
      · exact mem_iUnion.mpr ⟨e0, mem_iUnion.mpr ⟨hx0, hz⟩⟩
      · obtain ⟨d, hd⟩ := mem_iUnion.mp hz
        obtain ⟨_hdp, hzarc⟩ := mem_iUnion.mp hd
        exact mem_iUnion.mpr ⟨chosen d,
          mem_iUnion.mpr ⟨(hchosen d).2.1, harcimage d ▸ hzarc⟩⟩
    · intro z hz
      obtain ⟨e, he⟩ := mem_iUnion.mp hz
      obtain ⟨hxe, hze⟩ := mem_iUnion.mp he
      rcases (hsupport e).mp hxe with he0 | ⟨d, hdp, hde⟩
      · exact Or.inl (he0 ▸ hze)
      · exact Or.inr (mem_iUnion.mpr ⟨d, mem_iUnion.mpr ⟨hdp, by
          rw [harcimage d, hde]
          exact hze⟩⟩)
  have hKsub : K ⊆ ⋃ e, edge e '' Icc 0 1 := by
    rw [hKimage]
    intro z hz
    obtain ⟨e, he⟩ := mem_iUnion.mp hz
    obtain ⟨_, hze⟩ := mem_iUnion.mp he
    exact mem_iUnion.mpr ⟨e, hze⟩
  have hselected (e : E) : edge e (1 / 2) ∈ K ↔ x e ≠ 0 := by
    rw [hKimage]
    exact m64Intrinsic_midpoint_mem_selected_edge_union edge hinj hmeet (Function.support x) e
  exact m64Intrinsic_region_cycle_fill_of_jordan_partition A hclosed hregular hconnected hcover
    hU hW hdisjoint hpartition hfrontU hfrontW
    (fun i => (havoid i).mono_right hKsub) adjacent (fun e => edge e (1 / 2)) hinc x hselected

end PoincareConjecture
