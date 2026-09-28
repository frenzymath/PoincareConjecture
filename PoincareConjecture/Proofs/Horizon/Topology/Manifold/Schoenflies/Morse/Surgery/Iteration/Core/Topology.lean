import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.Path
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.CapPreservation
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.ProtectedSets
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.SphereCircle.ParallelDisks.Charts

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

private instance : ConnectedSpace S2 := isConnected_iff_connectedSpace.mp
  (isConnected_sphere (by rw [← Module.finrank_eq_rank]; norm_num [E3])
    (0 : E3) zero_le_one)

private theorem isPreconnected_diff_of_connected_frontier
    {X : Type*} [TopologicalSpace X] {C U : Set X}
    (hC : IsPreconnected C) (hU : IsOpen U)
    (hUC : closure U ⊆ C) (hF : IsPreconnected (frontier U)) :
    IsPreconnected (C ∩ Uᶜ) := by
  apply isPreconnected_closed_iff.mpr
  intro t t' ht ht' hcover hCt hCt'
  by_contra hmeet
  have hFC : frontier U ⊆ C ∩ Uᶜ := by
    intro x hx
    rw [hU.frontier_eq] at hx
    exact ⟨hUC hx.1, hx.2⟩
  have hFcover : frontier U ⊆ t ∪ t' := hFC.trans hcover
  have hside : frontier U ⊆ t ∨ frontier U ⊆ t' := by
    by_cases hFt : (frontier U ∩ t).Nonempty
    · left
      intro x hx
      by_contra hxt
      have hxt' := (hFcover hx).resolve_left hxt
      obtain ⟨y, hy, hyt, hyt'⟩ := isPreconnected_closed_iff.mp hF
        t t' ht ht' hFcover hFt ⟨x, hx, hxt'⟩
      exact hmeet ⟨y, hFC hy, hyt, hyt'⟩
    · right
      intro x hx
      exact (hFcover hx).resolve_left (fun hxt => hFt ⟨x, hx, hxt⟩)
  have hremove : ∀ (s s' : Set X), IsClosed s → IsClosed s' →
      C ∩ Uᶜ ⊆ s ∪ s' → (C ∩ Uᶜ ∩ s).Nonempty →
      (C ∩ Uᶜ ∩ s').Nonempty → frontier U ⊆ s →
      (C ∩ Uᶜ ∩ (s ∩ s')).Nonempty := by
    intro s s' hs hs' hcov hCs hCs' hFs
    have hcov' : C ⊆ (s ∪ closure U) ∪ (s' ∩ Uᶜ) := by
      intro x hx
      by_cases hxU : x ∈ U
      · exact Or.inl (Or.inr (subset_closure hxU))
      · rcases hcov ⟨hx, hxU⟩ with hxs | hxs'
        · exact Or.inl (Or.inl hxs)
        · exact Or.inr ⟨hxs', hxU⟩
    obtain ⟨x, hxC, hxs, hxs', hxU⟩ := isPreconnected_closed_iff.mp hC
      (s ∪ closure U) (s' ∩ Uᶜ) (hs.union isClosed_closure)
      (hs'.inter hU.isClosed_compl) hcov'
      (hCs.mono (fun _ hx => ⟨hx.1.1, Or.inl hx.2⟩))
      (hCs'.mono (fun _ hx => ⟨hx.1.1, hx.2, hx.1.2⟩))
    refine ⟨x, ⟨hxC, hxU⟩, ?_, hxs'⟩
    exact hxs.elim id (fun hxcl => hFs (by rw [hU.frontier_eq]; exact ⟨hxcl, hxU⟩))
  rcases hside with hFt | hFt'
  · exact hmeet (hremove t t' ht ht' hcover hCt hCt' hFt)
  · have hcover' : C ∩ Uᶜ ⊆ t' ∪ t := by simpa only [union_comm] using hcover
    obtain ⟨x, hx, hxt', hxt⟩ := hremove t' t ht' ht hcover' hCt' hCt hFt'
    exact hmeet ⟨x, hx, hxt, hxt'⟩

namespace SphereSurgeryPath

variable {v : E3}

def PreservesCaps : {f g : S2 → E3} → SphereSurgeryPath v f g → Prop
  | _, _, .refl _ => True
  | _, _, .minus S next => next.Protects S.capMinusHeights ∧ next.PreservesCaps
  | _, _, .plus S next => next.Protects S.capPlusHeights ∧ next.PreservesCaps

theorem Protects.mono {f g : S2 → E3} {P : SphereSurgeryPath v f g}
    {B C : Set Real} (hP : P.Protects B) (hCB : C ⊆ B) : P.Protects C := by
  induction P with
  | refl => trivial
  | minus S next ih => exact ⟨fun k hk => hP.1 k (hCB hk), ih hP.2⟩
  | plus S next ih => exact ⟨fun k hk => hP.1 k (hCB hk), ih hP.2⟩

theorem protected_preconnected_core_dichotomy
    {f g : S2 → E3} (P : SphereSurgeryPath v f g) {B : Set Real}
    (hprotects : P.Protects B) {K : Set S2} (hK : IsPreconnected K)
    (hheight : ∀ p ∈ K, inner Real v (f p) ∈ B) :
    (K ⊆ interior P.core ∧ ∀ p ∈ K, g =ᶠ[𝓝 p] f) ∨ Disjoint K P.core := by
  induction P with
  | refl => exact Or.inl ⟨by simp [core], fun _ _ => Filter.EventuallyEq.rfl⟩
  | minus S next ih =>
    rcases S.protected_preconnected_survives hK
      (fun p hp => hprotects.1 _ (hheight p hp)) with ⟨hM, hMeq⟩ | ⟨hP, hPeq⟩
    · have hchild : ∀ p ∈ K, inner Real v (S.fMinus p) ∈ B := by
        intro p hp
        rw [(hMeq p hp).self_of_nhds]
        exact hheight p hp
      rcases ih hprotects.2 hchild with ⟨hcore, heq⟩ | hdis
      · refine Or.inl ⟨?_, fun p hp => (heq p hp).trans (hMeq p hp)⟩
        intro p hp
        rw [core, interior_inter]
        exact ⟨hcore hp, by
          rw [← S.eMinus.image_ball_eq_interior S.eMinus_source rfl]
          exact hM hp⟩
      · exact Or.inr (hdis.mono_right inter_subset_left)
    · apply Or.inr
      apply S.retained_disjoint.symm.mono
        (hP.trans (image_mono ball_subset_closedBall)) inter_subset_right
  | plus S next ih =>
    rcases S.protected_preconnected_survives hK
      (fun p hp => hprotects.1 _ (hheight p hp)) with ⟨hM, hMeq⟩ | ⟨hP, hPeq⟩
    · apply Or.inr
      apply S.retained_disjoint.mono
        (hM.trans (image_mono ball_subset_closedBall)) inter_subset_right
    · have hchild : ∀ p ∈ K, inner Real v (S.fPlus p) ∈ B := by
        intro p hp
        rw [(hPeq p hp).self_of_nhds]
        exact hheight p hp
      rcases ih hprotects.2 hchild with ⟨hcore, heq⟩ | hdis
      · refine Or.inl ⟨?_, fun p hp => (heq p hp).trans (hPeq p hp)⟩
        intro p hp
        rw [core, interior_inter]
        exact ⟨hcore hp, by
          rw [← S.ePlus.image_ball_eq_interior S.ePlus_source rfl]
          exact hP hp⟩
      · exact Or.inr (hdis.mono_right inter_subset_left)

private theorem add_disk_to_complement
    (C : Set S2) (d : OpenPartialHomeomorph E2 S2)
    (hds : closedBall 0 1 ⊆ d.source)
    (hd : ContMDiffOn (𝓡 2) (𝓡 2) ∞ d d.source)
    (hdi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ d.symm d.target)
    (hposition : d '' closedBall 0 1 ⊆ interior C ∨ Disjoint (d '' closedBall 0 1) C)
    (L : List (OpenPartialHomeomorph E2 S2))
    (hL : ∀ e ∈ L, closedBall 0 1 ⊆ e.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    (hpair : L.Pairwise (fun (e e' : OpenPartialHomeomorph E2 S2) =>
      Disjoint (e '' closedBall 0 1) (e' '' closedBall 0 1)))
    (hC : C = (⋃ e ∈ L, e '' ball 0 1)ᶜ) :
    ∃ L' : List (OpenPartialHomeomorph E2 S2),
      (∀ e ∈ L', closedBall 0 1 ⊆ e.source ∧
        ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source ∧
        ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target) ∧
      L'.Pairwise (fun (e e' : OpenPartialHomeomorph E2 S2) =>
        Disjoint (e '' closedBall 0 1) (e' '' closedBall 0 1)) ∧
      C ∩ (d '' ball 0 1)ᶜ = (⋃ e ∈ L', e '' ball 0 1)ᶜ := by
  rcases hposition with hin | hout
  · refine ⟨d :: L, ?_, List.pairwise_cons.mpr ⟨?_, hpair⟩, ?_⟩
    · intro e he
      rcases List.mem_cons.mp he with rfl | he
      · exact ⟨hds, hd, hdi⟩
      · exact hL e he
    · intro e he
      have hdis : Disjoint (e '' ball 0 1) (interior C) := by
        apply Set.disjoint_left.mpr
        intro p hp hpi
        have hpC : p ∈ C := interior_subset hpi
        rw [hC] at hpC
        exact hpC (mem_iUnion_of_mem e (mem_iUnion_of_mem he hp))
      have hclosed := hdis.closure_left isOpen_interior
      rw [ParallelDisks.closure_image_ball zero_lt_one e (hL e he).1] at hclosed
      exact (hclosed.mono_right hin).symm
    · rw [hC]
      ext p
      simp only [mem_inter_iff, mem_compl_iff, mem_iUnion, List.mem_cons]
      constructor
      · rintro ⟨hL, hd⟩ ⟨e, he, hp⟩
        rcases he with rfl | he
        · exact hd hp
        · exact hL ⟨e, he, hp⟩
      · intro h
        exact ⟨fun ⟨e, he, hp⟩ => h ⟨e, Or.inr he, hp⟩,
          fun hp => h ⟨d, Or.inl rfl, hp⟩⟩
  · refine ⟨L, hL, hpair, ?_⟩
    rw [← hC]
    apply inter_eq_left.mpr
    intro p hp hdisk
    exact Set.disjoint_left.mp hout (image_mono ball_subset_closedBall hdisk) hp

theorem exists_disjoint_disk_complement
    {f g : S2 → E3} (P : SphereSurgeryPath v f g) (hcaps : P.PreservesCaps) :
    ∃ L : List (OpenPartialHomeomorph E2 S2),
      (∀ e ∈ L, closedBall 0 1 ⊆ e.source ∧
        ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source ∧
        ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target) ∧
      L.Pairwise (fun (e e' : OpenPartialHomeomorph E2 S2) =>
        Disjoint (e '' closedBall 0 1) (e' '' closedBall 0 1)) ∧
      P.core = (⋃ e ∈ L, e '' ball 0 1)ᶜ := by
  induction P with
  | refl => exact ⟨[], by simp, by simp, by simp [core]⟩
  | minus S next ih =>
    obtain ⟨L, hL, hpair, hcore⟩ := ih hcaps.2
    have hconn : IsPreconnected (S.dMinus '' closedBall 0 1) :=
      ((isConnected_closedBall (by norm_num : (0 : Real) ≤ 1)).image S.dMinus
        (S.dMinus.continuousOn.mono S.dMinus_source)).isPreconnected
    have hheight : ∀ p ∈ S.dMinus '' closedBall 0 1,
        inner Real v (S.fMinus p) ∈ S.capMinusHeights := by
      rintro p ⟨x, hx, rfl⟩
      rw [S.capMinus_eq x hx]
      exact ⟨x, hx, rfl⟩
    have hpos := next.protected_preconnected_core_dichotomy hcaps.1 hconn hheight
    obtain ⟨L', hL', hpair', hcore'⟩ := add_disk_to_complement next.core S.dMinus
      S.dMinus_source S.dMinus_smooth S.dMinus_symm_smooth
      (hpos.imp And.left id) L hL hpair hcore
    refine ⟨L', hL', hpair', ?_⟩
    simpa only [core, S.dMinus_open, compl_compl] using hcore'
  | plus S next ih =>
    obtain ⟨L, hL, hpair, hcore⟩ := ih hcaps.2
    have hconn : IsPreconnected (S.dPlus '' closedBall 0 1) :=
      ((isConnected_closedBall (by norm_num : (0 : Real) ≤ 1)).image S.dPlus
        (S.dPlus.continuousOn.mono S.dPlus_source)).isPreconnected
    have hheight : ∀ p ∈ S.dPlus '' closedBall 0 1,
        inner Real v (S.fPlus p) ∈ S.capPlusHeights := by
      rintro p ⟨x, hx, rfl⟩
      rw [S.capPlus_eq x hx]
      exact ⟨x, hx, rfl⟩
    have hpos := next.protected_preconnected_core_dichotomy hcaps.1 hconn hheight
    obtain ⟨L', hL', hpair', hcore'⟩ := add_disk_to_complement next.core S.dPlus
      S.dPlus_source S.dPlus_smooth S.dPlus_symm_smooth
      (hpos.imp And.left id) L hL hpair hcore
    refine ⟨L', hL', hpair', ?_⟩
    simpa only [core, S.dPlus_open, compl_compl] using hcore'

private theorem isConnected_remove_disk
    {C : Set S2} (hC : IsConnected C) (d : OpenPartialHomeomorph E2 S2)
    (hds : closedBall 0 1 ⊆ d.source)
    (hd : ContMDiffOn (𝓡 2) (𝓡 2) ∞ d d.source)
    (hdi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ d.symm d.target)
    (hposition : d '' closedBall 0 1 ⊆ interior C ∨ Disjoint (d '' closedBall 0 1) C) :
    IsConnected (C ∩ (d '' ball 0 1)ᶜ) := by
  rcases hposition with hin | hout
  · have hopen := d.isOpen_image_of_subset_source isOpen_ball
      (ball_subset_closedBall.trans hds)
    have hfront : IsConnected (frontier (d '' ball 0 1)) := by
      rw [ParallelDisks.frontier_image_ball zero_lt_one d hds hd hdi]
      exact (isConnected_sphere (E := E2)
        (by rw [← Module.finrank_eq_rank]; norm_num) 0 zero_le_one).image d
        (d.continuousOn.mono (sphere_subset_closedBall.trans hds))
    have hclosure : closure (d '' ball 0 1) ⊆ C := by
      rw [ParallelDisks.closure_image_ball zero_lt_one d hds]
      exact hin.trans interior_subset
    refine ⟨?_, isPreconnected_diff_of_connected_frontier hC.isPreconnected hopen
      hclosure hfront.isPreconnected⟩
    obtain ⟨p, hp⟩ := hfront.nonempty
    rw [hopen.frontier_eq] at hp
    exact ⟨p, hclosure hp.1, hp.2⟩
  · have heq : C ∩ (d '' ball 0 1)ᶜ = C := by
      apply inter_eq_left.mpr
      intro p hp hdisk
      exact Set.disjoint_left.mp hout (image_mono ball_subset_closedBall hdisk) hp
    rwa [heq]

theorem isConnected_core {f g : S2 → E3}
    (P : SphereSurgeryPath v f g) (hcaps : P.PreservesCaps) : IsConnected P.core := by
  induction P with
  | refl => exact isConnected_univ
  | minus S next ih =>
    have hconn : IsPreconnected (S.dMinus '' closedBall 0 1) :=
      ((isConnected_closedBall (by norm_num : (0 : Real) ≤ 1)).image S.dMinus
        (S.dMinus.continuousOn.mono S.dMinus_source)).isPreconnected
    have hheight : ∀ p ∈ S.dMinus '' closedBall 0 1,
        inner Real v (S.fMinus p) ∈ S.capMinusHeights := by
      rintro p ⟨x, hx, rfl⟩
      rw [S.capMinus_eq x hx]
      exact ⟨x, hx, rfl⟩
    have hpos := next.protected_preconnected_core_dichotomy hcaps.1 hconn hheight
    have hconnected := isConnected_remove_disk (ih hcaps.2) S.dMinus
      S.dMinus_source S.dMinus_smooth S.dMinus_symm_smooth (hpos.imp And.left id)
    simpa only [core, S.dMinus_open, compl_compl] using hconnected
  | plus S next ih =>
    have hconn : IsPreconnected (S.dPlus '' closedBall 0 1) :=
      ((isConnected_closedBall (by norm_num : (0 : Real) ≤ 1)).image S.dPlus
        (S.dPlus.continuousOn.mono S.dPlus_source)).isPreconnected
    have hheight : ∀ p ∈ S.dPlus '' closedBall 0 1,
        inner Real v (S.fPlus p) ∈ S.capPlusHeights := by
      rintro p ⟨x, hx, rfl⟩
      rw [S.capPlus_eq x hx]
      exact ⟨x, hx, rfl⟩
    have hpos := next.protected_preconnected_core_dichotomy hcaps.1 hconn hheight
    have hconnected := isConnected_remove_disk (ih hcaps.2) S.dPlus
      S.dPlus_source S.dPlus_smooth S.dPlus_symm_smooth (hpos.imp And.left id)
    simpa only [core, S.dPlus_open, compl_compl] using hconnected

end SphereSurgeryPath

namespace SphereSurgeryTree

variable {v : E3} {A : Finset Real} {f g : S2 → E3} {B : Set Real}

theorem Protects.union {tree : SphereSurgeryTree v A f} {C : Set Real}
    (hB : tree.Protects B) (hC : tree.Protects C) : tree.Protects (B ∪ C) := by
  induction tree with
  | leaf => trivial
  | branch hc hsep S minus plus ihM ihP =>
    exact ⟨fun k hk => hk.elim (hB.1 k) (hC.1 k),
      ihM hB.2.1 hC.2.1, ihP hB.2.2 hC.2.2⟩

theorem exists_cap_preserving_path_to_leaf
    (tree : SphereSurgeryTree v A f) (hg : g ∈ tree.leaves)
    (hprotects : tree.Protects B) (hcaps : tree.PreservesCaps) :
    ∃ P : SphereSurgeryPath v f g, P.Protects B ∧ P.PreservesCaps := by
  induction tree generalizing B with
  | leaf hf hav =>
    simp only [leaves, List.mem_singleton] at hg
    subst g
    exact ⟨.refl _, trivial, trivial⟩
  | branch hc hsep S minus plus ihM ihP =>
    rcases List.mem_append.mp hg with hM | hP
    · obtain ⟨P, hPB, hPC⟩ := ihM hM (hprotects.2.1.union hcaps.1) hcaps.2.2.1
      exact ⟨.minus S P, ⟨hprotects.1, hPB.mono subset_union_left⟩,
        ⟨hPB.mono subset_union_right, hPC⟩⟩
    · obtain ⟨P, hPB, hPC⟩ := ihP hP (hprotects.2.2.union hcaps.2.1) hcaps.2.2.2
      exact ⟨.plus S P, ⟨hprotects.1, hPB.mono subset_union_left⟩,
        ⟨hPB.mono subset_union_right, hPC⟩⟩

end SphereSurgeryTree

end Poincare.Manifold.Schoenflies
