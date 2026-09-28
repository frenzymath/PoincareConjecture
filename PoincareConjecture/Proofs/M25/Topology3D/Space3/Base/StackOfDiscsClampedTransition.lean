import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsTransition

set_option autoImplicit false

open Set Metric
open scoped ContDiff

namespace PoincareConjecture.M25.Topology3D

theorem exists_stackClampedDiscTransition
    (T G : OpenPartialHomeomorph (E2 × ℝ) (E2 × ℝ))
    (hT : ContDiffOn ℝ ∞ T T.source) (hTi : ContDiffOn ℝ ∞ T.symm T.target)
    (hG : ContDiffOn ℝ ∞ G G.source) (hGi : ContDiffOn ℝ ∞ G.symm G.target)
    (hTh : ∀ p ∈ T.source, (T p).2 = p.2)
    (hGh : ∀ p ∈ G.source, (G p).2 = p.2)
    (I : Set ℝ) (hI : IsCompact I)
    (hTs : closedBall (0 : E2) 1 ×ˢ I ⊆ T.source)
    (hGs : closedBall (0 : E2) 1 ×ˢ I ⊆ G.source)
    (hboundary : ∀ z ∈ I,
      (fun x : E2 => (T (x, z)).1) '' sphere (0 : E2) 1 =
        (fun x : E2 => (G (x, z)).1) '' sphere (0 : E2) 1)
    (k : ℝ → ℝ) (hk : ContDiff ℝ ∞ k) (hkI : ∀ z, k z ∈ I) :
    ∃ r : ℝ, 1 < r ∧ ∃ E : OpenPartialHomeomorph (ℝ × E2) (ℝ × E2),
      (∀ p, E p = (p.1, (G.symm (T (p.2, k p.1))).1)) ∧
      (∀ p, E.symm p = (p.1, (T.symm (G (p.2, k p.1))).1)) ∧
      E.source = {p | (p.2, k p.1) ∈ (T.trans G.symm).source} ∧
      E.target = {p | (p.2, k p.1) ∈ (T.trans G.symm).target} ∧
      ContDiffOn ℝ ∞ E E.source ∧ ContDiffOn ℝ ∞ E.symm E.target ∧
      (∀ p, (E p).1 = p.1 ∧ (E.symm p).1 = p.1) ∧
      (univ ×ˢ ball (0 : E2) r ⊆ E.source) ∧
      (univ ×ˢ ball (0 : E2) r ⊆ E.target) ∧
      (∀ J : Set ℝ, ∀ A : Set E2,
        (A = ball 0 1 ∨ A = closedBall 0 1 ∨ A = sphere 0 1) →
        E '' (J ×ˢ A) = J ×ˢ A ∧ E.symm '' (J ×ˢ A) = J ×ˢ A) ∧
      ∀ z, k z = z → ∀ x ∈ closedBall (0 : E2) 1,
        ((E (z, x)).2, z) ∈ G.source ∧
        G ((E (z, x)).2, z) = T (x, z) ∧
        ((E.symm (z, x)).2, z) ∈ T.source ∧
        T ((E.symm (z, x)).2, z) = G (x, z) := by
  let F := T.trans G.symm
  obtain ⟨hF, hFi, hFh, hFih, hFs, hFt, hProduct⟩ :=
    stackDiscTransition_spec T G hT hTi hG hGi hTh hGh I hTs hGs hboundary
  obtain ⟨rs, hrs, hsource⟩ :=
    exists_saddle_end_disc_buffer I hI F.source F.open_source hFs
  obtain ⟨rt, hrt, htarget⟩ :=
    exists_saddle_end_disc_buffer I hI F.target F.open_target hFt
  let r := min rs rt
  have hr : 1 < r := lt_min hrs hrt
  obtain ⟨f, hfapply, hfinv, hfs, hft, hf, hfi, _hfh⟩ :=
    exists_saddle_end_chart_reparam F hF hFi hFh k hk
  let P := ContinuousLinearEquiv.prodComm ℝ ℝ E2
  let E := (P.toHomeomorph.transOpenPartialHomeomorph f).transHomeomorph
    P.symm.toHomeomorph
  have hEapply (p : ℝ × E2) : E p = (p.1, (F (p.2, k p.1)).1) := by
    change ((f (p.2, p.1)).2, (f (p.2, p.1)).1) = _
    rw [hfapply]
  have hEinv (p : ℝ × E2) : E.symm p = (p.1, (F.symm (p.2, k p.1)).1) := by
    change ((f.symm (p.2, p.1)).2, (f.symm (p.2, p.1)).1) = _
    rw [hfinv]
  have hEs : E.source = {p | (p.2, k p.1) ∈ F.source} := by
    ext p
    change (p.2, p.1) ∈ f.source ↔ _
    rw [hfs]
    rfl
  have hEt : E.target = {p | (p.2, k p.1) ∈ F.target} := by
    ext p
    change (p.2, p.1) ∈ f.target ↔ _
    rw [hft]
    rfl
  have hE : ContDiffOn ℝ ∞ E E.source :=
    P.symm.contDiff.comp_contDiffOn
      (hf.comp P.contDiff.contDiffOn (fun _ hp => hp))
  have hEi : ContDiffOn ℝ ∞ E.symm E.target :=
    P.symm.contDiff.comp_contDiffOn
      (hfi.comp P.contDiff.contDiffOn (fun _ hp => hp))
  have hEsource : univ ×ˢ ball (0 : E2) r ⊆ E.source := by
    intro p hp
    rw [hEs]
    exact hsource ⟨ball_subset_ball (min_le_left rs rt) hp.2, hkI p.1⟩
  have hEtarget : univ ×ˢ ball (0 : E2) r ⊆ E.target := by
    intro p hp
    rw [hEt]
    exact htarget ⟨ball_subset_ball (min_le_right rs rt) hp.2, hkI p.1⟩
  refine ⟨r, hr, E, hEapply, hEinv, hEs, hEt, hE, hEi, ?_,
    hEsource, hEtarget, ?_, ?_⟩
  · intro p
    rw [hEapply, hEinv]
    exact ⟨rfl, rfl⟩
  · intro J A hA
    have hAsub : A ⊆ closedBall (0 : E2) 1 := by
      rcases hA with rfl | rfl | rfl
      · exact ball_subset_closedBall
      · exact subset_rfl
      · exact sphere_subset_closedBall
    have hJ (z : ℝ) : ({k z} : Set ℝ) ⊆ I := by
      intro w hw
      rw [mem_singleton_iff.mp hw]
      exact hkI z
    have hforward (p : ℝ × E2) (hp : p ∈ J ×ˢ A) :
        p ∈ E.source ∧ E p ∈ J ×ˢ A := by
      have hm : F (p.2, k p.1) ∈ A ×ˢ ({k p.1} : Set ℝ) := by
        rw [← (hProduct {k p.1} (hJ p.1) A hA).1]
        exact mem_image_of_mem F ⟨hp.2, rfl⟩
      refine ⟨hEsource ⟨mem_univ _, closedBall_subset_ball hr (hAsub hp.2)⟩, ?_⟩
      rw [hEapply]
      exact ⟨hp.1, hm.1⟩
    have hinverse (p : ℝ × E2) (hp : p ∈ J ×ˢ A) :
        p ∈ E.target ∧ E.symm p ∈ J ×ˢ A := by
      have hm : F.symm (p.2, k p.1) ∈ A ×ˢ ({k p.1} : Set ℝ) := by
        rw [← (hProduct {k p.1} (hJ p.1) A hA).2]
        exact mem_image_of_mem F.symm ⟨hp.2, rfl⟩
      refine ⟨hEtarget ⟨mem_univ _, closedBall_subset_ball hr (hAsub hp.2)⟩, ?_⟩
      rw [hEinv]
      exact ⟨hp.1, hm.1⟩
    constructor
    · apply Subset.antisymm
      · rintro _ ⟨p, hp, rfl⟩
        exact (hforward p hp).2
      · intro p hp
        exact ⟨E.symm p, (hinverse p hp).2, E.right_inv (hinverse p hp).1⟩
    · apply Subset.antisymm
      · rintro _ ⟨p, hp, rfl⟩
        exact (hinverse p hp).2
      · intro p hp
        exact ⟨E p, (hforward p hp).2, E.left_inv (hforward p hp).1⟩
  · intro z hkz x hx
    have hz : z ∈ I := hkz ▸ hkI z
    have hxs : (x, z) ∈ F.source := hFs ⟨hx, hz⟩
    have hxt : (x, z) ∈ F.target := hFt ⟨hx, hz⟩
    have hpoint : ((E (z, x)).2, z) = F (x, z) := by
      rw [hEapply, hkz]
      exact Prod.ext rfl (hFh _ hxs).symm
    have hinvpoint : ((E.symm (z, x)).2, z) = F.symm (x, z) := by
      rw [hEinv, hkz]
      exact Prod.ext rfl (hFih _ hxt).symm
    rw [hpoint, hinvpoint]
    exact ⟨(F.map_source hxs).1, G.right_inv hxs.2,
      (F.map_target hxt).1, T.right_inv hxt.2⟩

end PoincareConjecture.M25.Topology3D
