import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.OneCritical.SaddleEnds.Orientation

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.SphereSurgeryCoreCap

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1

private instance : ConnectedSpace S1 :=
  isConnected_iff_connectedSpace.mp
    (isConnected_sphere (by simp [← Module.finrank_eq_rank, E2]) (0 : E2) zero_le_one)

variable {v : E3} {g : S2 → E3} {B : Set Real}

private theorem closure_image_open_strip
    (F : OpenPartialHomeomorph (S1 × Real) S2) {a b : Real} (hab : a < b)
    (hsub : univ ×ˢ Icc a b ⊆ F.source) :
    F '' (univ ×ˢ Icc a b) ⊆ closure (F '' (univ ×ˢ Ioo a b)) := by
  have hclosure : closure (univ ×ˢ Ioo a b : Set (S1 × Real)) = univ ×ˢ Icc a b := by
    rw [closure_prod_eq, closure_univ, closure_Ioo hab.ne]
  have hcont : ContinuousOn F (closure (univ ×ˢ Ioo a b)) := by
    rw [hclosure]
    exact F.continuousOn.mono hsub
  simpa only [hclosure] using hcont.image_closure

private theorem upper_open_strip_meets_core
    (L : List (SphereSurgeryCoreCap v g B))
    (hpair : L.Pairwise (fun D E => Disjoint
      (D.chart '' closedBall 0 1) (E.chart '' closedBall 0 1)))
    {C : Set S2} (hcore : C = (⋃ D ∈ L, D.chart '' ball 0 1)ᶜ)
    {h : S2 → Real}
    (F : OpenPartialHomeomorph (S1 × Real) S2) {l b u : Real}
    (hFs : F.source = univ ×ˢ Ioo l u)
    (hheight : ∀ q t, t ∈ Ioo l u → h (F (q, t)) = t)
    (D : SphereSurgeryCoreCap v g B) (hD : D ∈ L) (hs : D.scale < 0)
    (hld : l < D.center) (hdb : D.center < b) (hbu : b < u)
    {p : S2} (hp : p ∈ D.chart '' sphere (0 : E2) 1)
    (hpF : p ∈ F.target) (hpheight : h p = D.center)
    (hgerm : h =ᶠ[𝓝 p] (fun q => inner Real v (g q))) :
    (F '' (univ ×ˢ Ioo D.center b) ∩ C).Nonempty := by
  classical
  let J : Set (SphereSurgeryCoreCap v g B) := {E | E ∈ L ∧ E ≠ D}
  let K : Set S2 := ⋃ E ∈ J, E.chart '' closedBall 0 1
  have hfinite : {E : SphereSurgeryCoreCap v g B | E ∈ L}.Finite := by
    simpa only [List.coe_toFinset] using L.toFinset.finite_toSet
  have hJ : J.Finite := hfinite.subset (fun _ he => he.1)
  have hK : IsClosed K := hJ.isClosed_biUnion (fun E _ =>
    ((isCompact_closedBall 0 1).image_of_continuousOn
      (E.chart.continuousOn.mono E.source)).isClosed)
  have hpK : p ∉ K := by
    simp only [K, mem_iUnion]
    rintro ⟨E, hE, hpE⟩
    exact Set.disjoint_left.mp (hpair.forall hD hE.1 hE.2.symm)
      (image_mono sphere_subset_closedBall hp) hpE
  have hpnbhd : Kᶜ ∩ {z | h z = inner Real v (g z)} ∈ 𝓝 p :=
    Filter.inter_mem (hK.isOpen_compl.mem_nhds hpK) hgerm
  have hsub : univ ×ˢ Icc D.center b ⊆ F.source := by
    rintro ⟨q, t⟩ ⟨_, ht⟩
    exact hFs ▸ ⟨mem_univ _, hld.trans_le ht.1, ht.2.trans_lt hbu⟩
  have hpstrip : p ∈ F '' (univ ×ˢ Icc D.center b) := by
    have ht := hheight (F.symm p).1 (F.symm p).2 (hFs ▸ F.map_target hpF).2
    rw [F.right_inv hpF, hpheight] at ht
    refine ⟨F.symm p, ⟨mem_univ _, ?_⟩, F.right_inv hpF⟩
    rw [← ht]
    exact ⟨le_rfl, hdb.le⟩
  have hpcl := closure_image_open_strip F hdb hsub hpstrip
  obtain ⟨W, hWsub, hWopen, hpW⟩ := _root_.mem_nhds_iff.mp hpnbhd
  obtain ⟨z, hzW, hzstrip⟩ := mem_closure_iff.mp hpcl W hWopen hpW
  have hz := hWsub hzW
  refine ⟨z, hzstrip, ?_⟩
  rw [hcore]
  simp only [mem_compl_iff, mem_iUnion]
  rintro ⟨E, hE, hzE⟩
  by_cases heq : E = D
  · subst E
    have hn := mul_neg_of_pos_of_neg (D.normalized_height_pos_on_open_disk hzE) hs
    rw [div_mul_cancel₀ _ D.scale_ne_zero, ← hz.2] at hn
    obtain ⟨⟨q, t⟩, ⟨_, ht⟩, rfl⟩ := hzstrip
    rw [hheight q t ⟨hld.trans ht.1, ht.2.trans hbu⟩] at hn
    linarith [ht.1]
  · exact hz.1 (mem_iUnion_of_mem E (mem_iUnion_of_mem ⟨hE, heq⟩
      (image_mono ball_subset_closedBall hzE)))

theorem upper_closed_strip_subset_core
    (L : List (SphereSurgeryCoreCap v g B))
    (hpair : L.Pairwise (fun D E => Disjoint
      (D.chart '' closedBall 0 1) (E.chart '' closedBall 0 1)))
    {C : Set S2} (hcore : C = (⋃ D ∈ L, D.chart '' ball 0 1)ᶜ)
    (hC : IsPreconnected C) (hclosed : IsClosed C)
    {h : S2 → Real} (hh : Continuous h)
    (hgerm : ∀ p ∈ C, h =ᶠ[𝓝 p] (fun q => inner Real v (g q)))
    (F : OpenPartialHomeomorph (S1 × Real) S2) {a b l u : Real}
    (hla : l < a) (hbu : b < u)
    (hFs : F.source = univ ×ˢ Ioo l u)
    (hheight : ∀ q t, t ∈ Ioo l u → h (F (q, t)) = t)
    (hlower : ∀ p ∈ C, a ≤ h p)
    (hgreater : ∃ q ∈ C, b < h q)
    (D : SphereSurgeryCoreCap v g B) (hD : D ∈ L)
    (hDa : a ≤ D.center) (hDb : D.center < b)
    {p : S2} (hp : p ∈ D.chart '' sphere (0 : E2) 1)
    (hpF : p ∈ F.target) :
    D.scale < 0 ∧ F '' (univ ×ˢ Icc D.center b) ⊆ C ∧
      F '' (univ ×ˢ Ioo D.center b) ⊆ interior C := by
  have hboundary (E : SphereSurgeryCoreCap v g B) (hE : E ∈ L) :
      E.chart '' sphere (0 : E2) 1 ⊆ C := fun z hz =>
    ((core_inter_closed_disk L hpair hcore E hE).superset hz).1
  have hEheight (E : SphereSurgeryCoreCap v g B) (hE : E ∈ L) :
      ∀ z ∈ E.chart '' sphere (0 : E2) 1, h z = E.center :=
    fun z hz => ((hgerm z (hboundary E hE hz)).eq_of_nhds).trans
      (E.height_eq_on_boundary z hz)
  have hDc : D.center ∈ Ioo l u := ⟨hla.trans_le hDa, hDb.trans hbu⟩
  have hs : D.scale < 0 := scale_neg_of_lower_annulus L hpair hcore hC hh hgerm F
    hla hFs hheight hlower D hD hDc hp hpF
      (by obtain ⟨q, hq, hqh⟩ := hgreater; exact ⟨q, hq, hDb.trans hqh⟩)
  let V := F '' (univ ×ˢ Ioo D.center b)
  have hsub : univ ×ˢ Icc D.center b ⊆ F.source := by
    rintro ⟨q, t⟩ ⟨_, ht⟩
    exact hFs ▸ ⟨mem_univ _, hDc.1.trans_le ht.1, ht.2.trans_lt hbu⟩
  have hV : IsPreconnected V :=
    (isPreconnected_univ.prod isPreconnected_Ioo).image _
      (F.continuousOn.mono ((Set.prod_mono Subset.rfl Ioo_subset_Icc_self).trans hsub))
  have hfront : Disjoint V (frontier C) := by
    apply Set.disjoint_left.mpr
    rintro z ⟨⟨q, t⟩, ⟨_, ht⟩, rfl⟩ hz
    rw [frontier_core L hpair hcore] at hz
    simp only [mem_iUnion] at hz
    obtain ⟨E, hE, hzE⟩ := hz
    have hEt : E.center = t := (hEheight E hE _ hzE).symm.trans
      (hheight q t ⟨hDc.1.trans ht.1, ht.2.trans hbu⟩)
    have hEc : E.center ∈ Ioo l u := hEt ▸ ⟨hDc.1.trans ht.1, ht.2.trans hbu⟩
    have hzF := F.map_source (hsub ⟨mem_univ _, ht.1.le, ht.2.le⟩)
    have hEs : E.scale < 0 := scale_neg_of_lower_annulus L hpair hcore hC hh hgerm F
      hla hFs hheight hlower E hE hEc hzE hzF (by
        obtain ⟨y, hy, hyh⟩ := hgreater
        exact ⟨y, hy, hEt ▸ ht.2.trans hyh⟩)
    have hbelow := E.lower_annular_strip_subset_open_disk_of_scale_neg hEs hh F hFs
      hheight hEc (hEheight E hE) hzE hzF (hgerm _ (hboundary E hE hzE))
    have hpcoord := hheight (F.symm p).1 (F.symm p).2 (hFs ▸ F.map_target hpF).2
    rw [F.right_inv hpF, hEheight D hD p hp] at hpcoord
    have hpE := hbelow (show p ∈ F '' (univ ×ˢ Ioo l E.center) from
      ⟨F.symm p, ⟨mem_univ _, hpcoord ▸ hDc.1,
        hpcoord ▸ (hEt ▸ ht.1)⟩, F.right_inv hpF⟩)
    exact (hcore ▸ hboundary D hD hp)
      (mem_iUnion_of_mem E (mem_iUnion_of_mem hE hpE))
  obtain ⟨z, hzV, hzC⟩ := upper_open_strip_meets_core L hpair hcore F hFs hheight
    D hD hs hDc.1 hDb hbu hp hpF (hEheight D hD p hp) (hgerm p (hboundary D hD hp))
  have hVint : V ⊆ interior C :=
    Poincare.Topology.subset_of_isPreconnected_of_disjoint_frontier isOpen_interior hV
      (hfront.mono_right frontier_interior_subset)
      ⟨z, hzV, (mem_interior_iff_notMem_frontier hzC).mpr
        (fun hzf => Set.disjoint_left.mp hfront hzV hzf)⟩
  exact ⟨hs, (closure_image_open_strip F hDb hsub).trans
    (closure_minimal (hVint.trans interior_subset) hclosed), hVint⟩

end Poincare.Manifold.Schoenflies.SphereSurgeryCoreCap
