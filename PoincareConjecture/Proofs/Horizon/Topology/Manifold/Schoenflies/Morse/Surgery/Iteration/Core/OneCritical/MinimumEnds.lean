import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.AnnularRegion



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.SphereSurgeryCoreCap

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1
local notation "Iprod" => ModelWithCorners.prod (𝓡 1) 𝓘(Real, Real)




theorem exists_unique_cap_of_minimum_component
    {v : E3} {g : S2 -> E3} {B : Set Real}
    (L : List (SphereSurgeryCoreCap v g B)) (hL : L ≠ [])
    (hpair : L.Pairwise (fun D E => Disjoint
      (D.chart '' closedBall 0 1) (E.chart '' closedBall 0 1)))
    {C : Set S2} (hcore : C = (⋃ D ∈ L, D.chart '' ball 0 1)ᶜ)
    (hC : IsPreconnected C) (hcompact : IsCompact C)
    {h : S2 -> Real} (hh : ContinuousOn h C)
    (hactual : EqOn h (fun p => inner Real v (g p)) C)
    (e : OpenPartialHomeomorph E2 S2) {r c a b δ : Real}
    (hr : 0 < r) (hrs : closedBall (0 : E2) r ⊆ e.source)
    (hform : ∀ x ∈ e.source, h (e x) = c + ‖x‖ ^ 2)
    (ha : a = c + r ^ 2) (hab : a < b) (hδ : 0 < δ)
    (hdisk : e '' closedBall (0 : E2) r ⊆ interior C)
    (F : OpenPartialHomeomorph (S1 × Real) S2)
    (hFs : F.source = univ ×ˢ Ioo (a - δ) (b + δ))
    (hF : ContMDiffOn Iprod (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) Iprod ∞ F.symm F.target)
    (hheight : ∀ q t, t ∈ Ioo (a - δ) (b + δ) -> h (F (q, t)) = t)
    (hbottom : range (fun q : S1 => F (q, a)) = e '' sphere (0 : E2) r)
    (hcover : C ⊆ e '' closedBall (0 : E2) r ∪ F '' (univ ×ˢ Icc a b)) :
    ∃ D ∈ L, ∀ A ∈ L, A = D := by
  classical
  let : ConnectedSpace S1 := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (E := E2) (by rw [← Module.finrank_eq_rank]; norm_num)
      0 zero_le_one)
  let K := e '' closedBall (0 : E2) r
  have hKC : K ⊆ C := hdisk.trans interior_subset
  have hKh : ∀ p ∈ K, h p ≤ a := by
    rintro p ⟨x, hx, rfl⟩
    rw [hform x (hrs hx), ha]
    exact add_le_add le_rfl ((sq_le_sq₀ (norm_nonneg _) hr.le).mpr
      (mem_closedBall_zero_iff.mp hx))
  have hband : Icc a b ⊆ Ioo (a - δ) (b + δ) := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hboundary (A : SphereSurgeryCoreCap v g B) (hA : A ∈ L) :
      A.chart '' sphere (0 : E2) 1 ⊆ C := fun p hp =>
    ((core_inter_closed_disk L hpair hcore A hA).superset hp).1
  have hfront (A : SphereSurgeryCoreCap v g B) (hA : A ∈ L) :
      A.chart '' sphere (0 : E2) 1 ⊆ frontier C := by
    rw [frontier_core L hpair hcore]
    exact fun p hp => mem_iUnion_of_mem A (mem_iUnion_of_mem hA hp)
  have hAheight (A : SphereSurgeryCoreCap v g B) (hA : A ∈ L) :
      ∀ p ∈ A.chart '' sphere (0 : E2) 1, h p = A.center := by
    intro p hp
    exact (hactual (hboundary A hA hp)).trans (A.height_eq_on_boundary p hp)
  have hAband (A : SphereSurgeryCoreCap v g B) (hA : A ∈ L) :
      A.chart '' sphere (0 : E2) 1 ⊆ F '' (univ ×ˢ Icc a b) := by
    intro p hp
    exact (hcover (hboundary A hA hp)).resolve_left
      (fun hpK => (hfront A hA hp).2 (hdisk hpK))
  have hAtarget (A : SphereSurgeryCoreCap v g B) (hA : A ∈ L) :
      A.chart '' sphere (0 : E2) 1 ⊆ F.target := by
    intro p hp
    obtain ⟨⟨q, t⟩, ⟨_, ht⟩, rfl⟩ := hAband A hA hp
    exact F.map_source (hFs ▸ ⟨mem_univ _, hband ht⟩)
  obtain ⟨x, hx⟩ := (NormedSpace.sphere_nonempty (E := E2)).mpr zero_le_one
  have hlevels (A : SphereSurgeryCoreCap v g B) (hA : A ∈ L) :
      A.center ∈ Ioc a b := by
    have hp : A.chart x ∈ A.chart '' sphere (0 : E2) 1 := mem_image_of_mem _ hx
    obtain ⟨⟨q, t⟩, ⟨_, ht⟩, hqp⟩ := hAband A hA hp
    have hct : A.center = t := (hAheight A hA _ hp).symm.trans
      ((congrArg h hqp).symm.trans (hheight q t (hband ht)))
    refine ⟨?_, hct ▸ ht.2⟩
    apply lt_of_le_of_ne (hct ▸ ht.1)
    intro hac
    have hta : t = a := hct.symm.trans hac.symm
    have hpK : A.chart x ∈ K := by
      apply image_mono sphere_subset_closedBall
      rw [← hbottom]
      exact ⟨q, hta ▸ hqp⟩
    exact (hfront A hA hp).2 (hdisk hpK)
  have hcircles (A : SphereSurgeryCoreCap v g B) (hA : A ∈ L) :
      A.chart '' sphere (0 : E2) 1 = range (fun q : S1 => F (q, A.center)) :=
    A.boundary_eq_annular_slice F hFs hF hFi hheight
      (hband ⟨(hlevels A hA).1.le, (hlevels A hA).2⟩)
      (hAtarget A hA) (hAheight A hA)
  obtain ⟨D, hD⟩ := List.exists_mem_of_ne_nil L hL
  obtain ⟨p, hp, hmax⟩ := hcompact.exists_isMaxOn
    ⟨D.chart x, hboundary D hD (mem_image_of_mem _ hx)⟩ hh
  let m := h p
  have hmD : D.center ≤ m := by
    rw [← hAheight D hD (D.chart x) (mem_image_of_mem _ hx)]
    exact hmax (hboundary D hD (mem_image_of_mem _ hx))
  have ham : a < m := (hlevels D hD).1.trans_le hmD
  have hmb : m ≤ b := by
    rcases hcover hp with hpK | ⟨⟨q, t⟩, ⟨_, ht⟩, hqp⟩
    · exact (hKh p hpK).trans hab.le
    · change h p ≤ b
      rw [← hqp, hheight q t (hband ht)]
      exact ht.2
  have hsmall : Icc a m ⊆ Icc a b := fun _ ht => ⟨ht.1, ht.2.trans hmb⟩
  have hcover' : C ⊆ K ∪ F '' (univ ×ˢ Icc a m) := by
    intro z hz
    rcases hcover hz with hzK | ⟨⟨q, t⟩, ⟨_, ht⟩, hqz⟩
    · exact Or.inl hzK
    · right
      have htm : t ≤ m := by
        rw [← hheight q t (hband ht), hqz]
        exact hmax hz
      exact ⟨(q, t), ⟨mem_univ _, ⟨ht.1, htm⟩⟩, hqz⟩
  have haC : a ∈ h '' C := by
    obtain ⟨y, hy⟩ := (NormedSpace.sphere_nonempty (E := E2)).mpr hr.le
    refine ⟨e y, hKC (mem_image_of_mem _ (sphere_subset_closedBall hy)), ?_⟩
    rw [hform y (hrs (sphere_subset_closedBall hy)), mem_sphere_zero_iff_norm.mp hy, ha]
  have hCeq : C = K ∪ F '' (univ ×ˢ Icc a m) := by
    apply Poincare.Topology.eq_union_image_closed_band_of_frontier_saturated F
      (fun t ht => hF.continuousOn.comp_continuous (continuous_id.prodMk continuous_const)
        (fun q => hFs ▸ ⟨mem_univ q, hband (hsmall ht)⟩)) hC hh
      (fun q t ht => hheight q t (hband (hsmall ht))) hKC hKh
      (hbottom ▸ image_mono sphere_subset_closedBall) hcover' haC ⟨p, hp, rfl⟩
    intro t ht q hq
    rw [frontier_core L hpair hcore] at hq
    simp only [mem_iUnion] at hq
    obtain ⟨A, hA, hqA⟩ := hq
    have hct : A.center = t := (hAheight A hA _ hqA).symm.trans
      (hheight q t (hband (hsmall ht)))
    rw [← hct, ← hcircles A hA]
    exact hboundary A hA
  have hopen : F '' (univ ×ˢ Ioo a m) ⊆ interior C := by
    apply interior_maximal ?_
      (F.isOpen_image_of_subset_source (isOpen_univ.prod isOpen_Ioo) ?_)
    · rw [hCeq]
      exact (image_mono (prod_mono Subset.rfl Ioo_subset_Icc_self)).trans subset_union_right
    · rintro ⟨q, t⟩ ⟨_, ht⟩
      rw [hFs]
      exact ⟨mem_univ _, hband (hsmall ⟨ht.1.le, ht.2.le⟩)⟩
  have htop (A : SphereSurgeryCoreCap v g B) (hA : A ∈ L) : A.center = m := by
    have hpA : A.chart x ∈ A.chart '' sphere (0 : E2) 1 := mem_image_of_mem _ hx
    have hcm : A.center ≤ m := by
      rw [← hAheight A hA _ hpA]
      exact hmax (hboundary A hA hpA)
    apply le_antisymm hcm
    by_contra hnot
    have hcm' : A.center < m := lt_of_not_ge hnot
    obtain ⟨q, hqp⟩ := hcircles A hA ▸ hpA
    exact (hfront A hA hpA).2 (hopen
      ⟨(q, A.center), ⟨mem_univ _, (hlevels A hA).1, hcm'⟩, hqp⟩)
  refine ⟨D, hD, ?_⟩
  intro A hA
  by_contra hne
  have heq : A.chart '' sphere (0 : E2) 1 = D.chart '' sphere (0 : E2) 1 := by
    rw [hcircles A hA, hcircles D hD, htop A hA, htop D hD]
  have hpA : A.chart x ∈ A.chart '' sphere (0 : E2) 1 := mem_image_of_mem _ hx
  exact Set.disjoint_left.mp (hpair.forall hA hD hne)
    (image_mono sphere_subset_closedBall hpA)
    (image_mono sphere_subset_closedBall (heq ▸ hpA))

end Poincare.Manifold.Schoenflies.SphereSurgeryCoreCap
