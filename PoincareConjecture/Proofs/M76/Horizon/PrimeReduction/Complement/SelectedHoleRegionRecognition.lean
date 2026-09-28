import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProtectedRegionRecognition
import PoincareConjecture.Proofs.Horizon.Topology.Maps.OpenPartialHomeomorph.Compact

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem closed_subset_alexander_bounded_side {S C U K : Set E}
    (hUf : frontier U = S)
    (hUE : IsFinitePLBallPair ((ℝ × ℝ) × ℝ)
      (frontier (C ×ˢ Icc (-1 : ℝ) 1) \ U ×ˢ {1}) (S ×ˢ {1}))
    (hK : IsClosed K) (hKf : frontier K ⊆ S) (hKC : K ⊆ interior C) :
    K ⊆ closure U := by
  intro x hx
  by_contra hxU
  have hxS : x ∉ S := fun h => hxU (frontier_subset_closure (hUf.symm ▸ h))
  have hxi : x ∈ interior K := by
    by_contra hn
    exact hxS (hKf ⟨hK.closure_eq.symm ▸ hx, hn⟩)
  let Z := frontier (C ×ˢ Icc (-1 : ℝ) 1)
  let Q : Set Z := (Subtype.val : Z → E × ℝ) ⁻¹'
    ((Z \ U ×ˢ {1}) \ S ×ˢ {1})
  let W : Set Z := (Subtype.val : Z → E × ℝ) ⁻¹' (interior K ×ˢ {1})
  have hQ : IsPreconnected Q := by
    apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
    have hsubset : ((Z \ U ×ˢ {(1 : ℝ)}) \ S ×ˢ {1}) ⊆ Z :=
      sdiff_subset.trans sdiff_subset
    rw [image_preimage_eq_of_subset (by simpa using hsubset)]
    exact hUE.isConnected_sdiff.isPreconnected
  have hW : IsOpen W :=
    isOpen_preimage_top_face isOpen_interior (interior_subset.trans hKC)
  have hWf : frontier W ⊆ (Subtype.val : Z → E × ℝ) ⁻¹' (S ×ˢ {1}) := by
    rw [frontier_preimage_top_face isOpen_interior (interior_subset.trans hKC)]
    exact preimage_mono (prod_mono (frontier_interior_subset.trans hKf) subset_rfl)
  have hdis : Disjoint (frontier W) Q :=
    disjoint_left.mpr fun _ hz hq => hq.2 (hWf hz)
  have hxC : x ∈ C := interior_subset (hKC hx)
  have hxtop : (x, (1 : ℝ)) ∈ Z :=
    prod_singleton_one_subset_frontier_cylinder (Subset.rfl : C ⊆ C) ⟨hxC, rfl⟩
  have hQW : (Q ∩ W).Nonempty := by
    refine ⟨⟨(x, 1), hxtop⟩, ⟨⟨hxtop, ?_⟩, ?_⟩, hxi, rfl⟩
    · exact fun h => hxU (subset_closure h.1)
    · exact fun h => hxS h.1
  have hQsub : Q ⊆ W := hQ.m76_subset_of_disjoint_frontier hW hdis hQW
  have hxbottom : (x, (-1 : ℝ)) ∈ Z := by
    dsimp [Z]
    rw [frontier_prod_eq, frontier_Icc (by norm_num : (-1 : ℝ) ≤ 1)]
    exact Or.inl ⟨subset_closure hxC, by simp⟩
  have hbottomQ : (⟨(x, -1), hxbottom⟩ : Z) ∈ Q := by
    refine ⟨⟨hxbottom, ?_⟩, ?_⟩ <;> intro h <;> norm_num at h
  have hbad := (hQsub hbottomQ).2
  norm_num at hbad

end PoincareConjecture.M76

namespace OpenPartialHomeomorph

open PoincareConjecture.M76

theorem image_complement_eq_alexander_bounded_side
    {X E : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : OpenPartialHomeomorph X E) {A R : Set X} {C U : Set E}
    (hAc : IsConnected A) (hAf : frontier A ⊆ R) (hRA : R ⊆ Aᶜ)
    (hcompact : IsCompact Aᶜ) (hsource : Aᶜ ⊆ e.source)
    (htarget : e.target = interior C) (p : X) (hp : p ∈ A) (hps : p ∉ e.source)
    (hU : IsOpen U) (hUf : frontier U = e '' R)
    (hUC : closure U ⊆ e.target) (hUc : IsCompact (closure U))
    (hUE : IsFinitePLBallPair ((ℝ × ℝ) × ℝ)
      (frontier (C ×ˢ Icc (-1 : ℝ) 1) \ U ×ˢ {1}) ((e '' R) ×ˢ {1})) :
    e '' Aᶜ = closure U := by
  have hK : IsCompact (e '' Aᶜ) :=
    hcompact.image_of_continuousOn (e.continuousOn.mono hsource)
  have hKt : e '' Aᶜ ⊆ e.target := image_subset_iff.mpr fun _ hx =>
    e.map_source (hsource hx)
  have hKf : frontier (e '' Aᶜ) ⊆ e '' R := by
    have hh := e.image_frontier_eq_target_inter_of_closure_subset
      (D := Aᶜ) (by rwa [hcompact.isClosed.closure_eq])
    rw [inter_eq_right.mpr (hK.isClosed.frontier_subset.trans hKt)] at hh
    rw [← hh, frontier_compl]
    exact image_mono hAf
  have hKU : e '' Aᶜ ⊆ closure U := closed_subset_alexander_bounded_side
    hUf hUE hK.isClosed hKf (hKt.trans htarget.subset)
  obtain ⟨hW, _, _, hWf⟩ := e.symm.image_region_of_isCompact_closure hU hUc hUC
  have hRW : frontier (e.symm '' U) = R := by
    rw [hWf, hUf]
    exact e.toPartialEquiv.symm_image_image_of_subset_source (hRA.trans hsource)
  have hWsub : e.symm '' U ⊆ Aᶜ := by
    intro x hx hxA
    have hAsub : A ⊆ e.symm '' U := hAc.isPreconnected.m76_subset_of_disjoint_frontier
      hW (by
        rw [hRW]
        exact disjoint_left.mpr fun _ hr ha => hRA hr ha)
      ⟨x, hxA, hx⟩
    obtain ⟨y, hy, hyp⟩ := hAsub hp
    exact hps (hyp ▸ e.map_target (hUC (subset_closure hy)))
  have hUK : U ⊆ e '' Aᶜ := by
    intro y hy
    exact ⟨e.symm y, hWsub ⟨y, hy, rfl⟩, e.right_inv (hUC (subset_closure hy))⟩
  exact Subset.antisymm hKU (closure_minimal hUK hK.isClosed)

end OpenPartialHomeomorph
