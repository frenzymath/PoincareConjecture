import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.CollarMatching
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.BallEmbedding
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Separation.Euclidean

open _root_.AddCircle
open _root_.Poincare
open _root_.PoincareConjecture

namespace M38Schoenflies

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric PoincareConjecture
open scoped Manifold ContDiff Topology

namespace Poincare

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "CylModel" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

private theorem globalize_ball_coordinates
    (b : OpenPartialHomeomorph E3 E3) (hs : closedBall 0 1 ⊆ b.source)
    (hb : ContMDiffOn (𝓡 3) (𝓡 3) ∞ b b.source)
    (hbi : ContMDiffOn (𝓡 3) (𝓡 3) ∞ b.symm b.target) :
    ∃ F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      ∀ x ∈ closedBall (0 : E3) 1, F x = b x := by
  let D : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞ := {
    toPartialEquiv := b.toPartialEquiv
    open_source := b.open_source
    open_target := b.open_target
    contMDiffOn_toFun := hb
    contMDiffOn_invFun := hbi }
  obtain ⟨f, V, hf, hV, hball, hVs, hfb⟩ :=
    Analysis.exists_contDiff_extension_near_compact (isCompact_closedBall 0 1)
      b.open_source hs b (fun x hx =>
        (hb.contMDiffAt (b.open_source.mem_nhds hx)).contDiffAt.contDiffWithinAt)
  have hder (x : E3) (hx : x ∈ closedBall 0 1) :
      Function.Bijective (fderiv ℝ f x) := by
    have heq : f =ᶠ[𝓝 x] b := Filter.eventuallyEq_of_mem (hV.mem_nhds (hball hx)) hfb
    rw [heq.fderiv_eq]
    have hl : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ b x :=
      ⟨D, hs hx, fun _ _ => rfl⟩
    have H := (hl.mfderivToContinuousLinearEquiv (by simp)).bijective
    change Function.Bijective (mfderiv (𝓡 3) (𝓡 3) b x) at H
    simpa only [mfderiv_eq_fderiv, TangentSpace] using H
  have hinj : InjOn f (closedBall 0 1) := by
    intro x hx y hy hxy
    apply b.injOn (hs hx) (hs hy)
    simpa only [hfb (hball hx), hfb (hball hy)] using hxy
  obtain ⟨F, hF⟩ := Manifold.Schoenflies.exists_global_extension_of_ball_embedding
    zero_lt_one f hf hinj hder
  exact ⟨F, fun x hx => (hF x hx).trans (hfb (hball hx))⟩

private theorem ambient_map_of_compact_collar_side
    {K : Set E3} (hK : IsCompact K) (hregular : closure (interior K) = K)
    (c : OpenPartialHomeomorph RoundCylinderSpace E3)
    (hc : ContMDiffOn CylModel (𝓡 3) ∞ c c.source)
    (hci : ContMDiffOn (𝓡 3) CylModel ∞ c.symm c.target)
    {δ : ℝ} (hδ : 0 < δ) (hsource : univ ×ˢ Ioo (-δ) δ ⊆ c.source)
    (hfront : frontier K = range (fun q : UnitTwoSphere => c (q, 0)))
    (hside : ∀ y ∈ c.target, y ∈ K ↔ (c.symm y).2 ≤ 0) :
    ∃ F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      ∀ q : UnitTwoSphere, F q = c (q, 0) := by
  obtain ⟨r, b, hr, _, hbs, _, hb, hbi, _, hmatch⟩ :=
    Manifold.Schoenflies.ball_neighborhood_matching_collar_in_coordinates
      (OpenPartialHomeomorph.refl E3) rfl contMDiffOn_id contMDiffOn_id
      hK (subset_univ _) hregular c hc hci hδ hsource (subset_univ _) hfront hside
  obtain ⟨F, hF⟩ := globalize_ball_coordinates b hbs hb hbi
  refine ⟨F, fun q => ?_⟩
  rw [hF q (sphere_subset_closedBall q.property)]
  simpa using (hmatch (q, 0) (by simpa using hr)).2

theorem exists_ambient_map_of_euclidean_sphere_collar
    (c : OpenPartialHomeomorph RoundCylinderSpace E3)
    (hc : ContMDiffOn CylModel (𝓡 3) ∞ c c.source)
    (hci : ContMDiffOn (𝓡 3) CylModel ∞ c.symm c.target)
    {δ : ℝ} (hδ : 0 < δ) (hsource : c.source = univ ×ˢ Ioo (-δ) δ) :
    ∃ F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      ∀ q : UnitTwoSphere, F q = c (q, 0) := by
  let e : (UnitTwoSphere × Ioo (-δ) δ) ≃ₜ c.target := {
    toFun := fun p => ⟨c (p.1, p.2), c.map_source (hsource.symm ▸ ⟨mem_univ _, p.2.property⟩)⟩
    invFun := fun y => ((c.symm y).1, ⟨(c.symm y).2, (hsource ▸ c.map_target y.property).2⟩)
    left_inv := by
      intro p
      have hp : (p.1, (p.2 : ℝ)) ∈ c.source := hsource.ge ⟨mem_univ _, p.2.property⟩
      apply Prod.ext
      · change (c.symm (c (p.1, p.2))).1 = p.1
        exact congrArg Prod.fst (c.left_inv hp)
      · apply Subtype.ext
        change (c.symm (c (p.1, p.2))).2 = p.2
        exact congrArg Prod.snd (c.left_inv hp)
    right_inv := fun y => Subtype.ext (c.right_inv y.property)
    continuous_toFun := by
      apply Continuous.subtype_mk
      apply c.continuousOn.comp_continuous (continuous_fst.prodMk
        (continuous_subtype_val.comp continuous_snd))
      intro p
      exact hsource.symm ▸ ⟨mem_univ _, p.2.property⟩
    continuous_invFun := by
      have h := c.continuousOn_symm.comp_continuous continuous_subtype_val
        (fun y : c.target => y.property)
      exact h.fst.prodMk (h.snd.subtype_mk _) }
  let S := range (fun q : UnitTwoSphere => c (q, 0))
  let : ConnectedSpace UnitTwoSphere := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (E := E3) (by rw [← Module.finrank_eq_rank]; norm_num) 0 zero_le_one)
  obtain ⟨A, B, hA, hB, _, _, hdis, hcover, hAf, hBf, hneg, hpos⟩ :=
    Topology.exists_collar_complementary_regions hδ c.open_target e
  change A ∪ B = Sᶜ at hcover
  change frontier A = S at hAf
  change frontier B = S at hBf
  have hAB : closure A = Bᶜ := by
    rw [closure_eq_self_union_frontier, hAf]
    have := Set.disjoint_left.mp hdis
    ext x
    have := Set.ext_iff.mp hcover x
    simp only [mem_union, mem_compl_iff] at *
    tauto
  have hBA : closure B = Aᶜ := by
    rw [closure_eq_self_union_frontier, hBf]
    have := Set.disjoint_left.mp hdis
    ext x
    have := Set.ext_iff.mp hcover x
    simp only [mem_union, mem_compl_iff] at *
    tauto
  have hnegative (y : E3) (hy : y ∈ c.target) : y ∈ A ↔ (c.symm y).2 < 0 := by
    let hp := e.symm ⟨y, hy⟩
    have heq : (e hp : E3) = y := congrArg Subtype.val (e.apply_symm_apply ⟨y, hy⟩)
    constructor
    · intro hyA
      by_contra hn
      have ht : 0 ≤ (c.symm y).2 := le_of_not_gt hn
      rcases ht.eq_or_lt with hz | hz
      · have hyS : y ∈ S := ⟨(c.symm y).1, by
          change c ((c.symm y).1, 0) = y
          rw [show ((c.symm y).1, (0 : ℝ)) = c.symm y from Prod.ext rfl hz]
          exact c.right_inv hy⟩
        exact (hcover.subset (mem_union_left B hyA)) hyS
      · exact Set.disjoint_left.mp hdis hyA
          (heq ▸ hpos ⟨hp, hz, rfl⟩)
    · intro hz
      exact heq ▸ hneg ⟨hp, hz, rfl⟩
  have hpositive (y : E3) (hy : y ∈ c.target) : y ∈ B ↔ 0 < (c.symm y).2 := by
    constructor
    · intro hyB
      by_contra hn
      have ht : (c.symm y).2 ≤ 0 := le_of_not_gt hn
      rcases ht.lt_or_eq with hz | hz
      · exact Set.disjoint_left.mp hdis ((hnegative y hy).mpr hz) hyB
      · have hyS : y ∈ S := ⟨(c.symm y).1, by
          change c ((c.symm y).1, 0) = y
          rw [show ((c.symm y).1, (0 : ℝ)) = c.symm y from Prod.ext rfl hz.symm]
          exact c.right_inv hy⟩
        exact (hcover.subset (mem_union_right A hyB)) hyS
    · intro hz
      have heq : (e (e.symm ⟨y, hy⟩) : E3) = y :=
        congrArg Subtype.val (e.apply_symm_apply ⟨y, hy⟩)
      exact heq ▸ hpos ⟨e.symm ⟨y, hy⟩, hz, rfl⟩
  have hS : IsCompact S := isCompact_range
    (c.continuousOn.comp_continuous (continuous_id.prodMk continuous_const)
      (fun q => hsource.ge ⟨mem_univ q, neg_lt_zero.mpr hδ, hδ⟩))
  rcases Topology.bounded_side_of_compact_complement_partition_euclidean_three
      hS hA hB hdis hcover with ⟨hAb, _⟩ | ⟨hBb, _⟩
  · apply ambient_map_of_compact_collar_side
      (K := closure A) (isCompact_iff_isClosed_bounded.mpr ⟨isClosed_closure, hAb.closure⟩)
      (by rw [hAB, interior_compl, hBA, compl_compl, hAB]) c hc hci hδ hsource.ge
      (by rw [hAB, frontier_compl, hBf])
    intro y hy
    rw [hAB, mem_compl_iff, hpositive y hy, not_lt]
  · let R : Diffeomorph CylModel CylModel RoundCylinderSpace RoundCylinderSpace ∞ := {
      toEquiv := (Equiv.refl UnitTwoSphere).prodCongr (Equiv.neg ℝ)
      contMDiff_toFun := contMDiff_fst.prodMk contMDiff_snd.neg
      contMDiff_invFun := contMDiff_fst.prodMk contMDiff_snd.neg }
    let d := R.toHomeomorph.toOpenPartialHomeomorph.trans c
    have hd0 (q : UnitTwoSphere) : d (q, 0) = c (q, 0) := by
      change c (q, -(0 : ℝ)) = c (q, 0)
      rw [neg_zero]
    have hds : univ ×ˢ Ioo (-δ) δ ⊆ d.source := by
      intro z hz
      refine ⟨mem_univ _, hsource.symm ▸ ⟨mem_univ _, ?_⟩⟩
      change -δ < -z.2 ∧ -z.2 < δ
      constructor <;> linarith [hz.2.1, hz.2.2]
    obtain ⟨F, hF⟩ := ambient_map_of_compact_collar_side
      (K := closure B) (isCompact_iff_isClosed_bounded.mpr ⟨isClosed_closure, hBb.closure⟩)
      (by rw [hBA, interior_compl, hAB, compl_compl, hBA]) d
      (hc.comp R.contMDiff.contMDiffOn inter_subset_right)
      (R.symm.contMDiff.comp_contMDiffOn (hci.mono inter_subset_left)) hδ hds
      (by rw [hBA, frontier_compl, hAf]; simp only [hd0]; rfl)
      (fun y hy => by
        change y ∈ closure B ↔ -(c.symm y).2 ≤ 0
        rw [hBA, mem_compl_iff, hnegative y hy.1, not_lt, neg_nonpos])
    exact ⟨F, fun q => (hF q).trans (hd0 q)⟩

end Poincare

end

end M38Schoenflies
