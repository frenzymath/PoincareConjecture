import PoincareConjecture.Proofs.M38.ProjectiveCutDomain
import PoincareConjecture.Proofs.M38.ProjectiveReverse

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M38

local notation "CylModel" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

theorem exists_projectiveDouble_first_cut_collar
    (A : GeneralizedSliceCarrier.{u}) (C : SmoothProjectiveDoubleModel A.carrier)
    {O : Set projectiveCarrier.{u}.carrier} (hO : IsOpen O)
    (hp : ULift.up C.first_puncture ∈ O) :
    let E := puncturedProjectiveRegionEquivalence A C.first_model
    ∃ (H : Diffeomorph (𝓡 3) (𝓡 3) A.carrier A.carrier ∞)
      (K : Set projectiveCarrier.{u}.carrier) (δ : ℝ)
      (c : OpenPartialHomeomorph RoundCylinderSpace projectiveCarrier.{u}.carrier),
      IsCompact K ∧ K ⊆ O ∧ closure (interior K) = K ∧
      Kᶜ = E.inverse '' (H '' C.first_region) ∧
      H '' closure C.first_region ⊆ C.first_region ∧
      0 < δ ∧ c.source = univ ×ˢ Ioo (-δ) δ ∧ c.target ⊆ O ∧
      ContMDiffOn CylModel (𝓡 3) ∞ c c.source ∧
      ContMDiffOn (𝓡 3) CylModel ∞ c.symm c.target ∧
      frontier K = range (fun z : UnitTwoSphere => c (z, 0)) ∧
      (∀ y ∈ c.target, y ∈ K ↔ (c.symm y).2 ≤ 0) ∧
      ∀ z : RoundCylinderSpace, c z = E.inverse (H (C.collar (z.1, -z.2))) := by
  classical
  let E := puncturedProjectiveRegionEquivalence A C.first_model
  let f := regionPartialDiffeomorph E isClosed_singleton.isOpen_compl C.first_open
  obtain ⟨_, H, K, _, _, _, hHU, hK, hKO, hKreg, _, hKcompl, hKfront⟩ :=
    exists_projectiveDouble_first_cut_domain A C hO hp
  let q := ((projectiveCollarReflection.toPartialDiffeomorph.trans
    (projectiveDoubleCollarChart C)).trans H.toPartialDiffeomorph).trans f.symm
  let b := q.toOpenPartialHomeomorph
  have hformula (z : RoundCylinderSpace) :
      b z = E.inverse (H (C.collar (z.1, -z.2))) := rfl
  have hzero (z : UnitTwoSphere) : (z, (0 : ℝ)) ∈ b.source := by
    refine ⟨⟨⟨mem_univ _, ?_⟩, mem_univ _⟩, ?_⟩
    · change (z, -(0 : ℝ)) ∈ univ ×ˢ Ioo (-1 : ℝ) 1
      norm_num
    · change H (C.collar (z, -(0 : ℝ))) ∈ C.first_region
      rw [neg_zero]
      exact hHU ⟨C.collar (z, 0),
        (projectiveDouble_sphere_subset_closures C
          ((projectiveDouble_collar_sphere_iff C z (by norm_num)).mpr rfl)).1, rfl⟩
  have hfront : frontier K = range (fun z : UnitTwoSphere => b (z, 0)) := by
    rw [hKfront]
    apply Subset.antisymm
    · rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      obtain ⟨z, rfl⟩ := (projectiveDouble_central_range C).symm.subset hx
      refine ⟨z, ?_⟩
      change E.inverse (H (C.collar (z, -(0 : ℝ)))) = E.inverse (H (C.collar (z, 0)))
      rw [neg_zero]
    · rintro _ ⟨z, rfl⟩
      change E.inverse (H (C.collar (z, -(0 : ℝ)))) ∈ E.inverse '' (H '' C.sphere)
      rw [neg_zero]
      exact ⟨H (C.collar (z, 0)), ⟨C.collar (z, 0),
        ((projectiveDouble_collar_sphere_iff C z (by norm_num)).mpr rfl), rfl⟩, rfl⟩
  let W := b.source ∩ b ⁻¹' O
  have hW : IsOpen W := b.isOpen_inter_preimage hO
  have hzeroW : (univ : Set UnitTwoSphere) ×ˢ ({0} : Set ℝ) ⊆ W := by
    rintro ⟨z, s⟩ ⟨_, hs⟩
    have hs0 : s = 0 := hs
    subst s
    refine ⟨hzero z, hKO (hK.isClosed.frontier_subset ?_)⟩
    rw [hfront]
    exact mem_range_self z
  obtain ⟨U, V, _, hV, hU, hV0, hUV⟩ := generalized_tube_lemma
    (isCompact_univ : IsCompact (univ : Set UnitTwoSphere)) isCompact_singleton hW hzeroW
  obtain ⟨r, hr, hrv⟩ := Metric.isOpen_iff.mp hV 0 (hV0 (by simp))
  have hstrip : univ ×ˢ Ioo (-r) r ⊆ W := by
    intro z hz
    exact hUV ⟨hU (mem_univ _), hrv (by
      simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using abs_lt.mpr hz.2)⟩
  let c := b.restrOpen (univ ×ˢ Ioo (-r) r) (isOpen_univ.prod isOpen_Ioo)
  have hcs : c.source = univ ×ˢ Ioo (-r) r :=
    inter_eq_right.mpr (fun _ hz => (hstrip hz).1)
  have hct : c.target ⊆ O := by
    intro y hy
    have h := (hstrip hy.2).2
    change b (b.symm y) ∈ O at h
    rwa [b.right_inv hy.1] at h
  have hside {z : RoundCylinderSpace} (hz : z ∈ b.source) : b z ∈ K ↔ z.2 ≤ 0 := by
    have hzs : (z.1, -z.2) ∈ univ ×ˢ Ioo (-1 : ℝ) 1 := hz.1.1.2
    have htarget : H (C.collar (z.1, -z.2)) ∈ C.first_region := hz.2
    have hcomp : b z ∈ Kᶜ ↔ C.collar (z.1, -z.2) ∈ C.first_region := by
      rw [hKcompl, hformula]
      constructor
      · rintro ⟨_, ⟨x, hx, rfl⟩, heq⟩
        have hxU : H x ∈ C.first_region := hHU ⟨x, subset_closure hx, rfl⟩
        have h := f.symm.toOpenPartialHomeomorph.injOn hxU htarget heq
        exact H.injective h ▸ hx
      · intro hx
        exact ⟨H (C.collar (z.1, -z.2)),
          ⟨C.collar (z.1, -z.2), hx, rfl⟩, rfl⟩
    have hmem : b z ∈ K ↔ ¬ C.collar (z.1, -z.2) ∈ C.first_region := by
      simpa only [mem_compl_iff, not_not] using hcomp.not
    rw [hmem, projectiveDouble_collar_first_iff C z.1 hzs.2, not_lt, neg_nonneg]
  refine ⟨H, K, r, c, hK, hKO, hKreg, hKcompl, hHU, hr, hcs, hct,
    q.contMDiffOn_toFun.mono inter_subset_left,
    q.contMDiffOn_invFun.mono inter_subset_left, hfront, ?_, hformula⟩
  intro y hy
  have h := hside (c.map_target hy).1
  change b (c.symm y) ∈ K ↔ (c.symm y).2 ≤ 0 at h
  change c (c.symm y) ∈ K ↔ (c.symm y).2 ≤ 0 at h
  rwa [c.right_inv hy] at h

end PoincareConjecture.M38
