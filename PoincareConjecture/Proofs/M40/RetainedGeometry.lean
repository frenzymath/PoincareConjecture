import PoincareConjecture.Definitions.M39ComparisonMap









set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M40

variable {g₀ : StandardInitialMetric} {D : RepairedSurgeryFlowData.{u} g₀}
  {T : ℝ} {hT : T ∈ D.flow.surgery_times}
  [Nonempty (D.flow.slice T).carrier]
  {I : RepairedComparisonMapInput D T hT}
  (Q : RepairedComparisonMapConclusion I)

local notation "E" => D.flow.event T hT



theorem retained_injOn : Set.InjOn Q.map I.retained := by
  intro x hx y hy hxy
  apply I.parent.inclusion_openEmbedding.injective
  apply (E).retention.left_inverse.injOn
    (interior_subset (I.retained_subset x hx))
    (interior_subset (I.retained_subset y hy))
  rw [← Q.retained_agreement x hx, ← Q.retained_agreement y hy, hxy]



theorem retained_image_not_mem_cap {x : I.parent.carrier.carrier}
    (hx : x ∈ I.retained) (i : Fin (E).cap_count) :
    I.child.inclusion (Q.map x) ∉ ((E).caps i).carrier := by
  intro hcap
  have hxpre := I.retained_subset x hx
  have hpost : I.child.inclusion (Q.map x) ∈ (E).retained_post := by
    rw [Q.retained_agreement x hx]
    exact (E).retention.map_image.subset ⟨_, interior_subset hxpre, rfl⟩
  have hfront : I.child.inclusion (Q.map x) ∈ frontier ((E).caps i).carrier := by
    rw [← (E).cap_boundary i]
    exact ⟨hpost, hcap⟩
  rw [← (E).boundary_correspondence i] at hfront
  obtain ⟨z, hz, hzeq⟩ := hfront
  have hzfront : z ∈ frontier (E).retained_pre := by
    rw [(E).pre_boundary]
    exact mem_iUnion.mpr ⟨i, hz⟩
  have hzpre : z ∈ (E).retained_pre :=
    (E).retained_pre_compact.isClosed.closure_subset hzfront.1
  have hzx : z = I.parent.inclusion x :=
    (E).retention.left_inverse.injOn hzpre (interior_subset hxpre)
      (hzeq.trans (Q.retained_agreement x hx))
  exact hzfront.2 (hzx.symm ▸ hxpre)



theorem retained_fiber_eq {x : I.parent.carrier.carrier} (hx : x ∈ I.retained)
    {y : I.parent.carrier.carrier} (hy : Q.map y = Q.map x) : y = x := by
  have hyret : y ∈ I.retained := by
    by_contra hnot
    obtain ⟨i, hi⟩ := Q.outside_image_in_caps y hnot
    rw [hy] at hi
    exact retained_image_not_mem_cap Q hx i hi
  exact retained_injOn Q hyret hx hy



theorem exists_unique_retained_fiber :
    ∃ x ∈ I.retained, ∀ y, Q.map y = Q.map x → y = x := by
  obtain ⟨x, hx⟩ := I.inherited
  exact ⟨x, hx, fun _ hy => retained_fiber_eq Q hx hy⟩



theorem retained_inverse_apply {x : I.parent.carrier.carrier}
    (hx : x ∈ I.retained) :
    I.parent.inverse ((E).retention.inverse (I.child.inclusion (Q.map x))) = x := by
  rw [Q.retained_agreement x hx,
    (E).retention.left_inverse (interior_subset (I.retained_subset x hx)),
    I.parent.left_inverse]



def retainedOpenPartialHomeomorph :
    OpenPartialHomeomorph I.parent.carrier.carrier I.child.carrier.carrier where
  toFun := Q.map
  invFun := I.parent.inverse ∘ (E).retention.inverse ∘ I.child.inclusion
  source := I.retained
  target := Q.map '' I.retained
  map_source' := fun x hx => mem_image_of_mem Q.map hx
  map_target' := by
    rintro _ ⟨x, hx, rfl⟩
    simpa only [Function.comp_apply, retained_inverse_apply Q hx] using hx
  left_inv' := fun _ hx => retained_inverse_apply Q hx
  right_inv' := by
    rintro _ ⟨x, hx, rfl⟩
    change Q.map (I.parent.inverse ((E).retention.inverse
      (I.child.inclusion (Q.map x)))) = Q.map x
    rw [retained_inverse_apply Q hx]
  open_source := I.retained_open
  open_target := I.child.inclusion_openEmbedding.isOpen_iff_image_isOpen.mpr
    Q.retained_target_open
  continuousOn_toFun := Q.map.continuous.continuousOn
  continuousOn_invFun := by
    apply I.parent.inverse_smooth.continuousOn.comp
      ((E).retention.inverse_smooth.continuousOn.comp
        I.child.inclusion_smooth.continuous.continuousOn ?_) ?_
    · rintro _ ⟨x, hx, rfl⟩
      rw [Q.retained_agreement x hx]
      exact (E).retention.map_image.subset
        ⟨_, interior_subset (I.retained_subset x hx), rfl⟩
    · rintro _ ⟨x, hx, rfl⟩
      change (E).retention.inverse (I.child.inclusion (Q.map x)) ∈ _
      rw [Q.retained_agreement x hx,
        (E).retention.left_inverse (interior_subset (I.retained_subset x hx))]
      exact mem_range_self x

end PoincareConjecture.M40
