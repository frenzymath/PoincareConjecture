import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Cor6_67_SliceInverse

set_option autoImplicit false

open Set

universe u v

namespace PoincareConjecture.Proofs.M46

theorem finite_inverse_fiber_capture
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [T2Space Y] {f : X → Y} {B : Set X}
    (hB : IsCompact B) (hf : ContinuousOn f B) (q : Y)
    (e : {z : X // z ∈ B ∧ f z = q} → OpenPartialHomeomorph X Y)
    (hsource : ∀ z, z.val ∈ (e z).source)
    (hvalue : ∀ z, EqOn (e z) f (e z).source) :
    ∃ J : Finset {z : X // z ∈ B ∧ f z = q},
      ∃ V : Set Y, IsOpen V ∧ q ∈ V ∧
        (∀ i ∈ J, V ⊆ (e i).target) ∧
        ∀ z ∈ B, f z ∈ V → ∃ i ∈ J, z ∈ (e i).source := by
  classical
  let : T1Space Y := T2Space.t1Space
  let K : Set X := {z | z ∈ B ∧ f z = q}
  have hKclosed : IsClosed K := by
    change IsClosed (B ∩ f ⁻¹' {q})
    exact hf.preimage_isClosed_of_isClosed hB.isClosed isClosed_singleton
  have hK : IsCompact K := hB.of_isClosed_subset hKclosed (fun _ hz => hz.1)
  obtain ⟨J, hcover⟩ := hK.elim_finite_subcover (fun i : K => (e i).source)
    (fun i => (e i).open_source) (by
      intro z hz
      exact mem_iUnion.mpr ⟨⟨z, hz⟩, hsource ⟨z, hz⟩⟩)
  let U := ⋃ i ∈ J, (e i).source
  have hU : IsOpen U := isOpen_iUnion (fun i => isOpen_iUnion (fun _ => (e i).open_source))
  have hbad : IsClosed (f '' (B \ U)) :=
    ((hB.diff hU).image_of_continuousOn (hf.mono sdiff_subset)).isClosed
  let V := (f '' (B \ U))ᶜ ∩ ⋂ i ∈ J, (e i).target
  have hV : IsOpen V := hbad.isOpen_compl.inter
    (isOpen_biInter_finset (fun i _ => (e i).open_target))
  have hqV : q ∈ V := by
    constructor
    · rintro ⟨z, hz, heq⟩
      exact hz.2 (hcover ⟨hz.1, heq⟩)
    · apply mem_iInter.mpr
      intro i
      apply mem_iInter.mpr
      intro _
      have htarget := (e i).map_source (hsource i)
      rwa [hvalue i (hsource i), i.property.2] at htarget
  refine ⟨J, V, hV, hqV, ?_, ?_⟩
  · intro i hi z hz
    exact mem_iInter.mp (mem_iInter.mp hz.2 i) hi
  · intro z hz htarget
    have hzU : z ∈ U := by
      by_contra hnot
      exact htarget.1 ⟨z, ⟨hz, hnot⟩, rfl⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp hzU
    obtain ⟨hiJ, hiSource⟩ := mem_iUnion.mp hi
    exact ⟨i, hiJ, hiSource⟩

end PoincareConjecture.Proofs.M46
