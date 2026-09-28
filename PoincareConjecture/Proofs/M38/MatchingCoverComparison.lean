import PoincareConjecture.Proofs.M38.CompactCoverSheet










set_option autoImplicit false

open Set Filter Topology
open scoped Manifold ContDiff

namespace PoincareConjecture.M38



theorem exists_partialDiffeomorph_of_matching_local_covers
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M] [Nonempty M]
    {Q Z : GeneralizedSliceCarrier}
    (q : M → Q.carrier) (f : M → Z.carrier)
    (hq : IsLocalDiffeomorph I (𝓡 3) ∞ q)
    (hf : IsLocalDiffeomorph I (𝓡 3) ∞ f)
    {C : Set M} (hC : IsOpen C)
    (hfibers : ∀ x ∈ C, ∀ y ∈ C, q x = q y ↔ f x = f y) :
    ∃ e : PartialDiffeomorph (𝓡 3) (𝓡 3) Q.carrier Z.carrier ∞,
      e.source = q '' C ∧ e.target = f '' C ∧
        ∀ x ∈ C, e (q x) = f x := by
  classical
  let x₀ : M := Classical.choice inferInstance
  let lq (y : Q.carrier) : M := if h : y ∈ q '' C then h.choose else x₀
  let lf (y : Z.carrier) : M := if h : y ∈ f '' C then h.choose else x₀
  have hlq (y : Q.carrier) (hy : y ∈ q '' C) : lq y ∈ C ∧ q (lq y) = y := by
    simpa only [lq, dif_pos hy] using hy.choose_spec
  have hlf (y : Z.carrier) (hy : y ∈ f '' C) : lf y ∈ C ∧ f (lf y) = y := by
    simpa only [lf, dif_pos hy] using hy.choose_spec
  let F : Q.carrier → Z.carrier := f ∘ lq
  let G : Z.carrier → Q.carrier := q ∘ lf
  have hF (x : M) (hx : x ∈ C) : F (q x) = f x := by
    have h := hlq (q x) (mem_image_of_mem q hx)
    exact (hfibers _ h.1 x hx).mp h.2
  have hG (x : M) (hx : x ∈ C) : G (f x) = q x := by
    have h := hlf (f x) (mem_image_of_mem f hx)
    exact (hfibers _ h.1 x hx).mpr h.2
  have hFs : ContMDiffOn (𝓡 3) (𝓡 3) ∞ F (q '' C) := by
    rintro _ ⟨x, hx, rfl⟩
    apply ContMDiffAt.contMDiffWithinAt
    let h := hq x
    have hi : h.localInverse (q x) = x := h.localInverse_left_inv h.localInverse_mem_target
    have hs := hf.contMDiff.contMDiffAt.comp (q x) h.localInverse_contMDiffAt
    apply hs.congr_of_eventuallyEq
    have hmem : h.localInverse ⁻¹' C ∈ 𝓝 (q x) :=
      h.localInverse_contMDiffAt.continuousAt.preimage_mem_nhds
        (hC.mem_nhds (hi.symm ▸ hx))
    filter_upwards [hmem, h.localInverse.open_source.mem_nhds h.localInverse_mem_source]
      with y hy hyS
    have he := hF (h.localInverse y) hy
    rw [h.localInverse_right_inv hyS] at he
    exact he
  have hGs : ContMDiffOn (𝓡 3) (𝓡 3) ∞ G (f '' C) := by
    rintro _ ⟨x, hx, rfl⟩
    apply ContMDiffAt.contMDiffWithinAt
    let h := hf x
    have hi : h.localInverse (f x) = x := h.localInverse_left_inv h.localInverse_mem_target
    have hs := hq.contMDiff.contMDiffAt.comp (f x) h.localInverse_contMDiffAt
    apply hs.congr_of_eventuallyEq
    have hmem : h.localInverse ⁻¹' C ∈ 𝓝 (f x) :=
      h.localInverse_contMDiffAt.continuousAt.preimage_mem_nhds
        (hC.mem_nhds (hi.symm ▸ hx))
    filter_upwards [hmem, h.localInverse.open_source.mem_nhds h.localInverse_mem_source]
      with y hy hyS
    have he := hG (h.localInverse y) hy
    rw [h.localInverse_right_inv hyS] at he
    exact he
  refine ⟨{
    toFun := F
    invFun := G
    source := q '' C
    target := f '' C
    map_source' := ?_
    map_target' := ?_
    left_inv' := ?_
    right_inv' := ?_
    open_source := hq.isLocalHomeomorph.isOpenMap C hC
    open_target := hf.isLocalHomeomorph.isOpenMap C hC
    contMDiffOn_toFun := hFs
    contMDiffOn_invFun := hGs }, rfl, rfl, hF⟩
  · rintro _ ⟨x, hx, rfl⟩
    rw [hF x hx]
    exact mem_image_of_mem f hx
  · rintro _ ⟨x, hx, rfl⟩
    rw [hG x hx]
    exact mem_image_of_mem q hx
  · rintro _ ⟨x, hx, rfl⟩
    rw [hF x hx, hG x hx]
  · rintro _ ⟨x, hx, rfl⟩
    rw [hG x hx, hF x hx]

end PoincareConjecture.M38
