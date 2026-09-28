import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallPairs

set_option autoImplicit false

open Set Geometry

namespace Set

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup X] [NormedSpace ℝ X] {d q : Set X}

theorem IsFinitePLBallPair.isCompact (hd : IsFinitePLBallPair E d q) : IsCompact d := by
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hspace, _⟩, _⟩, _⟩ := hd
  rw [← hspace]
  exact K.isCompact_space_of_finite hK

theorem IsFinitePLBallPair.sdiff_nonempty (hd : IsFinitePLBallPair E d q) :
    (d \ q).Nonempty := by
  obtain ⟨_, C, _, _, ⟨y, hy⟩, e, _, heb⟩ := hd
  let z : C := ⟨y, interior_subset hy⟩
  refine ⟨e.symm z, (e.symm z).property, ?_⟩
  intro hq
  have hfront := (heb (e.symm z)).mp hq
  rw [e.apply_symm_apply] at hfront
  exact hfront.2 hy

theorem IsFinitePLBallPair.closure_sdiff (hd : IsFinitePLBallPair E d q) :
    closure (d \ q) = d := by
  have hdc := hd.isCompact.isClosed
  obtain ⟨_, C, hC, hcv, hne, e, _, heb⟩ := hd
  let I : Set C := (Subtype.val : C → E) ⁻¹' interior C
  have hIimage : (Subtype.val : C → E) '' I = interior C :=
    image_preimage_eq_of_subset (by simpa using (interior_subset : interior C ⊆ C))
  have hIclosure : closure I = univ := by
    rw [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image, hIimage,
      hcv.closure_interior_eq_closure_of_nonempty_interior hne, hC.isClosed.closure_eq]
    ext x
    simp only [mem_preimage, x.property, mem_univ]
  let g : C → X := fun y => e.symm y
  have hgc : Continuous g := continuous_subtype_val.comp e.symm.continuous
  have hgI : g '' I = d \ q := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨(e.symm y).property, ?_⟩
      intro hq
      have hf := (heb (e.symm y)).mp hq
      rw [e.apply_symm_apply] at hf
      exact hf.2 hy
    · intro hx
      let z : d := ⟨x, hx.1⟩
      refine ⟨e z, ?_, by simp [g, z]⟩
      by_contra hi
      exact hx.2 ((heb z).mpr ⟨subset_closure (e z).property, hi⟩)
  apply Subset.antisymm (closure_minimal sdiff_subset hdc)
  intro x hx
  have him : x ∈ g '' closure I := by
    rw [hIclosure]
    exact ⟨e ⟨x, hx⟩, mem_univ _, by simp [g]⟩
  rw [← hgI]
  exact image_closure_subset_closure_image hgc him

theorem IsFinitePLBallPair.closure_preimage_sdiff (hd : IsFinitePLBallPair E d q)
    {s : Set X} (hds : d ⊆ s) :
    closure ((Subtype.val : s → X) ⁻¹' (d \ q)) = (Subtype.val : s → X) ⁻¹' d := by
  rw [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image,
    image_preimage_eq_of_subset (by simpa using (sdiff_subset.trans hds : d \ q ⊆ s)),
    hd.closure_sdiff]

theorem IsFinitePLBallPair.frontier_preimage_val (hd : IsFinitePLBallPair E d q)
    {s : Set X} (hint : interior ((Subtype.val : s → X) ⁻¹' d) =
      (Subtype.val : s → X) ⁻¹' (d \ q)) :
    frontier ((Subtype.val : s → X) ⁻¹' d) = (Subtype.val : s → X) ⁻¹' q := by
  rw [frontier, (hd.isCompact.isClosed.preimage continuous_subtype_val).closure_eq, hint]
  ext x
  change ((x : X) ∈ d ∧ ¬ ((x : X) ∈ d ∧ (x : X) ∉ q)) ↔ (x : X) ∈ q
  constructor
  · intro hx
    by_contra hq
    exact hx.2 ⟨hx.1, hq⟩
  · intro hx
    exact ⟨hd.1 hx, fun h => h.2 hx⟩

end Set
