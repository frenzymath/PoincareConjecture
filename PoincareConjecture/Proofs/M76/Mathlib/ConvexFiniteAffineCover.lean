import PoincareConjecture.Proofs.M76.Mathlib.AffineSubspaceAvoidance
import Mathlib.Analysis.Convex.Intrinsic










set_option autoImplicit false

open Set

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Finite ι]






theorem Convex.exists_subset_affineSubspace_of_subset_iUnion
    {s : Set E} (hcv : Convex ℝ s) (hne : s.Nonempty)
    (A : ι → AffineSubspace ℝ E) (hcover : s ⊆ ⋃ i, (A i : Set E)) :
    ∃ i, s ⊆ A i := by
  classical
  by_contra h
  have hnot : ∀ i, ¬s ⊆ A i := not_exists.mp h
  obtain ⟨p, hp⟩ := hne
  let W := affineSpan ℝ s
  let p' : W := ⟨p, subset_affineSpan ℝ s hp⟩
  let : Nonempty W := ⟨p'⟩
  let e := (AffineIsometryEquiv.constVSub ℝ p').symm
  let f : W.direction →ᵃ[ℝ] E := W.subtype.comp e.toAffineEquiv.toAffineMap
  let B : ι → AffineSubspace ℝ W.direction := fun i => (A i).comap f
  have hB (i : ι) : B i ≠ ⊤ := by
    intro heq
    apply hnot i
    intro x hx
    let x' : W := ⟨x, subset_affineSpan ℝ s hx⟩
    have hmem : e.symm x' ∈ B i := by
      rw [heq]
      trivial
    change ((e (e.symm x') : W) : E) ∈ A i at hmem
    rw [AffineIsometryEquiv.apply_symm_apply] at hmem
    exact hmem
  have hU : (interior ((↑) ⁻¹' s : Set W)).Nonempty := by
    simpa only [intrinsicInterior, image_nonempty] using
      Set.Nonempty.intrinsicInterior hcv ⟨p, hp⟩
  have hU' : (interior (f ⁻¹' s)).Nonempty := by
    change (interior (e.toHomeomorph ⁻¹' ((↑) ⁻¹' s : Set W))).Nonempty
    rw [← e.toHomeomorph.preimage_interior]
    obtain ⟨x, hx⟩ := hU
    exact ⟨e.symm x, by simpa using hx⟩
  have hdense := AffineSubspace.dense_compl_iUnion B hB
  obtain ⟨x, hx, hxB⟩ := hdense.inter_open_nonempty _ isOpen_interior hU'
  have hxS : x ∈ f ⁻¹' s := interior_subset hx
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover hxS)
  exact hxB (mem_iUnion.mpr ⟨i, hi⟩)
