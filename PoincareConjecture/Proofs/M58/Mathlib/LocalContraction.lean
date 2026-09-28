import PoincareConjecture.Proofs.M58.Mathlib.LocalContractionFinite

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.Proofs.M58

theorem exists_local_contraction
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    [I.Boundaryless] [IsManifold I ∞ M]
    (hcompact : IsCompact (univ : Set M)) (k : ℕ) :
    ∃ (C : ℝ × (M × M) → M) (U : Set (M × M)),
      IsOpen U ∧ diagonal M ⊆ U ∧
      (∀ p q, C (0, p, q) = q) ∧
      (∀ v ∈ U, C (1, v) = v.1) ∧
      (∀ t p, C (t, p, p) = p) ∧
      ∀ v ∈ Icc (0 : ℝ) 1 ×ˢ U,
        ContMDiffAt (𝓘(ℝ, ℝ).prod (I.prod I)) I (k : ℕ∞ω) C v := by
  let : CompactSpace M := isCompact_univ_iff.mp hcompact
  obtain ⟨L, hcover⟩ := exists_finite_bump_plateau_cover I hcompact
  let C := chartContractionSequence I L
  let V : Set (ℝ × (M × M)) :=
    {v | ContMDiffAt (𝓘(ℝ, ℝ).prod (I.prod I)) I (k : ℕ∞ω) C v}
  have hV : IsOpen V := by
    apply isOpen_iff_mem_nhds.mpr
    intro v hv
    exact (contMDiffAt_iff_contMDiffAt_nhds (by simp)).mp hv
  have hIV : Icc (0 : ℝ) 1 ×ˢ diagonal M ⊆ V := by
    rintro ⟨t, p, q⟩ hv
    have hpq : p = q := hv.2
    subst q
    exact (contMDiffAt_chartContractionSequence_diagonal I L t p).of_le (mod_cast le_top)
  obtain ⟨T, U, -, hU, hT, hdiag, hTU⟩ :=
    generalized_tube_lemma isCompact_Icc isCompact_diagonal hV hIV
  let W : Set (M × M) := interior {v | C (1, v) = v.1}
  have hW : diagonal M ⊆ W := by
    rintro ⟨p, q⟩ hpq
    have hpq' : p = q := hpq
    subst q
    exact mem_interior_iff_mem_nhds.mpr
      (chartContractionSequence_one_eventually I L p (hcover p))
  refine ⟨C, U ∩ W, hU.inter isOpen_interior, subset_inter hdiag hW,
    chartContractionSequence_zero I L, ?_, chartContractionSequence_diagonal I L, ?_⟩
  · intro v hv
    have hv' : v ∈ {v | C (1, v) = v.1} := interior_subset hv.2
    exact hv'
  · intro v hv
    exact hTU ⟨hT hv.1, hv.2.1⟩

end PoincareConjecture.Proofs.M58
