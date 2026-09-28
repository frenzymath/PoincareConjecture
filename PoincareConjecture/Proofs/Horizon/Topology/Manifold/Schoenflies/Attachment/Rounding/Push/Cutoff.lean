import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Attachment.Rounding.Push.Graph









set_option autoImplicit false

open Set Metric TopologicalSpace
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Rounding

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [TopologicalSpace M]



theorem exists_slab_cutoff
    (C : Opens M) (e : C ≃ₜ E × Real) {B U : Set M}
    (hB : IsCompact B) (hU : IsOpen U)
    (hslab : B ∩ C = (fun p : E × Real => (e.symm p : M)) ''
      {p | 0 ≤ p.2 ∧ p.2 ≤ 1})
    (hedge : B \ C ⊆ U) :
    ∃ b : E → Real, ContDiff Real ∞ b ∧ HasCompactSupport b ∧
      (∀ x, b x ∈ Icc (0 : Real) 1) ∧
      (∀ x t, t ∈ Icc (0 : Real) 1 → (e.symm (x, t * b x) : M) ∈ B) ∧
      (∀ p : E × Real, (e.symm p : M) ∈ B \ U → b p.1 = 1) ∧
      (((fun p : E × Real => (e.symm p : M)) ''
        {p | 0 ≤ p.2 ∧ p.2 ≤ b p.1}) \ U) = B \ U := by
  let q : E × Real → M := fun p => (e.symm p : M)
  have hBC (x : M) (hx : x ∈ B \ U) : x ∈ C := by
    by_contra hn
    exact hx.2 (hedge ⟨hx.1, hn⟩)
  have hc : IsCompact ((Subtype.val : C → M) ⁻¹' (B \ U)) :=
    Topology.IsInducing.subtypeVal.isCompact_preimage'
      (hB.diff hU)
      (by simpa only [Subtype.range_coe] using (show B \ U ⊆ C from hBC))
  let P : Set E := Prod.fst '' (e '' ((Subtype.val : C → M) ⁻¹' (B \ U)))
  have hP : IsCompact P := (hc.image e.continuous).image continuous_fst
  obtain ⟨L, hL, hPL, _⟩ := exists_compact_between hP isOpen_univ (subset_univ P)
  obtain ⟨b, hbOne, hbZero, hbRange⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior 𝓘(Real, E)
      hP.isClosed hPL (n := ⊤)
  have hbc : HasCompactSupport (b : E → Real) := by
    apply hL.of_isClosed_subset isClosed_closure
    apply closure_minimal _ hL.isClosed
    intro x hx
    by_contra hn
    exact hx (hbZero x hn)
  have hqB (p : E × Real) (hp : 0 ≤ p.2 ∧ p.2 ≤ 1) : q p ∈ B := by
    have hm : q p ∈ B ∩ C := hslab.symm ▸ mem_image_of_mem q hp
    exact hm.1
  have hOne (p : E × Real) (hp : (e.symm p : M) ∈ B \ U) : b p.1 = 1 := by
    apply hbOne.self_of_nhdsSet
    exact ⟨p, ⟨e.symm p, hp, e.apply_symm_apply p⟩, rfl⟩
  refine ⟨b, b.contMDiff.contDiff, hbc, hbRange, ?_, hOne, ?_⟩
  · intro x t ht
    apply hqB
    exact ⟨mul_nonneg ht.1 (hbRange x).1,
      (mul_le_mul ht.2 (hbRange x).2 (hbRange x).1 zero_le_one).trans (by norm_num)⟩
  · ext y
    constructor
    · rintro ⟨⟨p, hp, rfl⟩, hyU⟩
      exact ⟨hqB p ⟨hp.1, hp.2.trans (hbRange p.1).2⟩, hyU⟩
    · intro hy
      obtain ⟨p, hp, hpy⟩ :=
        (show y ∈ q '' {p | 0 ≤ p.2 ∧ p.2 ≤ 1} from hslab ▸ ⟨hy.1, hBC y hy⟩)
      have hpP : p.1 ∈ P := by
        refine ⟨p, ?_, rfl⟩
        refine ⟨e.symm p, ?_, e.apply_symm_apply p⟩
        change q p ∈ B \ U
        rwa [hpy]
      have hbp : b p.1 = 1 := hbOne.self_of_nhdsSet _ hpP
      exact ⟨⟨p, ⟨hp.1, by simpa only [hbp] using hp.2⟩, hpy⟩, hy.2⟩

end Poincare.Manifold.Schoenflies.Rounding
