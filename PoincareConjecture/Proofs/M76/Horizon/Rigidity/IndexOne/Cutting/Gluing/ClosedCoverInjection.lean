import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Cutting.Rim.SignedCharts
import PoincareConjecture.Proofs.M76.Brown.BicollarOpenHalves

set_option autoImplicit false
open Set BrownCollar

namespace PoincareConjecture.M76.HamiltonIntervalTorus

theorem exists_side_collars_of_closed_cover
    {X : Type*} [MetricSpace X] {N M : Set X}
    (hN : IsClosed N) (hM : IsClosed M) (hcover : N ∪ M = univ)
    (hcompact : IsCompact (N ∩ M)) (hne : (N ∩ M).Nonempty)
    (hlocalN : ∀ x : ↥(N ∩ M),
      ∃ c : OpenPartialHomeomorph (↥(N ∩ M) × Ico (0 : ℝ) 1) N,
        collarBase x ∈ c.source ∧
          ∀ a, collarBase a ∈ c.source → c (collarBase a) = Set.inclusion inter_subset_left a)
    (hlocalM : ∀ x : ↥(N ∩ M),
      ∃ c : OpenPartialHomeomorph (↥(N ∩ M) × Ico (0 : ℝ) 1) M,
        collarBase x ∈ c.source ∧
          ∀ a, collarBase a ∈ c.source → c (collarBase a) = Set.inclusion inter_subset_right a) :
    ∃ C : AmbientSideCollars (N ∩ M), C.positive = N ∧ C.negative = M := by
  let : CompactSpace ↥(N ∩ M) := isCompact_iff_compactSpace.mp hcompact
  let : Nonempty ↥(N ∩ M) := hne.to_subtype
  obtain ⟨Up, hUp, _, cp, hcp⟩ := exists_full_collar_of_compact_local_patches
    (Set.inclusion (inter_subset_left : N ∩ M ⊆ N))
    (Set.inclusion_injective _) hlocalN
  obtain ⟨Um, hUm, _, cm, hcm⟩ := exists_full_collar_of_compact_local_patches
    (Set.inclusion (inter_subset_right : N ∩ M ⊆ M))
    (Set.inclusion_injective _) hlocalM
  let C : AmbientSideCollars (N ∩ M) :=
    { neighborhood := univ
      positive := N
      negative := M
      open_neighborhood := isOpen_univ
      base_subset := subset_univ _
      union_eq := hcover
      inter_eq := rfl
      positive_closed := hN.preimage continuous_subtype_val
      negative_closed := hM.preimage continuous_subtype_val
      positive_range := Up
      negative_range := Um
      positive_open := hUp
      negative_open := hUm
      positive_collar := cp
      negative_collar := cm
      positive_base := fun x => congrArg (Subtype.val : N → X) (hcp x)
      negative_base := fun x => congrArg (Subtype.val : M → X) (hcm x) }
  exact ⟨C, rfl, rfl⟩

theorem frontier_eq_of_closed_cover_side_collars
    {X : Type*} [TopologicalSpace X] {N M : Set X}
    (hN : IsClosed N) (hM : IsClosed M) (hcover : N ∪ M = univ)
    (C : AmbientSideCollars (N ∩ M)) (hpos : C.positive = N) :
    frontier N = N ∩ M ∧ M = (interior N)ᶜ := by
  have hcomp : Mᶜ ⊆ N := by
    intro x hx
    exact ((Set.ext_iff.mp hcover x).mpr (mem_univ x)).resolve_right hx
  have hnegative : range (negativeBicollarMap C.bicollarHomeomorph) ⊆ Nᶜ := by
    rintro y ⟨z, rfl⟩ hy
    have ht := (C.bicollar_mem_positive_iff
      (z.1, ⟨z.2.val, z.2.property.1, lt_trans z.2.property.2 (by norm_num)⟩)).mp
        (hpos.symm.subset hy)
    exact (not_le_of_gt z.2.property.2) ht
  have hfront : frontier N = N ∩ M := by
    apply Subset.antisymm
    · intro x hx
      refine ⟨hN.frontier_subset hx, ?_⟩
      by_contra hxM
      exact hx.2 (interior_mono hcomp (hM.isOpen_compl.interior_eq.symm ▸ hxM))
    · intro x hx
      have hc := closure_mono hnegative
        (base_subset_closure_negativeBicollarMap C.bicollarHomeomorph
          C.bicollarHomeomorph_base hx)
      rw [closure_compl] at hc
      rw [frontier, hN.closure_eq]
      exact ⟨hx.1, hc⟩
  refine ⟨hfront, ?_⟩
  ext x
  constructor
  · intro hxM hxint
    exact (hfront.symm.subset ⟨interior_subset hxint, hxM⟩).2 hxint
  · intro hx
    by_contra hxM
    exact hx (interior_mono hcomp (hM.isOpen_compl.interior_eq.symm ▸ hxM))

theorem nonempty_openFrontierCollapse_of_closed_cover_local_collars
    {X : Type*} [MetricSpace X] {N M : Set X}
    (hN : IsClosed N) (hM : IsClosed M) (hcover : N ∪ M = univ)
    (hcompact : IsCompact (N ∩ M)) (hne : (N ∩ M).Nonempty)
    (hlocalN : ∀ x : ↥(N ∩ M),
      ∃ c : OpenPartialHomeomorph (↥(N ∩ M) × Ico (0 : ℝ) 1) N,
        collarBase x ∈ c.source ∧
          ∀ a, collarBase a ∈ c.source → c (collarBase a) = Set.inclusion inter_subset_left a)
    (hlocalM : ∀ x : ↥(N ∩ M),
      ∃ c : OpenPartialHomeomorph (↥(N ∩ M) × Ico (0 : ℝ) 1) M,
        collarBase x ∈ c.source ∧
          ∀ a, collarBase a ∈ c.source → c (collarBase a) = Set.inclusion inter_subset_right a) :
    frontier N = N ∩ M ∧ M = (interior N)ᶜ ∧ Nonempty (OpenFrontierCollapse N) := by
  obtain ⟨C, hpos, hneg⟩ := exists_side_collars_of_closed_cover
    hN hM hcover hcompact hne hlocalN hlocalM
  obtain ⟨hfront, hother⟩ := frontier_eq_of_closed_cover_side_collars hN hM hcover C hpos
  have hcollar : ∃ U : Set X, IsOpen U ∧
      ∃ H : (frontier N × Ioo (-1 : ℝ) 1) ≃ₜ U,
        (∀ x, (H (bicollarBase x) : X) = (x : X)) ∧
        (∀ z, (H z : X) ∈ N ↔ 0 ≤ (z.2 : ℝ)) ∧
        (∀ z, (H z : X) ∈ (interior N)ᶜ ↔ (z.2 : ℝ) ≤ 0) ∧
        ∀ z, (H z : X) ∈ frontier N ↔ (z.2 : ℝ) = 0 := by
    rw [hfront]
    refine ⟨C.collarUnion, C.isOpen_collarUnion, C.bicollarHomeomorph,
      C.bicollarHomeomorph_base, ?_, ?_, C.bicollar_mem_base_iff⟩
    · simpa only [hpos] using C.bicollar_mem_positive_iff
    · simpa only [hneg, hother] using C.bicollar_mem_negative_iff
  obtain ⟨U, hU, H, hbase, hp, hm, hz⟩ := hcollar
  exact ⟨hfront, hother, nonempty_openFrontierCollapse_of_open_bicollar hN
    (hfront.symm ▸ hcompact) (hfront.symm ▸ hne) hU H hbase hp hm hz⟩

theorem closed_cover_sides_pi1_injective
    {X : Type*} [MetricSpace X] {N M : Set X}
    (hN : IsClosed N) (hM : IsClosed M) (hcover : N ∪ M = univ)
    (hcompact : IsCompact (N ∩ M)) (hne : (N ∩ M).Nonempty)
    (hlocalN : ∀ x : ↥(N ∩ M),
      ∃ c : OpenPartialHomeomorph (↥(N ∩ M) × Ico (0 : ℝ) 1) N,
        collarBase x ∈ c.source ∧
          ∀ a, collarBase a ∈ c.source → c (collarBase a) = Set.inclusion inter_subset_left a)
    (hlocalM : ∀ x : ↥(N ∩ M),
      ∃ c : OpenPartialHomeomorph (↥(N ∩ M) × Ico (0 : ℝ) 1) M,
        collarBase x ∈ c.source ∧
          ∀ a, collarBase a ∈ c.source → c (collarBase a) = Set.inclusion inter_subset_right a)
    (hpiN : ∀ x : ↥(N ∩ M), Function.Injective
      (FundamentalGroup.map (ContinuousMap.inclusion inter_subset_left) x))
    (hpiM : ∀ x : ↥(N ∩ M), Function.Injective
      (FundamentalGroup.map (ContinuousMap.inclusion inter_subset_right) x)) :
    ∀ T ∈ ({N, M} : Set (Set X)), ∀ x : T,
      Function.Injective (FundamentalGroup.map (VanKampen.inclusion T) x) := by
  obtain ⟨hfront, hother, ⟨C⟩⟩ :=
    nonempty_openFrontierCollapse_of_closed_cover_local_collars
      hN hM hcover hcompact hne hlocalN hlocalM
  have hpi : ∀ T ∈ ({N, (interior N)ᶜ} : Set (Set X)),
      ∃ hFT : frontier N ⊆ T, ∀ x : frontier N,
        Function.Injective (FundamentalGroup.map (ContinuousMap.inclusion hFT) x) := by
    rw [hfront, ← hother]
    intro T hT
    rcases hT with rfl | rfl
    · exact ⟨inter_subset_left, hpiN⟩
    · exact ⟨inter_subset_right, hpiM⟩
  simpa only [hother] using C.side_ambient_injective hN hpi

end PoincareConjecture.M76.HamiltonIntervalTorus
