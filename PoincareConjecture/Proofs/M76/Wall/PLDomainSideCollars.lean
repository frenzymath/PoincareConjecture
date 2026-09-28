import PoincareConjecture.Proofs.M76.Wall.Mathlib.AffineHalfspaceProduct
import PoincareConjecture.Proofs.M76.Wall.OppositePLDomain
import PoincareConjecture.Proofs.M76.Brown.AmbientSideCollars










set_option autoImplicit false

open Set Geometry BrownCollar

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)





theorem PLDomain.exists_side_collars
    {X ι : Type*} [MetricSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {P : Set X}
    (hP : PLDomain e P) (hF : IsCompact (frontier P))
    (hne : (frontier P).Nonempty) :
    ∃ C : AmbientSideCollars (frontier P),
      C.positive = P ∧ C.negative = (interior P)ᶜ := by
  classical
  let : CompactSpace (frontier P) := isCompact_iff_compactSpace.mp hF
  let : Nonempty (frontier P) := hne.to_subtype
  have hFP : frontier P ⊆ P := hP.closed.frontier_subset
  have hFQ : frontier P ⊆ (interior P)ᶜ := fun _ hx => hx.2
  have hlocal (x : frontier P) :
      ∃ B : OpenPartialHomeomorph X (V2 × ℝ), (x : X) ∈ B.source ∧
        (∀ y ∈ B.source, y ∈ frontier P ↔ (B y).2 = 0) ∧
        (∀ y ∈ B.source, y ∈ P ↔ 0 ≤ (B y).2) ∧
        ∀ y ∈ B.source, y ∈ (interior P)ᶜ ↔ (B y).2 ≤ 0 := by
    obtain ⟨ell, v, B, hv, hxB, _, _, hhalf⟩ := hP.halfspace x x.property
    have hell : ell.toAffineMap.linear ≠ 0 := by
      intro h
      have hval : ell.toAffineMap.linear v = 1 := hv
      rw [h] at hval
      norm_num at hval
    obtain ⟨T, hT⟩ := ell.exists_halfspace_product_homeomorph (F := V2) v hv (by simp)
    let B' := B.transHomeomorph T
    refine ⟨B', hxB, ?_, ?_, ?_⟩
    · intro y hy
      change y ∈ frontier P ↔ (T (B y)).2 = 0
      rw [hT]
      exact ((B.isImage_frontier_of_affine_nonneg ell hell hhalf).apply_mem_iff hy).symm
    · intro y hy
      change y ∈ P ↔ 0 ≤ (T (B y)).2
      rw [hT]
      exact hhalf y hy
    · intro y hy
      change y ∉ interior P ↔ (T (B y)).2 ≤ 0
      rw [hT, B.mem_interior_iff_affine_pos ell hell hhalf hy]
      exact not_lt
  have hpos (x : frontier P) :
      ∃ c : OpenPartialHomeomorph (frontier P × Ico (0 : ℝ) 1) P,
        collarBase x ∈ c.source ∧
          ∀ a, collarBase a ∈ c.source → c (collarBase a) = Set.inclusion hFP a := by
    obtain ⟨B, hxB, hpair, hside, _⟩ := hlocal x
    exact exists_positive_halfspace_local_collar B hFP hpair hside x hxB
  have hneg (x : frontier P) :
      ∃ c : OpenPartialHomeomorph (frontier P × Ico (0 : ℝ) 1)
          ((interior P)ᶜ : Set X),
        collarBase x ∈ c.source ∧
          ∀ a, collarBase a ∈ c.source → c (collarBase a) = Set.inclusion hFQ a := by
    obtain ⟨B, hxB, hpair, _, hside⟩ := hlocal x
    exact exists_negative_halfspace_local_collar B hFQ hpair hside x hxB
  obtain ⟨Up, hUp, _, cp, hcp⟩ := exists_full_collar_of_compact_local_patches
    (Set.inclusion hFP) (Set.inclusion_injective hFP) hpos
  obtain ⟨Um, hUm, _, cm, hcm⟩ := exists_full_collar_of_compact_local_patches
    (Set.inclusion hFQ) (Set.inclusion_injective hFQ) hneg
  have hunion : P ∪ (interior P)ᶜ = univ := by
    apply eq_univ_of_forall
    intro x
    by_cases hx : x ∈ P
    · exact Or.inl hx
    · exact Or.inr (fun hi => hx (interior_subset hi))
  have hinter : P ∩ (interior P)ᶜ = frontier P := by
    simp only [frontier, hP.closed.closure_eq, sdiff_eq]
  let C : AmbientSideCollars (frontier P) :=
    { neighborhood := univ
      positive := P
      negative := (interior P)ᶜ
      open_neighborhood := isOpen_univ
      base_subset := subset_univ _
      union_eq := hunion
      inter_eq := hinter
      positive_closed := hP.closed.preimage continuous_subtype_val
      negative_closed := isOpen_interior.isClosed_compl.preimage continuous_subtype_val
      positive_range := Up
      negative_range := Um
      positive_open := hUp
      negative_open := hUm
      positive_collar := cp
      negative_collar := cm
      positive_base := fun s => congrArg (Subtype.val : P → X) (hcp s)
      negative_base := fun s =>
        congrArg (Subtype.val : ((interior P)ᶜ : Set X) → X) (hcm s) }
  exact ⟨C, rfl, rfl⟩

end PoincareConjecture.M76
