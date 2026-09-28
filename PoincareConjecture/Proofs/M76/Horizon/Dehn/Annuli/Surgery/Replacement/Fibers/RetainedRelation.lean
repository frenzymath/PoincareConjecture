import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Replacement.Fibers.SingleFibers
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.Components.RetainedModels

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "V2" => (Fin 2 → ℝ)
local notation "Q" => sphere (0 : V2) 1
local notation "Cyl" => Set.prod Q (Icc (-1 : ℝ) 1)
local notation "Left" => Set.prod Q (Icc (-1 : ℝ) (-1 / 2))
local notation "Middle" => Set.prod Q (Icc (-1 / 2 : ℝ) 0)
local notation "Right" => Set.prod Q (Icc (0 : ℝ) 1)

theorem exists_resolving_retained_copy_relation
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {O I : Set E} {f : E → X} {g : (V2 × ℝ) → X} (hdis : Disjoint O I)
    (copyO : O ≃ₜ Left) (copyI : I ≃ₜ Right)
    (hO : copyO.IsFinitePL) (hI : copyI.IsFinitePL)
    (hkeepO : ∀ x : O, g (copyO x) = f x)
    (hkeepI : ∀ x : I, g (copyI x) = f x)
    (hsingle : ∀ z ∈ Middle, ∀ w ∈ Cyl, g w = g z → w = z) :
    ∃ j : (O ∪ I : Set E) → V2 × ℝ,
      Function.Injective j ∧ Continuous j ∧
      (∃ J : E → V2 × ℝ, FinitePiecewiseAffineOn J (O ∪ I) ∧
        ∀ x : (O ∪ I : Set E), J x = j x) ∧
      (∀ x : O, j ⟨x, Or.inl x.property⟩ = (copyO x : V2 × ℝ)) ∧
      (∀ x : I, j ⟨x, Or.inr x.property⟩ = (copyI x : V2 × ℝ)) ∧
      range j = Left ∪ Right ∧ (∀ x, j x ∈ Cyl) ∧ (∀ x, g (j x) = f x) ∧
      {v : (V2 × ℝ) × (V2 × ℝ) |
        v.1 ∈ Cyl ∧ v.2 ∈ Cyl ∧ g v.1 = g v.2 ∧ v.1 ≠ v.2} =
        (fun v : (O ∪ I : Set E) × (O ∪ I : Set E) ↦ (j v.1, j v.2)) ''
          {v | f v.1 = f v.2 ∧ (v.1 : E) ≠ v.2} ∧
      doubleLocusOn g Cyl =
        j '' {x : (O ∪ I : Set E) | ∃ y : (O ∪ I : Set E),
          f x = f y ∧ (x : E) ≠ y} := by
  let jO : O → V2 × ℝ := fun x ↦ copyO x
  let jI : I → V2 × ℝ := fun x ↦ copyI x
  let j := joinSourceCopies hdis jO jI
  have hrO : range jO = Left := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact (copyO x).property
    · intro hy
      exact ⟨copyO.symm ⟨y, hy⟩, congrArg Subtype.val (copyO.apply_symm_apply ⟨y, hy⟩)⟩
  have hrI : range jI = Right := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact (copyI x).property
    · intro hy
      exact ⟨copyI.symm ⟨y, hy⟩, congrArg Subtype.val (copyI.apply_symm_apply ⟨y, hy⟩)⟩
  have hLR : Disjoint Left Right := by
    apply disjoint_left.mpr
    intro z hz hw
    linarith [hz.2.2, hw.2.1]
  have hji : Function.Injective j := joinSourceCopies_injective hdis
    (Subtype.val_injective.comp copyO.injective) (Subtype.val_injective.comp copyI.injective)
    (by rw [hrO, hrI]; exact hLR)
  obtain ⟨JO, hJO, hJOval⟩ := hO
  obtain ⟨JI, hJI, hJIval⟩ := hI
  have hjc : Continuous j := joinSourceCopies_continuous hdis
    hJO.isCompact.isClosed hJI.isCompact.isClosed
    (continuous_subtype_val.comp copyO.continuous) (continuous_subtype_val.comp copyI.continuous)
  have hjPL : ∃ J : E → V2 × ℝ, FinitePiecewiseAffineOn J (O ∪ I) ∧
      ∀ x : (O ∪ I : Set E), J x = j x := joinSourceCopies_exists_finitePL_extension hdis jO jI
    ⟨JO, hJO, fun x ↦ (hJOval x).symm⟩ ⟨JI, hJI, fun x ↦ (hJIval x).symm⟩
  have hrange : range j = Left ∪ Right := by rw [joinSourceCopies_range, hrO, hrI]
  have hcover : range j ∪ Middle = Cyl := by
    rw [hrange]
    ext z
    constructor
    · rintro ((hz | hz) | hz)
      · exact ⟨hz.1, hz.2.1, by linarith [hz.2.2]⟩
      · exact ⟨hz.1, by linarith [hz.2.1], hz.2.2⟩
      · exact ⟨hz.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩
    · intro hz
      by_cases hlo : z.2 ≤ -1 / 2
      · exact Or.inl (Or.inl ⟨hz.1, hz.2.1, hlo⟩)
      · by_cases hhi : 0 ≤ z.2
        · exact Or.inl (Or.inr ⟨hz.1, hhi, hz.2.2⟩)
        · exact Or.inr ⟨hz.1, (lt_of_not_ge hlo).le, (lt_of_not_ge hhi).le⟩
  have hkeep : ∀ x, g (j x) = f x := joinSourceCopies_target hdis hkeepO hkeepI
  exact ⟨j, hji, hjc, hjPL,
    fun x ↦ joinSourceCopies_left hdis jO jI _ x.property,
    fun x ↦ joinSourceCopies_right hdis jO jI _ x.property,
    hrange, fun x ↦ hcover.subset (Or.inl (mem_range_self x)), hkeep,
    retained_double_relation_eq j hji hcover hkeep hsingle,
    retained_double_locus_eq j hji hcover hkeep hsingle⟩

end PoincareConjecture.M76.Dehn.Annuli
