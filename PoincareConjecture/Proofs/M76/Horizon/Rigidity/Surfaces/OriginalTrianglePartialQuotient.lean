import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.OriginalTrianglePointwiseGluing

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.OriginalTriangleCopies

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (K : SimplicialComplex ℝ E)

variable [FiniteDimensional ℝ E]

abbrev partialQuotient (label : Triangle K → ℝ)
    (contact : Triangle K → Triangle K → Prop) : Type _ :=
  Quotient (pointwiseGlueSetoid K label contact)

noncomputable def partialMk (label : Triangle K → ℝ)
    (contact : Triangle K → Triangle K → Prop) (x : carrier K label) :
    partialQuotient K label contact :=
  @Quotient.mk' (carrier K label) (pointwiseGlueSetoid K label contact) x

noncomputable def partialProjection (label : Triangle K → ℝ)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 3)
    (contact : Triangle K → Triangle K → Prop) :
    partialQuotient K label contact → K.space :=
  Quotient.lift (projectionMap K label hpure) (by
    intro x y hxy
    apply Subtype.ext
    exact pointwiseGlueRelation_fiber K label contact hxy)

@[simp] theorem partialProjection_mk (label : Triangle K → ℝ)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 3)
    (contact : Triangle K → Triangle K → Prop) (x : carrier K label) :
    partialProjection K label hpure contact (partialMk K label contact x) =
      projectionMap K label hpure x :=
  rfl

theorem partialProjection_surjective (label : Triangle K → ℝ)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 3)
    (contact : Triangle K → Triangle K → Prop) :
    Function.Surjective (partialProjection K label hpure contact) := by
  intro z
  obtain ⟨x, hx⟩ := projectionMap_surjective K label hpure z
  refine ⟨partialMk K label contact x, ?_⟩
  exact hx

theorem continuous_partialProjection (label : Triangle K → ℝ)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 3)
    (contact : Triangle K → Triangle K → Prop) :
    Continuous (partialProjection K label hpure contact) := by
  apply (@isQuotientMap_quotient_mk' (carrier K label) _
    (pointwiseGlueSetoid K label contact)).continuous_iff.mpr
  change Continuous (fun x : carrier K label =>
    partialProjection K label hpure contact (partialMk K label contact x))
  simp only [partialProjection_mk]
  exact continuous_projectionMap K label hpure

theorem partialProjection_isQuotientMap (hK : K.faces.Finite)
    (label : Triangle K → ℝ)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 3)
    (contact : Triangle K → Triangle K → Prop) :
    Topology.IsQuotientMap (partialProjection K label hpure contact) := by
  letI : CompactSpace (carrier K label) :=
    isCompact_iff_compactSpace.mp (isCompact_carrier K hK label)
  letI : CompactSpace (partialQuotient K label contact) := inferInstance
  exact Topology.IsQuotientMap.of_surjective_continuous
    (partialProjection_surjective K label hpure contact)
    (continuous_partialProjection K label hpure contact)

theorem partialQuotient_mk_eq_iff (label : Triangle K → ℝ)
    (contact : Triangle K → Triangle K → Prop)
    (x y : carrier K label) :
    partialMk K label contact x = partialMk K label contact y ↔
      pointwiseGlueRelation K label contact x y := by
  exact @Quotient.eq' (carrier K label) (pointwiseGlueSetoid K label contact) x y

theorem partialProjection_eq_of_glue (label : Triangle K → ℝ)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 3)
    (contact : Triangle K → Triangle K → Prop)
    {x y : carrier K label}
    (hxy : pointwiseGlueRelation K label contact x y) :
    partialProjection K label hpure contact (partialMk K label contact x) =
      partialProjection K label hpure contact (partialMk K label contact y) := by
  rw [partialProjection_mk, partialProjection_mk]
  apply Subtype.ext
  exact pointwiseGlueRelation_fiber K label contact hxy

theorem partialProjection_fiber_coordinate (label : Triangle K → ℝ)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 3)
    (contact : Triangle K → Triangle K → Prop)
    {x y : carrier K label}
    (hxy : partialProjection K label hpure contact (partialMk K label contact x) =
      partialProjection K label hpure contact (partialMk K label contact y)) :
    x.1.1 = y.1.1 := by
  apply Subtype.ext_iff.mp at hxy
  exact hxy

noncomputable def partialProjectionHomeomorph_of_complete
    (hK : K.faces.Finite)
    (label : Triangle K → ℝ)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 3)
    (contact : Triangle K → Triangle K → Prop)
    (hcomplete : ∀ x y : carrier K label,
      x.1.1 = y.1.1 → pointwiseGlueRelation K label contact x y) :
    partialQuotient K label contact ≃ₜ K.space := by
  have hrel : ∀ x y : carrier K label,
      pointwiseGlueSetoid K label contact x y ↔
        Setoid.ker (projectionMap K label hpure) x y := by
    intro x y
    change pointwiseGlueRelation K label contact x y ↔
      projectionMap K label hpure x = projectionMap K label hpure y
    constructor
    · intro hxy
      apply Subtype.ext
      exact pointwiseGlueRelation_fiber K label contact hxy
    · intro hxy
      apply hcomplete x y
      exact congrArg Subtype.val hxy
  let qh : Quotient (pointwiseGlueSetoid K label contact) ≃ₜ
      Quotient (Setoid.ker (projectionMap K label hpure)) :=
    Homeomorph.Quotient.congrRight hrel
  exact qh.trans (projectionQuotientHomeomorph K hK label hpure)

end PoincareConjecture.M76.OriginalTriangleCopies
