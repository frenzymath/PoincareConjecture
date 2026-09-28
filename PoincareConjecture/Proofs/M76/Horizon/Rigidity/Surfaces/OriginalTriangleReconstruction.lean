import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.OriginalTriangleCopies
import Mathlib.Topology.Homeomorph.Quotient

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.OriginalTriangleCopies

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (K : SimplicialComplex ℝ E)

variable [FiniteDimensional ℝ E]

theorem isCompact_carrier (hK : K.faces.Finite) (label : Triangle K → ℝ) :
    IsCompact (carrier K label) := by
  classical
  letI : Finite (Triangle K) :=
    (hK.subset (fun _ h ↦ h.1)).to_subtype
  apply isCompact_iUnion
  intro s
  rw [copy]
  exact (s.val.finite_toSet.isCompact_convexHull ℝ).image
    (inclusion (E := E) (label s)).continuous

noncomputable def projectionMap (label : Triangle K → ℝ)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 3) :
    carrier K label → K.space := fun x ↦
  ⟨x.1.1, by
    obtain ⟨s, hs⟩ := mem_iUnion.mp x.2
    exact K.convexHull_subset_space s.property.1
      ((mem_copy_iff K label s x.1).mp hs).1⟩

theorem projectionMap_apply (label : Triangle K → ℝ)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 3)
    (x : carrier K label) :
    projectionMap K label hpure x = ⟨x.1.1, by
      obtain ⟨s, hs⟩ := mem_iUnion.mp x.2
      exact K.convexHull_subset_space s.property.1
        ((mem_copy_iff K label s x.1).mp hs).1⟩ := rfl

theorem continuous_projectionMap (label : Triangle K → ℝ)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 3) :
    Continuous (projectionMap K label hpure) := by
  apply continuous_induced_rng.mpr
  change Continuous (fun x : carrier K label ↦ x.1.1)
  exact continuous_fst.comp continuous_subtype_val

theorem projectionMap_surjective (label : Triangle K → ℝ)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 3) :
    Function.Surjective (projectionMap K label hpure) := by
  intro x
  have hximg : x.1 ∈ Prod.fst '' carrier K label := by
    rw [projection_carrier K label hpure]
    exact x.2
  obtain ⟨y, hy, hxy⟩ := hximg
  exact ⟨⟨y, hy⟩, Subtype.ext hxy⟩

theorem projectionMap_isQuotientMap (hK : K.faces.Finite)
    (label : Triangle K → ℝ)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 3) :
    Topology.IsQuotientMap (projectionMap K label hpure) := by
  letI : CompactSpace (carrier K label) :=
    isCompact_iff_compactSpace.mp (isCompact_carrier K hK label)
  exact Topology.IsQuotientMap.of_surjective_continuous
    (projectionMap_surjective K label hpure)
    (continuous_projectionMap K label hpure)

noncomputable def projectionQuotientHomeomorph (hK : K.faces.Finite)
    (label : Triangle K → ℝ)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 3) :
    Quotient (Setoid.ker (projectionMap K label hpure)) ≃ₜ K.space := by
  letI : CompactSpace (carrier K label) :=
    isCompact_iff_compactSpace.mp (isCompact_carrier K hK label)
  let f : C(carrier K label, K.space) :=
    ⟨projectionMap K label hpure, continuous_projectionMap K label hpure⟩
  have hf : Topology.IsQuotientMap (f : carrier K label → K.space) := by
    exact projectionMap_isQuotientMap K hK label hpure
  exact hf.homeomorph

theorem projection_kernel_iff (label : Triangle K → ℝ)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 3)
    (x y : carrier K label) :
    Setoid.ker (projectionMap K label hpure) x y ↔ x.1.1 = y.1.1 := by
  change projectionMap K label hpure x = projectionMap K label hpure y ↔ _
  rw [Subtype.ext_iff]
  rfl

end PoincareConjecture.M76.OriginalTriangleCopies
