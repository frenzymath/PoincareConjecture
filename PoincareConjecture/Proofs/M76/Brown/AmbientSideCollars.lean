import PoincareConjecture.Proofs.M76.Brown.AmbientSideRegions
import PoincareConjecture.Proofs.M76.Brown.HalfspaceLocalCollars
import PoincareConjecture.Proofs.M76.Brown.CompactCollaring

set_option autoImplicit false

open Set

namespace BrownCollar

variable {X : Type*} [TopologicalSpace X]

structure AmbientSideCollars (S : Set X) where
  neighborhood : Set X
  positive : Set X
  negative : Set X
  open_neighborhood : IsOpen neighborhood
  base_subset : S ⊆ neighborhood
  union_eq : positive ∪ negative = neighborhood
  inter_eq : positive ∩ negative = S
  positive_closed : IsClosed ((Subtype.val : neighborhood → X) ⁻¹' positive)
  negative_closed : IsClosed ((Subtype.val : neighborhood → X) ⁻¹' negative)
  positive_range : Set positive
  negative_range : Set negative
  positive_open : IsOpen positive_range
  negative_open : IsOpen negative_range
  positive_collar : (S × Ico (0 : ℝ) 1) ≃ₜ positive_range
  negative_collar : (S × Ico (0 : ℝ) 1) ≃ₜ negative_range
  positive_base : ∀ s, ((positive_collar (collarBase s) : positive) : X) = (s : X)
  negative_base : ∀ s, ((negative_collar (collarBase s) : negative) : X) = (s : X)

end BrownCollar

namespace BrownCollar

variable {X P : Type*} [MetricSpace X] [TopologicalSpace P]

theorem exists_ambient_side_collars {S : Set X} (hS : IsCompact S) [Nonempty S]
    (E : S → OpenPartialHomeomorph X (P × ℝ))
    (hcover : ∀ x : S, (x : X) ∈ (E x).source)
    (hpair : ∀ i y, y ∈ (E i).source → (y ∈ S ↔ (E i y).2 = 0))
    (hgerm : ∀ i j (x : S), (x : X) ∈ (E i).source ∩ (E j).source →
      ∃ V : Set X, IsOpen V ∧ (x : X) ∈ V ∧
        EqOn (fun y => SignType.sign (E i y).2) (fun y => SignType.sign (E j y).2) V) :
    Nonempty (AmbientSideCollars S) := by
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  obtain ⟨W, Rp, Rm, hW, hSW, hu, hi, hpc, hmc, hlocal⟩ :=
    exists_ambient_side_regions hS E hcover hpair hgerm
  have hp : S ⊆ Rp := by
    rw [← hi]
    exact inter_subset_left
  have hm : S ⊆ Rm := by
    rw [← hi]
    exact inter_subset_right
  obtain ⟨hlp, hlm⟩ := exists_side_local_collars hp hm E hpair (by
    intro x
    obtain ⟨i, V, hV, hxV, hVE, _, hside⟩ := hlocal x
    exact ⟨i, V, hV, hxV, hVE, hside⟩)
  have hpinj : Function.Injective (Set.inclusion hp) := by
    intro x y h
    exact Subtype.ext (congrArg (fun z : Rp => (z : X)) h)
  have hminj : Function.Injective (Set.inclusion hm) := by
    intro x y h
    exact Subtype.ext (congrArg (fun z : Rm => (z : X)) h)
  obtain ⟨Cp, hCp, _, cp, hcp⟩ :=
    exists_full_collar_of_compact_local_patches (Set.inclusion hp) hpinj hlp
  obtain ⟨Cm, hCm, _, cm, hcm⟩ :=
    exists_full_collar_of_compact_local_patches (Set.inclusion hm) hminj hlm
  exact ⟨{
    neighborhood := W
    positive := Rp
    negative := Rm
    open_neighborhood := hW
    base_subset := hSW
    union_eq := hu
    inter_eq := hi
    positive_closed := hpc
    negative_closed := hmc
    positive_range := Cp
    negative_range := Cm
    positive_open := hCp
    negative_open := hCm
    positive_collar := cp
    negative_collar := cm
    positive_base := fun s => congrArg (fun z : Rp => (z : X)) (hcp s)
    negative_base := fun s => congrArg (fun z : Rm => (z : X)) (hcm s) }⟩

end BrownCollar
