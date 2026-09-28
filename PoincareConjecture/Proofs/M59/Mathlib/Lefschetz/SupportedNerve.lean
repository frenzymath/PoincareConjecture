import PoincareConjecture.Proofs.M59.Mathlib.Lefschetz.SingularLift
import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits

set_option autoImplicit false

noncomputable section

open CategoryTheory
open scoped Simplicial

universe u

namespace PoincareConjecture.Proofs.M59

variable {J : Type u} [PartialOrder J]

def supportedNerve (s : Finset J) : (nerve J).Subcomplex where
  obj _ := {z | ∀ i, z.obj i ∈ s}
  map f _ hz i := hz (f.unop i)

theorem supportedNerve_mono {s t : Finset J} (h : s ⊆ t) :
    supportedNerve s ≤ supportedNerve t :=
  fun _ _ hz i => h (hz i)

open scoped Classical in

theorem supportedNerve_inter (s t : Finset J) :
    supportedNerve (s ∩ t) = supportedNerve s ⊓ supportedNerve t := by
  ext n z
  change (∀ i, z.obj i ∈ s ∩ t) ↔ (∀ i, z.obj i ∈ s) ∧ ∀ i, z.obj i ∈ t
  simp only [Finset.mem_inter, forall_and]

theorem supportedNerve_univ [Fintype J] :
    supportedNerve (Finset.univ : Finset J) = ⊤ := by
  ext n z
  change (∀ i, z.obj i ∈ Finset.univ) ↔ True
  simp only [Finset.mem_univ, implies_true]

open scoped Classical in

theorem supportedNerve_minimal_union (s : Finset J) (v : J)
    (hminimal : ∀ j ∈ s, j ≤ v → j = v) :
    supportedNerve (s.erase v) ⊔ supportedNerve (s.filter (v ≤ ·)) =
      supportedNerve s := by
  classical
  apply le_antisymm
  · exact sup_le (supportedNerve_mono (Finset.erase_subset v s))
      (supportedNerve_mono (Finset.filter_subset _ _))
  · intro n z hz
    change (∀ i, z.obj i ∈ s.erase v) ∨ ∀ i, z.obj i ∈ s.filter (v ≤ ·)
    by_cases h : ∀ i, z.obj i ≠ v
    · exact Or.inl (fun i => Finset.mem_erase.mpr ⟨h i, hz i⟩)
    · push Not at h
      obtain ⟨j, hj⟩ := h
      refine Or.inr (fun i => Finset.mem_filter.mpr ⟨hz i, ?_⟩)
      rcases le_total j i with hji | hij
      · simpa only [hj] using z.monotone hji
      · have heq := hminimal (z.obj i) (hz i) (by simpa only [hj] using z.monotone hij)
        exact heq.ge

open scoped Classical in

theorem supportedNerve_minimal_inter (s : Finset J) (v : J) :
    supportedNerve (s.erase v) ⊓ supportedNerve (s.filter (v ≤ ·)) =
      supportedNerve (s.filter (v < ·)) := by
  rw [← supportedNerve_inter]
  congr 1
  ext j
  simp only [Finset.mem_inter, Finset.mem_erase, Finset.mem_filter]
  constructor
  · rintro ⟨⟨hne, hs⟩, _, hle⟩
    exact ⟨hs, lt_of_le_of_ne hle hne.symm⟩
  · rintro ⟨hs, hlt⟩
    exact ⟨⟨ne_of_gt hlt, hs⟩, hs, hlt.le⟩

variable {E X : Type u} [TopologicalSpace E] [TopologicalSpace X]
  (p : C(E, X)) (χ : nerve J ⟶ TopCat.toSSet.obj (TopCat.of X))

def supportedSingularLift (s : Finset J) : (singularLiftSSet p (nerve J) χ).Subcomplex :=
  (supportedNerve s).preimage (singularLiftBase p (nerve J) χ)

open scoped Classical in

theorem supportedSingularLift_minimal_union (s : Finset J) (v : J)
    (hminimal : ∀ j ∈ s, j ≤ v → j = v) :
    supportedSingularLift p χ (s.erase v) ⊔
        supportedSingularLift p χ (s.filter (v ≤ ·)) = supportedSingularLift p χ s := by
  have h := congrArg (fun A : (nerve J).Subcomplex =>
    A.preimage (singularLiftBase p (nerve J) χ)) (supportedNerve_minimal_union s v hminimal)
  exact h

end PoincareConjecture.Proofs.M59
