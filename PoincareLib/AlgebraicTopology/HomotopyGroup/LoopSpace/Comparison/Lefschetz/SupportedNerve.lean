import PoincareLib.AlgebraicTopology.HomotopyGroup.LoopSpace.Comparison.Lefschetz.SingularLift
import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits

/-!
# Induced subcomplexes of a finite nerve

Keep the ambient partial order fixed and select the simplices all of whose
vertices lie in a chosen finite subset. Removing a minimal vertex and taking
its upper cone gives a literal subcomplex union, with the expected
intersection. The same identities hold in the lifted simplicial model.
Source: Hatcher, Theorem 2.27, printed pp. 128-130.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory
open scoped Simplicial

universe u

namespace PoincareMT.Proofs.M59

variable {J : Type u} [PartialOrder J]

/-- The nerve subcomplex on the selected vertices.
Source: Hatcher, Theorem 2.27, pp. 128-130. -/
def supportedNerve (s : Finset J) : (nerve J).Subcomplex where
  obj _ := {z | ∀ i, z.obj i ∈ s}
  map f _ hz i := hz (f.unop i)

/-- Inclusion of vertex sets gives the literal inclusion of their
induced nerve subcomplexes. Source: Hatcher, Theorem 2.27. -/
theorem supportedNerve_mono {s t : Finset J} (h : s ⊆ t) :
    supportedNerve s ≤ supportedNerve t :=
  fun _ _ hz i => h (hz i)

open scoped Classical in
/-- Intersections of vertex sets are literal subcomplex intersections.
Source: Hatcher, Theorem 2.27, pp. 128-130. -/
theorem supportedNerve_inter (s t : Finset J) :
    supportedNerve (s ∩ t) = supportedNerve s ⊓ supportedNerve t := by
  ext n z
  change (∀ i, z.obj i ∈ s ∩ t) ↔ (∀ i, z.obj i ∈ s) ∧ ∀ i, z.obj i ∈ t
  simp only [Finset.mem_inter, forall_and]

/-- The full vertex set gives the actual entire nerve.
Source: Hatcher, Theorem 2.27, pp. 128-130. -/
theorem supportedNerve_univ [Fintype J] :
    supportedNerve (Finset.univ : Finset J) = ⊤ := by
  ext n z
  change (∀ i, z.obj i ∈ Finset.univ) ↔ True
  simp only [Finset.mem_univ, implies_true]

open scoped Classical in
/-- Every chain either avoids a minimal vertex or lies in its upper
cone. Source: the induction in Hatcher, Theorem 2.27, pp. 128-130. -/
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
/-- The overlap of the deletion and upper cone is the strict upper
link. Source: Hatcher, Theorem 2.27, pp. 128-130. -/
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

/-- The induced subcomplex in the literal lifted model retains its
actual singular lifts. Source: Hatcher, Theorem 2.27, pp. 128-130. -/
def supportedSingularLift (s : Finset J) : (singularLiftSSet p (nerve J) χ).Subcomplex :=
  (supportedNerve s).preimage (singularLiftBase p (nerve J) χ)

open scoped Classical in
/-- The minimal-vertex union remains literal after lifting.
Source: Hatcher, Theorem 2.27, pp. 128-130. -/
theorem supportedSingularLift_minimal_union (s : Finset J) (v : J)
    (hminimal : ∀ j ∈ s, j ≤ v → j = v) :
    supportedSingularLift p χ (s.erase v) ⊔
        supportedSingularLift p χ (s.filter (v ≤ ·)) = supportedSingularLift p χ s := by
  have h := congrArg (fun A : (nerve J).Subcomplex =>
    A.preimage (singularLiftBase p (nerve J) χ)) (supportedNerve_minimal_union s v hminimal)
  exact h

end PoincareMT.Proofs.M59
