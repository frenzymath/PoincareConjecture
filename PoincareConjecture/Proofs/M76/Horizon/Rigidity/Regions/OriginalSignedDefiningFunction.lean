import PoincareConjecture.Proofs.M76.Dehn.OriginalBoundaryDefiningCut
import PoincareConjecture.Proofs.M76.PrimeReduction.PLDomainExterior











set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

variable {X ι : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X}




theorem PLDomain.exists_signed_defining_function (he : PLDomain e R)
    (hR : IsCompact R) (hExt : IsCompact (interior R)ᶜ) :
    ∃ r : X → ℝ, Continuous r ∧
      (∀ i, LocallyPiecewiseAffineOn (r ∘ (e i).symm) (e i).target) ∧
      ∀ x, (x ∈ R ↔ 0 ≤ r x) ∧ (x ∈ frontier R ↔ r x = 0) ∧
        (x ∈ interior R ↔ 0 < r x) ∧ (x ∉ R ↔ r x < 0) := by
  obtain ⟨a, U, _, hRU, hac, ha, _, haneg, hazero, hapos⟩ :=
    OpenPartialHomeomorph.exists_PL_defining_cut_near_compact_with_signs
      e he.compatible he.cover hR (Subset.rfl : R ⊆ R) he.halfspace
  obtain ⟨b, V, _, hExtV, hbc, hb, _, hbneg, hbzero, hbpos⟩ :=
    OpenPartialHomeomorph.exists_PL_defining_cut_near_compact_with_signs
      e he.compatible he.cover hExt (Subset.rfl : (interior R)ᶜ ⊆ (interior R)ᶜ)
      he.closed_exterior.halfspace
  let r := fun x => a x - b x
  have hrpos (x : X) (hx : x ∈ interior R) : 0 < r x := by
    have hp := (hapos x (hRU (interior_subset hx))).2.2.mp hx
    have hn := hbneg x (show x ∉ (interior R)ᶜ from fun h => h hx)
    dsimp only [r]
    linarith
  have hrneg (x : X) (hx : x ∉ R) : r x < 0 := by
    have hxExt : x ∈ (interior R)ᶜ := fun h => hx (interior_subset h)
    have hxint : x ∈ interior (interior R)ᶜ := by
      rw [interior_compl, he.closure_interior]
      exact hx
    have hp := (hbpos x (hExtV hxExt)).2.2.mp hxint
    have hn := haneg x hx
    dsimp only [r]
    linarith
  have hrzero (x : X) (hx : x ∈ frontier R) : r x = 0 := by
    have hxExt : x ∈ frontier (interior R)ᶜ := he.frontier_closed_exterior.symm ▸ hx
    simp only [r, hazero x hx, hbzero x hxExt, sub_self]
  refine ⟨r, hac.sub hbc, fun i => ?_, ?_⟩
  · exact ((ha i).add (hb i).neg).congr (fun _ _ => (sub_eq_add_neg _ _).symm)
  · intro x
    by_cases hx : x ∈ R
    · by_cases hi : x ∈ interior R
      · have hp := hrpos x hi
        have hnf : x ∉ frontier R := fun hf =>
          disjoint_left.mp disjoint_interior_frontier hi hf
        exact ⟨iff_of_true hx hp.le, iff_of_false hnf hp.ne',
          iff_of_true hi hp, iff_of_false (not_not.mpr hx) (not_lt_of_ge hp.le)⟩
      · have hf : x ∈ frontier R := (mem_frontier_iff_notMem_interior hx).mpr hi
        rw [hrzero x hf]
        exact ⟨iff_of_true hx le_rfl, iff_of_true hf rfl,
          iff_of_false hi (lt_irrefl _), iff_of_false (not_not.mpr hx) (lt_irrefl _)⟩
    · have hn := hrneg x hx
      have hnf : x ∉ frontier R := fun hf => hx (he.closed.frontier_subset hf)
      have hni : x ∉ interior R := fun hi => hx (interior_subset hi)
      exact ⟨iff_of_false hx (not_le_of_gt hn), iff_of_false hnf hn.ne,
        iff_of_false hni (not_lt_of_ge hn.le), iff_of_true hx hn⟩

end PoincareConjecture.M76
