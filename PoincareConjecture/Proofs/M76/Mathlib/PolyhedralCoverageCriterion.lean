import PoincareConjecture.Proofs.M76.Mathlib.AffineSubspaceAvoidance

set_option autoImplicit false

open Set Module

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem IsClosed.covers_of_interior_off_affineSubspaces {C U : Set E}
    (hC : IsClosed C) (hU : IsOpen U) (hconv : Convex ℝ U)
    (hmeet : (U ∩ interior C).Nonempty)
    {ι : Type*} [Finite ι] (A : ι → AffineSubspace ℝ E)
    (hA : ∀ i, Module.finrank ℝ (A i).direction + 1 < Module.finrank ℝ E)
    (hregular : ∀ x ∈ U, x ∈ C → x ∉ ⋃ i, (A i : Set E) → x ∈ interior C) :
    U ⊆ C := by
  have hproper : ∀ i, A i ≠ ⊤ := by
    intro i he
    have hi := hA i
    rw [he, AffineSubspace.direction_top, finrank_top] at hi
    omega
  have hdense := AffineSubspace.dense_compl_iUnion A hproper
  let S := U \ ⋃ i, (A i : Set E)
  have hconn : IsPreconnected S :=
    (AffineSubspace.isPathConnected_sdiff_iUnion A hA hU hconv
      (hmeet.mono inter_subset_left)).isConnected.isPreconnected
  have hinterior : (S ∩ interior C).Nonempty := by
    obtain ⟨x, hxU, hxA⟩ := hdense.inter_open_nonempty (U ∩ interior C)
      (hU.inter isOpen_interior) hmeet
    exact ⟨x, ⟨hxU.1, hxA⟩, hxU.2⟩
  have hSC : S ⊆ interior C := hconn.subset_of_closure_inter_subset isOpen_interior
    hinterior (fun x hx => hregular x hx.2.1
      ((closure_minimal interior_subset hC) hx.1) hx.2.2)
  have hclosure : U ⊆ closure S := by
    simpa only [S, sdiff_eq_compl_inter, inter_comm] using hdense.open_subset_closure_inter hU
  exact hclosure.trans (closure_minimal (hSC.trans interior_subset) hC)
