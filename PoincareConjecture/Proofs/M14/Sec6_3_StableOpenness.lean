import PoincareConjecture.Proofs.M14.Sec6_3_ExponentialSliceInverse

set_option autoImplicit false

open Set Filter
open scoped Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ : ℝ} {x : G.Point}

theorem isOpen_stableInitialVectors (E : M14ExponentialFamily G T x) (hτ : 0 ≤ τ) :
    IsOpen {Z | M14StableInitialVector G T τ x E Z} := by
  rw [isOpen_iff_mem_nhds]
  intro Z hZ
  obtain ⟨hZD, hbij, U, hU, hZU, hmin⟩ := hZ
  let q₀ : (G.slices (T - τ)).Point :=
    ⟨E.gamma Z (Real.sqrt τ), by simpa only [Real.sq_sqrt hτ] using E.clock Z _ hZD⟩
  let S := U ∩ {W | (W, Real.sqrt τ) ∈ E.domain}
  have hS : IsOpen S := hU.inter (exponentialFamily_domain_slice_isOpen E (Real.sqrt τ))
  have hSD : ∀ W ∈ S, (W, Real.sqrt τ) ∈ E.domain := fun _ hW => hW.2
  obtain ⟨e, hZe, heS, _, _, hbij_e⟩ :=
    exists_exponentialSlice_local_inverse E hτ q₀ hS hSD ⟨hZU, hZD⟩ hbij
  apply mem_of_superset (e.open_source.mem_nhds hZe)
  intro W hW
  obtain ⟨hWD, hbijW⟩ := hbij_e W hW
  exact ⟨hWD, hbijW, U, hU, (heS hW).1, hmin⟩

theorem stableInitialVector_unique_branch (E : M14ExponentialFamily G T x)
    {Z : G.Horizontal x} (hZ : M14StableInitialVector G T τ x E Z) :
    M14UniqueMinimizingBranch G T τ x E Z := by
  obtain ⟨_, _, U, _, hZU, hmin⟩ := hZ
  exact hmin Z hZU

theorem stableInitialVector_open_neighborhood (E : M14ExponentialFamily G T x)
    (hτ : 0 ≤ τ) {Z : G.Horizontal x} (hZ : M14StableInitialVector G T τ x E Z) :
    ∃ U : Set (G.Horizontal x), IsOpen U ∧ Z ∈ U ∧
      U ⊆ {W | M14StableInitialVector G T τ x E W} ∧
      ∀ W ∈ U, M14UniqueMinimizingBranch G T τ x E W := by
  have hstable := hZ
  obtain ⟨_, _, U, hU, hZU, hmin⟩ := hZ
  exact ⟨U ∩ {W | M14StableInitialVector G T τ x E W},
    hU.inter (isOpen_stableInitialVectors E hτ), ⟨hZU, hstable⟩,
    inter_subset_right, fun W hW => hmin W hW.1⟩

end PoincareConjecture.M14
