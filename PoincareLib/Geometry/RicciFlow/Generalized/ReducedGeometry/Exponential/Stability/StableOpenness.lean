import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Exponential.Construction.ExponentialSliceInverse

/-!
# Openness of the full actual stable carrier

Morgan-Tian Definition 6.25 and Proposition 6.28, pp. 116-117.
The given unique-minimizer neighborhood is retained. The actual
slice inverse theorem gives an open smaller source with invertible
differential throughout, so every point in that source remains stable.
No existence of a stable vector is inferred from survival.
-/

set_option autoImplicit false

open Set Filter
open scoped Topology

universe u

namespace PoincareMT.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ : ℝ} {x : G.Point}

/-- The full frozen stable predicate is open in the initial vector:
invertibility persists on the local inverse source and the prescribed
unique-minimizer neighborhood is retained, Proposition 6.28, p. 117. -/
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

/-- Each stable vector has the actual uniquely minimizing branch
required by its defining neighborhood, Definition 6.25, p. 116. -/
theorem stableInitialVector_unique_branch (E : M14ExponentialFamily G T x)
    {Z : G.Horizontal x} (hZ : M14StableInitialVector G T τ x E Z) :
    M14UniqueMinimizingBranch G T τ x E Z := by
  obtain ⟨_, _, U, _, hZU, hmin⟩ := hZ
  exact hmin Z hZU

/-- A stable vector has an open neighborhood inside the full stable
carrier on which every actual branch uniquely minimizes,
Definition 6.25 and Proposition 6.28, pp. 116-117. -/
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

end PoincareMT.M14
