import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Affine.AffineHalfspaceSubcomplex

/-!
# The whole nonnegative and zero loci in one finite pair

One actual common subdivision respects both signs of the affine
scalar. Its retained halfspace and zero faces give a genuine
subcomplex pair with exact entire carriers. See Hudson, pp. 12--14,
and Dehn derivations 022 section 3 and 023 section 4.
-/

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- An actual finite subdivision constructs the full nonnegative
carrier and its entire zero subcomplex for any affine scalar,
including a constant scalar. See Dehn derivation 023, section 4. -/
theorem exists_finite_nonnegative_zero_pair
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (ell : E →ᵃ[ℝ] ℝ) :
    ∃ P Z : SimplicialComplex ℝ E, P.faces.Finite ∧ Z ≤ P ∧
      P.space = K.space ∩ {x | 0 ≤ ell x} ∧
      Z.space = K.space ∩ {x | ell x = 0} := by
  classical
  let cuts : Finset (E →ᵃ[ℝ] ℝ) := {ell, -ell}
  let n := hK.toFinset.sup Finset.card
  have hn (s : Finset E) (hs : s ∈ K.faces) : s.card ≤ n + 1 :=
    (Finset.le_sup (hK.mem_toFinset.mpr hs)).trans (Nat.le_succ n)
  obtain ⟨L, hL, hLK, _, hcuts⟩ :=
    K.exists_subdivision_respectsAffineHyperplanes hK hn cuts
  let P := L.affineHalfspaceSubcomplex {-ell}
  let Z := L.affineHalfspaceSubcomplex cuts
  have hZP : Z ≤ P := by
    intro s hs
    refine ⟨hs.1, ?_⟩
    intro v hv a ha
    rcases Finset.mem_singleton.mp ha with rfl
    exact hs.2 v hv (-ell) (by simp [cuts])
  refine ⟨P, Z, L.affineHalfspaceSubcomplex_finite {-ell} hL, hZP, ?_, ?_⟩
  · rw [L.affineHalfspaceSubcomplex_space {-ell} (by
      intro a ha
      rcases Finset.mem_singleton.mp ha with rfl
      exact hcuts (-ell) (by simp [cuts])), hLK.space_eq]
    ext x
    simp only [mem_inter_iff, mem_ofPred_eq, Finset.mem_singleton, forall_eq]
    change (x ∈ K.space ∧ -ell x ≤ 0) ↔ (x ∈ K.space ∧ 0 ≤ ell x)
    rw [neg_nonpos]
  · rw [L.affineHalfspaceSubcomplex_space cuts hcuts, hLK.space_eq]
    ext x
    simp only [cuts, mem_inter_iff, mem_ofPred_eq, Finset.mem_insert,
      Finset.mem_singleton, forall_eq_or_imp, forall_eq]
    change (x ∈ K.space ∧ ell x ≤ 0 ∧ -ell x ≤ 0) ↔
      (x ∈ K.space ∧ ell x = 0)
    rw [neg_nonpos]
    exact and_congr_right fun _ =>
      ⟨fun h => le_antisymm h.1 h.2, fun h => ⟨h.le, h.ge⟩⟩

end Geometry.SimplicialComplex
