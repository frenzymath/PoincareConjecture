import PoincareLib.Topology.Manifold.Smoothing.Dehn.Affine.Mathlib.AffineParameterAvoidance

/-!
# Actual parameter avoidance inside an affine subspace

Pull the forbidden affine subspaces back along the actual translation
of the direction space. This keeps the chosen direction tangent to
the given affine subspace, including its zero-dimensional case.
See Hudson1969, Lemma4.5, pp.96--97, and Dehn030, section2.
-/

set_option autoImplicit false

open Set

namespace AffineSubspace

/-- A finite family that does not contain the actual affine subspace
admits one direction in its direction space and arbitrarily small
positive parameters avoiding every forbidden member. The pullback
family and all parameters are constructed. See Dehn030, section2. -/
theorem exists_relative_direction_parameters
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Finite ι]
    (A : AffineSubspace ℝ E) {v : E} (hv : v ∈ A)
    (B : ι → AffineSubspace ℝ E) (hB : ∀ i, ¬A ≤ B i) :
    ∃ u : A.direction, ∀ {ε : ℝ}, 0 < ε →
      ∃ a : ℝ, a ∈ Ioo 0 ε ∧ ∀ i, v + a • (u : E) ∉ B i := by
  let av : A.direction →ᵃ[ℝ] E :=
    AffineMap.const ℝ A.direction v + A.direction.subtype.toAffineMap
  let C : ι → AffineSubspace ℝ A.direction := fun i => (B i).comap av
  have hC : ∀ i, C i ≠ ⊤ := by
    intro i hi
    apply hB i
    intro x hx
    let q : A.direction := ⟨x - v, vsub_mem_direction hx hv⟩
    have hq : q ∈ C i := by
      rw [hi]
      trivial
    have hmem : av q ∈ B i := (mem_comap.mp hq)
    have heq : av q = x := by
      change v + (x - v) = x
      abel
    exact heq ▸ hmem
  obtain ⟨u, hu⟩ := exists_avoiding_directions C hC
  refine ⟨u, ?_⟩
  intro ε hε
  obtain ⟨a, ha, havoid⟩ := exists_pos_small_line_avoiding C (0 : A.direction) u hu hε
  refine ⟨a, ha, ?_⟩
  intro i hi
  apply havoid i
  change av ((0 : A.direction) + a • u) ∈ B i
  change v + (((0 : A.direction) + a • u : A.direction) : E) ∈ B i
  simpa only [zero_add, Submodule.coe_smul] using hi

end AffineSubspace
