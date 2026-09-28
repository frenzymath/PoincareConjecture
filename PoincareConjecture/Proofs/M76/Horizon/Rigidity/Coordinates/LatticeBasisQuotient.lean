import PoincareConjecture.Proofs.M76.Triangulation.HamiltonLatticeHandleModel

set_option autoImplicit false

open Set Module

namespace PoincareConjecture.M76

theorem exists_lattice_quotient_homeomorph
    {κ κ' : Type*} [Fintype κ] [Fintype κ']
    (L : Submodule ℤ (κ → ℝ)) (L' : Submodule ℤ (κ' → ℝ))
    (A : (κ → ℝ) ≃L[ℝ] (κ' → ℝ))
    (hA : L.map (A.toLinearEquiv.restrictScalars ℤ).toLinearMap = L') :
    ∃ q : ((κ → ℝ) ⧸ L.toAddSubgroup) ≃ₜ ((κ' → ℝ) ⧸ L'.toAddSubgroup),
      ∀ x : κ → ℝ, q (QuotientAddGroup.mk x) = QuotientAddGroup.mk (A x) := by
  let e := Submodule.Quotient.equiv L L' (A.toLinearEquiv.restrictScalars ℤ) hA
  refine ⟨{ toEquiv := e.toEquiv, continuous_toFun := ?_, continuous_invFun := ?_ },
    fun _ => rfl⟩
  · apply QuotientAddGroup.isOpenQuotientMap_mk.continuous_comp_iff.mp
    change Continuous (fun x : κ → ℝ =>
      (QuotientAddGroup.mk (A x) : (κ' → ℝ) ⧸ L'.toAddSubgroup))
    exact QuotientAddGroup.continuous_mk.comp A.continuous
  · apply QuotientAddGroup.isOpenQuotientMap_mk.continuous_comp_iff.mp
    change Continuous (fun x : κ' → ℝ =>
      (QuotientAddGroup.mk (A.symm x) : (κ → ℝ) ⧸ L.toAddSubgroup))
    exact QuotientAddGroup.continuous_mk.comp A.symm.continuous

theorem exists_lattice_basis_quotient_homeomorph
    {κ κ' : Type*} [Fintype κ] [Fintype κ'] (σ : κ ≃ κ')
    (L : Submodule ℤ (κ → ℝ)) (L' : Submodule ℤ (κ' → ℝ))
    [DiscreteTopology L] [IsZLattice ℝ L]
    [DiscreteTopology L'] [IsZLattice ℝ L'] :
    ∃ A : (κ → ℝ) ≃L[ℝ] (κ' → ℝ),
      L.map (A.toLinearEquiv.restrictScalars ℤ).toLinearMap = L' ∧
      ∃ q : ((κ → ℝ) ⧸ L.toAddSubgroup) ≃ₜ ((κ' → ℝ) ⧸ L'.toAddSubgroup),
        ∀ x : κ → ℝ, q (QuotientAddGroup.mk x) = QuotientAddGroup.mk (A x) := by
  let b := (IsZLattice.basis L).ofZLatticeBasis ℝ
  let b' := (IsZLattice.basis L').ofZLatticeBasis ℝ
  let A := (b.equiv b' σ).toContinuousLinearEquiv
  have hA : L.map (A.toLinearEquiv.restrictScalars ℤ).toLinearMap = L' := by
    rw [← (IsZLattice.basis L).ofZLatticeBasis_span ℝ]
    change (Submodule.span ℤ (range b)).map
      ((b.equiv b' σ).restrictScalars ℤ).toLinearMap = L'
    rw [ZSpan.map, Basis.map_equiv]
    simp only [Basis.coe_reindex, Equiv.symm_symm]
    rw [σ.surjective.range_comp]
    exact (IsZLattice.basis L').ofZLatticeBasis_span ℝ
  exact ⟨A, hA, exists_lattice_quotient_homeomorph L L' A hA⟩

end PoincareConjecture.M76
