import PoincareConjecture.Proofs.M76.Dehn.Mathlib.SimplicialCocycleConnected








set_option autoImplicit false

open Set

namespace PreAbstractSimplicialComplex.ModTwoEdgeCocycle

variable {ι Z : Type*} [Fintype ι] [TopologicalSpace Z]
  {A : PreAbstractSimplicialComplex ι}



theorem exists_lift_of_star_potential (c : A.ModTwoEdgeCocycle)
    (γ : C(Z, A.barycentricSpace)) (a : ι → ZMod 2)
    (ha : ∀ z i j, γ z ∈ A.openVertexStar i → γ z ∈ A.openVertexStar j →
      c.value i j = a i + a j) :
    ∃ q : C(Z, c.bundle.TotalSpace), ∀ z, c.bundle.proj (q z) = γ z := by
  let q : Z → c.bundle.TotalSpace := fun z => ⟨γ z, a (c.bundle.indexAt (γ z))⟩
  have hlocal (i : ι) (z : Z) (hz : γ z ∈ A.openVertexStar i) :
      (c.sheet i (a i)) ⟨γ z, hz⟩ = q z := by
    change (⟨γ z, a i + c.value i (c.bundle.indexAt (γ z))⟩ :
      c.bundle.TotalSpace) = ⟨γ z, a (c.bundle.indexAt (γ z))⟩
    rw [ha z i _ hz (c.bundle.mem_baseSet_at (γ z)), ← add_assoc,
      CharTwo.add_self_eq_zero, zero_add]
  have hq : Continuous q := by
    apply continuous_iff_continuousAt.mpr
    intro z
    obtain ⟨i, hi⟩ := A.exists_mem_openVertexStar (γ z)
    have hcont : ContinuousOn q (γ ⁻¹' A.openVertexStar i) := by
      apply continuousOn_iff_continuous_domRestrict.mpr
      let g : C(γ ⁻¹' A.openVertexStar i, A.openVertexStar i) :=
        ⟨fun x => ⟨γ x, x.property⟩,
          (γ.continuous.comp continuous_subtype_val).subtype_mk _⟩
      exact ((c.sheet i (a i)).continuous.comp g.continuous).congr
        (fun x => hlocal i x x.property)
    exact hcont.continuousAt
      (((A.isOpen_openVertexStar i).preimage γ.continuous).mem_nhds hi)
  exact ⟨⟨q, hq⟩, fun _ => rfl⟩

end PreAbstractSimplicialComplex.ModTwoEdgeCocycle
