import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.OriginalProtectedIndexTwoCut
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Handles.ProtectedAtlasFromCut










set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem hasHamiltonProtectedIrreducibleReplacement_of_card_eq_two
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    (L : Submodule ℤ (κ → ℝ))
    (e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3)
    (hi : Fintype.card ι = 2) :
    HasHamiltonProtectedIrreducibleReplacement ι κ L e := by
  classical
  intro hdim hindex hdis hlattice he D hD
  let := hdis
  let := hlattice
  obtain ⟨bD⟩ := hD
  obtain ⟨t₀,f,K,H,g,hf,hfi,hK,hH,hg,hgPL,ν,hν,c,hno,hmax,_⟩ :=
    exists_maximal_lattice_handle_sphere_cut L hdim hindex he bD
  let := hν
  have hgi : InjOn (fun z => (g z : LatticeHandleAmbient ι κ L)) K.space := by
    intro x hx y hy hxy
    have heq : H.symm ⟨x,hx⟩ = H.symm ⟨y,hy⟩ :=
      Subtype.ext ((hg ⟨x,hx⟩).symm.trans (hxy.trans (hg ⟨y,hy⟩)))
    exact congrArg Subtype.val (H.symm.injective heq)
  have hreal : ∀ x ∈ latticeHandleDomain ι κ L,
      f x ∈ K.space ∧ (g (f x) : LatticeHandleAmbient ι κ L) = x := by
    intro x hx
    have hh := hH ⟨x,hx⟩
    refine ⟨hh ▸ (H ⟨x,hx⟩).property,?_⟩
    rw [←hh,hg]
    exact congrArg Subtype.val (H.symm_apply_apply ⟨x,hx⟩)
  obtain ⟨d,hnoD,havoid⟩ :=
    bD.exists_index_two_disjoint_noL3_cut he hdim hi c hno K
      (fun z => (g z : LatticeHandleAmbient ι κ L)) hf hgPL hgi hreal
  exact exists_protected_irreducible_lattice_atlas_from_cut L hdim hindex he bD
    (by omega) d K (fun z => (g z : LatticeHandleAmbient ι κ L)) hgPL hgi hreal
    hnoD hmax havoid

end PoincareConjecture.M76

