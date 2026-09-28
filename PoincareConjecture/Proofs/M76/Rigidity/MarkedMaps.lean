import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.IdentityHomotopy
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonMarkedApproximation

set_option autoImplicit false

open Set

namespace PoincareConjecture.M76

variable (ι κ : Type*) [Fintype ι] [Fintype κ]
  (L : Submodule ℤ (κ → ℝ))

local notation "H" => LatticeHandle ι κ L
local notation "R" => latticeHandleDomain ι κ L
local notation "B" => latticeHandleBoundary ι κ L
local notation "BR" =>
  (Subtype.val : R → LatticeHandleAmbient ι κ L) ⁻¹' frontier R

omit [Fintype κ] in

theorem exists_hamilton_boundary_homeomorph
    (phi : C(H, H)) (F : (ContinuousMap.id H).HomotopyRel phi B) :
    ∃ b : B ≃ₜ B, ∀ x : B, (b x : H) = phi x := by
  refine ⟨Homeomorph.refl B, ?_⟩
  intro x
  exact F.fst_eq_snd x.property

omit [Fintype κ] in

theorem latticeHandleMapInDomain_preimage_boundary
    (phi : C(H, H)) (hproper : phi ⁻¹' B = B) :
    latticeHandleMapInDomain ι κ L phi ⁻¹' BR = BR := by
  let q := latticeHandleDomainEquiv ι κ L
  have hb (x : R) : q x ∈ B ↔ x ∈ BR :=
    Set.ext_iff.mp (latticeHandleDomainEquiv_preimage_boundary ι κ L) x
  ext x
  change q.symm (phi (q x)) ∈ BR ↔ x ∈ BR
  rw [← hb, q.apply_symm_apply, ← hb]
  exact Set.ext_iff.mp hproper (q x)

def latticeHandleMapInDomain_homotopyRel
    (phi : C(H, H)) (F : (ContinuousMap.id H).HomotopyRel phi B) :
    (ContinuousMap.id R).HomotopyRel
      (latticeHandleMapInDomain ι κ L phi) BR := by
  let q := latticeHandleDomainEquiv ι κ L
  refine {
    toFun := fun z => q.symm (F (z.1, q z.2))
    continuous_toFun := q.symm.continuous.comp
      (F.continuous.comp (continuous_fst.prodMk (q.continuous.comp continuous_snd)))
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_
  }
  · intro x
    rw [F.apply_zero]
    exact q.symm_apply_apply x
  · intro x
    rw [F.apply_one]
    rfl
  · intro t x hx
    have hxB : q x ∈ B :=
      (Set.ext_iff.mp (latticeHandleDomainEquiv_preimage_boundary ι κ L) x).mpr hx
    change q.symm (F (t, q x)) = x
    rw [F.eq_fst t hxB]
    exact q.symm_apply_apply x

end PoincareConjecture.M76
