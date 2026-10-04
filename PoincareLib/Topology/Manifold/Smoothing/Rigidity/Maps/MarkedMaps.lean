import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Isotopy.Mathlib.IdentityHomotopy
import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Handles.HamiltonMarkedApproximation

/-!
# The supplied rigidity map on the whole marked domain

The actual identity-relative homotopy gives the complete boundary
homeomorphism. The fixed product-subtype equivalence transports both
the exact boundary-preimage equation and that relative homotopy.
No PL homeomorphism of the whole handle is asserted. See Hamilton
1976, Lemma 3, p. 65, Waldhausen 1968, pp. 77--78, and M76
inputs/Rigidity/derivations/001_source_and_marked_maps.md.
-/

set_option autoImplicit false

open Set

namespace PoincareMT.M76

variable (ι κ : Type*) [Fintype ι] [Fintype κ]
  (L : Submodule ℤ (κ → ℝ))

local notation "H" => LatticeHandle ι κ L
local notation "R" => latticeHandleDomain ι κ L
local notation "B" => latticeHandleBoundary ι κ L
local notation "BR" =>
  (Subtype.val : R → LatticeHandleAmbient ι κ L) ⁻¹' frontier R

omit [Fintype κ] in
/-- The boundary restriction of the supplied map is the identity
homeomorphism with every original value retained. This is the
boundary-injectivity input used before Waldhausen's exceptional
case analysis on p. 78. See rigidity derivation 001, stage 1. -/
theorem exists_hamilton_boundary_homeomorph
    (phi : C(H, H)) (F : (ContinuousMap.id H).HomotopyRel phi B) :
    ∃ b : B ≃ₜ B, ∀ x : B, (b x : H) = phi x := by
  refine ⟨Homeomorph.refl B, ?_⟩
  intro x
  exact F.fst_eq_snd x.property

omit [Fintype κ] in
/-- The exact boundary-preimage equation is preserved by the frozen
product-subtype comparison. Both sides use the complete original
frontier. See Hamilton p. 65 and rigidity derivation 001, stage 3. -/
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

/-- The supplied identity-relative homotopy transports to the
actual ambient-domain subtype, fixing its entire intrinsic
boundary at every time. See rigidity derivation 001, stage 3. -/
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

end PoincareMT.M76
