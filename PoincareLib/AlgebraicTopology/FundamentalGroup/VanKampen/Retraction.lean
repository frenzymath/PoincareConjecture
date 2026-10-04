import PoincareLib.AlgebraicTopology.FundamentalGroup.VanKampen.Local

/-! Adapted from Mapher `PoincareMT/Proofs/M54/Mathlib/VanKampenRetraction.lean` at
`0c5d5c4e1ecbc12703b1994e226df1b15d2e8d39`; see `references/ricci-flow/mapher/group-effects.md`. -/

/-!
# The retraction form of van Kampen

If two open sets cover a space and their overlap is simply connected,
the fundamental group of the first set is a retract of the ambient group,
at any basepoint in the overlap. Neither open set is assumed connected.
This is the projection case of Hatcher Theorem 1.20 (pp. 43-46), used
for Morgan--Tian Proposition 15.3 (pp. 357-358).
-/

set_option autoImplicit false

open Set
open scoped unitInterval

namespace VanKampen

variable {X : Type*} [TopologicalSpace X] (U V : Set X)

/-- The continuous inclusion of a subspace, used in Hatcher
Theorem 1.20, pp. 43-46. -/
def inclusion : C(U, X) := ⟨Subtype.val, continuous_subtype_val⟩

/-- The Boolean two-set cover is open (Hatcher Theorem 1.20,
pp. 43-46). -/
theorem cover_open (hU : IsOpen U) (hV : IsOpen V) : ∀ i, IsOpen (cover U V i) := by
  intro i
  cases i
  · exact hU
  · exact hV

omit [TopologicalSpace X] in
/-- The Boolean two-set cover covers the ambient space
(Hatcher Theorem 1.20, pp. 43-46). -/
theorem cover_covers (hcover : U ∪ V = univ) : univ ⊆ ⋃ i, cover U V i := by
  intro x _
  have hx : x ∈ U ∪ V := hcover.symm ▸ mem_univ x
  rcases hx with hx | hx
  · exact mem_iUnion.mpr ⟨false, hx⟩
  · exact mem_iUnion.mpr ⟨true, hx⟩

variable (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    (hUV : IsSimplyConnected (U ∩ V)) (b : U) (hb : b.1 ∈ V)

/-- The global van Kampen homomorphism before removing the conjugation
from the auxiliary basepoint path (Hatcher Theorem 1.20, pp. 43-46). -/
noncomputable def preliminaryRetraction : FundamentalGroup X b.1 →* FundamentalGroup U b :=
  ((localTransport U V hUV b hb).global (cover_open U V hU hV)
    (cover_covers U V hcover)).toMonoidHom b.1

/-- The auxiliary loop at the chosen basepoint in Hatcher's path system
(Theorem 1.20, pp. 43-46). -/
noncomputable def basepointLoop : FundamentalGroup U b :=
  overlapTails U V hUV b hb b (Joined.refl b)

set_option backward.isDefEq.respectTransparency false in
/-- Restriction of the global homomorphism to the first set is conjugation
by the chosen basepoint loop (Hatcher Theorem 1.20, pp. 43-46). -/
theorem preliminaryRetraction_comp_inclusion :
    (preliminaryRetraction U V hU hV hcover hUV b hb).comp
        (FundamentalGroup.map (inclusion U) b) =
      (MulAut.conj (G := FundamentalGroup U b)
        (basepointLoop U V hUV b hb)⁻¹).toMonoidHom := by
  ext q
  induction q using Path.Homotopic.Quotient.ind with
  | mk p =>
    let L := localTransport U V hUV b hb
    change MulOpposite.unop (L.extend (cover_open U V hU hV) (cover_covers U V hcover)
      (p.map (inclusion U).continuous).toContinuousMap) = _
    rw [L.extend_eq_local (cover_open U V hU hV) (cover_covers U V hcover) _ false
      (fun t => (p t).2)]
    change MulOpposite.unop (localValue U V hUV b hb
      (p.map (inclusion U).continuous).toContinuousMap) = _
    rw [localValue_first U V hUV b hb _ (fun t => (p t).2)]
    have hp : (p.map (inclusion U).continuous).toContinuousMap.restrictRange U
        (fun t => (p t).2) = p.toContinuousMap := by ext t; rfl
    rw [hp, Path.Homotopic.Quotient.basedContinuousTransport_path,
      Path.Homotopic.Quotient.basedTransport_of_joined b _ _ (Joined.refl b) (Joined.refl b)]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rfl

/-- The van Kampen projection, corrected to be a literal left inverse of
the first inclusion (Hatcher Theorem 1.20, pp. 43-46). -/
noncomputable def retraction : FundamentalGroup X b.1 →* FundamentalGroup U b :=
  (MulAut.conj (G := FundamentalGroup U b) (basepointLoop U V hUV b hb)⁻¹).symm.toMonoidHom.comp
      (preliminaryRetraction U V hU hV hcover hUV b hb)

/-- The first-set inclusion has the van Kampen projection as a left
inverse (Hatcher Theorem 1.20, pp. 43-46). -/
theorem retraction_comp_inclusion :
    (retraction U V hU hV hcover hUV b hb).comp
      (FundamentalGroup.map (inclusion U) b) = MonoidHom.id (FundamentalGroup U b) := by
  ext q
  have h := DFunLike.congr_fun
    (preliminaryRetraction_comp_inclusion U V hU hV hcover hUV b hb) q
  change (MulAut.conj (G := FundamentalGroup U b) (basepointLoop U V hUV b hb)⁻¹).symm
    (preliminaryRetraction U V hU hV hcover hUV b hb (FundamentalGroup.map (inclusion U) b q)) = q
  rw [show preliminaryRetraction U V hU hV hcover hUV b hb
      (FundamentalGroup.map (inclusion U) b q) = _ from h]
  exact MulEquiv.symm_apply_apply _ q

include hU hV hcover hUV hb in
/-- A simply connected overlap makes the first-set fundamental-group
inclusion injective (Hatcher Theorem 1.20, pp. 43-46). -/
theorem inclusion_injective : Function.Injective (FundamentalGroup.map (inclusion U) b) := by
  have h : Function.LeftInverse (retraction U V hU hV hcover hUV b hb)
      (FundamentalGroup.map (inclusion U) b) :=
    fun q => DFunLike.congr_fun (retraction_comp_inclusion U V hU hV hcover hUV b hb) q
  exact h.injective

end VanKampen
