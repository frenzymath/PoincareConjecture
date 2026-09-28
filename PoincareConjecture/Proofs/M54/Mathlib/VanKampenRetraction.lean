import PoincareConjecture.Proofs.M54.Mathlib.VanKampenLocal











set_option autoImplicit false

open Set
open scoped unitInterval

namespace VanKampen

variable {X : Type*} [TopologicalSpace X] (U V : Set X)



def inclusion : C(U, X) := ⟨Subtype.val, continuous_subtype_val⟩



theorem cover_open (hU : IsOpen U) (hV : IsOpen V) : ∀ i, IsOpen (cover U V i) := by
  intro i
  cases i
  · exact hU
  · exact hV

omit [TopologicalSpace X] in


theorem cover_covers (hcover : U ∪ V = univ) : univ ⊆ ⋃ i, cover U V i := by
  intro x _
  have hx : x ∈ U ∪ V := hcover.symm ▸ mem_univ x
  rcases hx with hx | hx
  · exact mem_iUnion.mpr ⟨false, hx⟩
  · exact mem_iUnion.mpr ⟨true, hx⟩

variable (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    (hUV : IsSimplyConnected (U ∩ V)) (b : U) (hb : b.1 ∈ V)



noncomputable def preliminaryRetraction : FundamentalGroup X b.1 →* FundamentalGroup U b :=
  ((localTransport U V hUV b hb).global (cover_open U V hU hV)
    (cover_covers U V hcover)).toMonoidHom b.1



noncomputable def basepointLoop : FundamentalGroup U b :=
  overlapTails U V hUV b hb b (Joined.refl b)

set_option backward.isDefEq.respectTransparency false in


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



noncomputable def retraction : FundamentalGroup X b.1 →* FundamentalGroup U b :=
  (MulAut.conj (G := FundamentalGroup U b) (basepointLoop U V hUV b hb)⁻¹).symm.toMonoidHom.comp
      (preliminaryRetraction U V hU hV hcover hUV b hb)



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


theorem inclusion_injective : Function.Injective (FundamentalGroup.map (inclusion U) b) := by
  have h : Function.LeftInverse (retraction U V hU hV hcover hUV b hb)
      (FundamentalGroup.map (inclusion U) b) :=
    fun q => DFunLike.congr_fun (retraction_comp_inclusion U V hU hV hcover hUV b hb) q
  exact h.injective

end VanKampen
