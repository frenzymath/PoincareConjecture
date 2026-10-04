import PoincareLib.Geometry.RicciFlow.Surgery.Ancestry.GroupEffects

/-! Adapted from Mapher `PoincareMT/Proofs/M54/BasepointTransport.lean` at
`0c5d5c4e1ecbc12703b1994e226df1b15d2e8d39`; see `references/ricci-flow/mapher/group-effects.md`. -/

/-!
# Transport and composition of the surgery group factors

The retractions obtained from Morgan--Tian Proposition 15.3 (pp. 357-358)
compose along a reconstruction and transport across basepoint-change group
isomorphisms. These are algebraic operations on the frozen certificate.
-/

set_option autoImplicit false

universe u

namespace PoincareMT.RepairedGroupFactorData

variable {G H K : Type u} [Group G] [Group H] [Group K]

/-- Package a homomorphism with a right inverse as the factor certificate
used in Proposition 15.3 (pp. 357-358). -/
def ofRetraction (r : G →* H) (j : H →* G)
    (h : r.comp j = MonoidHom.id H) : RepairedGroupFactorData G H where
  factor_map := r
  kernel_subgroup := r.ker
  kernel_eq := rfl
  factor_surjective y := ⟨j y, DFunLike.congr_fun h y⟩
  survivor_injection := j
  injection_injective := by
    intro a b hab
    have ha := DFunLike.congr_fun h a
    have hb := DFunLike.congr_fun h b
    exact ha.symm.trans ((congrArg r hab).trans hb)
  factor_retraction := h

/-- An isomorphism supplies a factor certificate, in particular for
basepoint transport in Proposition 15.3 (pp. 357-358). -/
def ofMulEquiv (e : G ≃* H) : RepairedGroupFactorData G H :=
  ofRetraction e.toMonoidHom e.symm.toMonoidHom (by ext x; exact e.apply_symm_apply x)

/-- Compose survivor retractions through successive connected sums in
Proposition 15.3 (pp. 357-358). -/
def trans (D : RepairedGroupFactorData G H) (E : RepairedGroupFactorData H K) :
    RepairedGroupFactorData G K :=
  ofRetraction (E.factor_map.comp D.factor_map)
    (D.survivor_injection.comp E.survivor_injection) (by
      ext x
      change E.factor_map (D.factor_map (D.survivor_injection
        (E.survivor_injection x))) = x
      rw [show D.factor_map (D.survivor_injection (E.survivor_injection x)) =
        E.survivor_injection x from
          DFunLike.congr_fun D.factor_retraction (E.survivor_injection x)]
      exact DFunLike.congr_fun E.factor_retraction x)

/-- Transport both groups of a survivor certificate across group
isomorphisms, as required for the basepoints of Proposition 15.3 (pp. 357-358). -/
def transport {G' H' : Type u} [Group G'] [Group H']
    (D : RepairedGroupFactorData G H) (e : G' ≃* G) (f : H ≃* H') :
    RepairedGroupFactorData G' H' :=
  ((ofMulEquiv e).trans D).trans (ofMulEquiv f)

end PoincareMT.RepairedGroupFactorData
