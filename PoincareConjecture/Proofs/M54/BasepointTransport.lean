import PoincareConjecture.Definitions.M54GroupEffects









set_option autoImplicit false

universe u

namespace PoincareConjecture.RepairedGroupFactorData

variable {G H K : Type u} [Group G] [Group H] [Group K]



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



def ofMulEquiv (e : G ≃* H) : RepairedGroupFactorData G H :=
  ofRetraction e.toMonoidHom e.symm.toMonoidHom (by ext x; exact e.apply_symm_apply x)



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



def transport {G' H' : Type u} [Group G'] [Group H']
    (D : RepairedGroupFactorData G H) (e : G' ≃* G) (f : H ≃* H') :
    RepairedGroupFactorData G' H' :=
  ((ofMulEquiv e).trans D).trans (ofMulEquiv f)

end PoincareConjecture.RepairedGroupFactorData
