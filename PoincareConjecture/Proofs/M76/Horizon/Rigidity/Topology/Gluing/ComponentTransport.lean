import PoincareConjecture.Proofs.M54.Mathlib.BasedPathTransport
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.FundamentalGroup.PathMaps









set_option autoImplicit false

open Set
open scoped unitInterval

namespace PoincareConjecture.M76.IncompressibleGluing

variable {X : Type*} [TopologicalSpace X]

open Path.Homotopic.Quotient



noncomputable def pathConjugation {b x : X} (t : Path.Homotopic.Quotient b x) :
    (FundamentalGroup X x)ᵐᵒᵖ ≃* (FundamentalGroup X b)ᵐᵒᵖ where
  toFun q := MulOpposite.op (t.trans ((MulOpposite.unop q).trans t.symm))
  invFun q := MulOpposite.op (t.symm.trans ((MulOpposite.unop q).trans t))
  left_inv q := by
    apply MulOpposite.unop_injective
    change t.symm.trans ((t.trans ((MulOpposite.unop q).trans t.symm)).trans t) = _
    simp only [trans_assoc, symm_trans_assoc, symm_trans, trans_refl]
  right_inv q := by
    apply MulOpposite.unop_injective
    change t.trans ((t.symm.trans ((MulOpposite.unop q).trans t)).trans t.symm) = _
    simp only [trans_assoc, trans_symm_assoc, trans_symm, trans_refl]
  map_mul' p q := by
    apply MulOpposite.unop_injective
    change t.trans (((MulOpposite.unop p).trans (MulOpposite.unop q)).trans t.symm) =
      (t.trans ((MulOpposite.unop p).trans t.symm)).trans
        (t.trans ((MulOpposite.unop q).trans t.symm))
    simp only [trans_assoc, symm_trans_assoc]



abbrev ComponentGroup (X : Type*) [TopologicalSpace X] (c : ZerothHomotopy X) :=
  (FundamentalGroup X c.out)ᵐᵒᵖ

theorem joined_component_out_iff (c : ZerothHomotopy X) (x : X) :
    Joined c.out x ↔ c = ZerothHomotopy.mk x := by
  constructor
  · intro h
    exact (Quotient.out_eq' c).symm.trans (Quotient.sound h)
  · intro h
    exact Quotient.exact ((Quotient.out_eq' c).trans h)


noncomputable def componentTails (c : ZerothHomotopy X) (x : X)
    (h : Joined c.out x) : Path.Homotopic.Quotient c.out x := mk h.somePath


noncomputable def componentTransport (p : C(unitInterval, X)) :
    ∀ c : ZerothHomotopy X, ComponentGroup X c :=
  fun c => basedContinuousTransport c.out (componentTails c) p

@[simp] theorem componentTransport_const (x : X) :
    componentTransport (ContinuousMap.const unitInterval x) = 1 := by
  funext c
  exact basedContinuousTransport_const c.out (componentTails c) x


theorem componentTransport_eq_one_of_ne (p : C(unitInterval, X))
    (c : ZerothHomotopy X) (hc : c ≠ ZerothHomotopy.mk (p 0)) :
    componentTransport p c = 1 := by
  exact basedTransport_of_not_joined c.out (componentTails c) (mk p.toPath)
    (fun h => hc ((joined_component_out_iff c (p 0)).mp h))



theorem componentTransport_square (S : C(unitInterval × unitInterval, X)) :
    componentTransport (S.horizontalPath 0) * componentTransport (S.verticalPath 1) =
      componentTransport (S.verticalPath 0) * componentTransport (S.horizontalPath 1) := by
  funext c
  exact basedContinuousTransport_square c.out (componentTails c) S


noncomputable def componentLoopTransport (x : X) :
    (FundamentalGroup X x)ᵐᵒᵖ →* (∀ c : ZerothHomotopy X, ComponentGroup X c) where
  toFun q c := basedTransport c.out (componentTails c) (MulOpposite.unop q)
  map_one' := by
    funext c
    exact basedTransport_refl c.out (componentTails c) x
  map_mul' p q := by
    funext c
    exact basedTransport_trans c.out (componentTails c)
      (MulOpposite.unop p) (MulOpposite.unop q)

@[simp] theorem componentLoopTransport_mk (x : X) (p : Path x x) :
    componentLoopTransport x (MulOpposite.op (mk p)) =
      componentTransport p.toContinuousMap := by
  funext c
  exact (basedContinuousTransport_path c.out (componentTails c) p).symm


theorem componentLoopTransport_injective (x : X) :
    Function.Injective (componentLoopTransport x) := by
  let c := ZerothHomotopy.mk x
  have hx : Joined c.out x := (joined_component_out_iff c x).mpr rfl
  intro p q hpq
  have heq := congrFun hpq c
  change basedTransport c.out (componentTails c) (MulOpposite.unop p) =
    basedTransport c.out (componentTails c) (MulOpposite.unop q) at heq
  rw [basedTransport_of_joined _ _ _ hx hx,
    basedTransport_of_joined _ _ _ hx hx] at heq
  exact (pathConjugation (componentTails c x hx)).injective heq

end PoincareConjecture.M76.IncompressibleGluing
