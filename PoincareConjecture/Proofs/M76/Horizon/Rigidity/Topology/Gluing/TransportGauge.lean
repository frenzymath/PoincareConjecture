import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Gluing.ComponentTransport
import PoincareConjecture.Proofs.M54.Mathlib.PathTransportFundamentalGroup

set_option autoImplicit false

open Set
open scoped unitInterval

namespace PoincareConjecture.M76.IncompressibleGluing

open Path.Homotopic.Quotient

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

noncomputable def mappedLoopHom (f : C(X, Y)) (a : X) {b : Y}
    (t : Path.Homotopic.Quotient b (f a)) :
    (FundamentalGroup X a)ᵐᵒᵖ →* (FundamentalGroup Y b)ᵐᵒᵖ :=
  (pathConjugation t).toMonoidHom.comp (MonoidHom.op (FundamentalGroup.map f a))

theorem mappedLoopHom_injective (f : C(X, Y)) (a : X) {b : Y}
    (t : Path.Homotopic.Quotient b (f a))
    (hf : Function.Injective (FundamentalGroup.map f a)) :
    Function.Injective (mappedLoopHom f a t) := by
  apply (pathConjugation t).injective.comp
  intro p q hpq
  apply MulOpposite.unop_injective
  exact hf (congrArg MulOpposite.unop hpq)

noncomputable def mappedTailDifference (f : C(X, Y)) {a x : X} {b : Y}
    (t : Path.Homotopic.Quotient b (f a))
    (s : Path.Homotopic.Quotient a x) (r : Path.Homotopic.Quotient b (f x)) :
    (FundamentalGroup Y b)ᵐᵒᵖ :=
  MulOpposite.op (r.trans ((s.map f).symm.trans t.symm))

theorem mapped_transport_gauge (f : C(X, Y)) {a x y : X} {b : Y}
    (t : Path.Homotopic.Quotient b (f a))
    (s₀ : Path.Homotopic.Quotient a x) (s₁ : Path.Homotopic.Quotient a y)
    (r₀ : Path.Homotopic.Quotient b (f x)) (r₁ : Path.Homotopic.Quotient b (f y))
    (p : Path.Homotopic.Quotient x y) :
    (MulOpposite.op (r₀.trans ((p.map f).trans r₁.symm)) :
        (FundamentalGroup Y b)ᵐᵒᵖ) *
        mappedTailDifference f t s₁ r₁ =
      mappedTailDifference f t s₀ r₀ *
        mappedLoopHom f a t (MulOpposite.op (s₀.trans (p.trans s₁.symm))) := by
  apply MulOpposite.unop_injective
  change (r₀.trans ((p.map f).trans r₁.symm)).trans
      (r₁.trans ((s₁.map f).symm.trans t.symm)) =
    (r₀.trans ((s₀.map f).symm.trans t.symm)).trans
      (t.trans (((s₀.trans (p.trans s₁.symm)).map f).trans t.symm))
  simp only [map_trans, map_symm, trans_assoc, symm_trans_assoc]

variable {A : Type*} [Group A]

noncomputable def gaugeTransport
    (L : LocalPathTransport (fun _ : Unit => (univ : Set X)) A)
    (frame : X → A) : LocalPathTransport (fun _ : Unit => (univ : Set X)) A where
  value p := frame (p 0) * L.value p * (frame (p 1))⁻¹
  map_const x := by simp [L.map_const]
  square S _ _ := by
    have hS := L.square S () (fun _ => mem_univ _)
    dsimp
    simp only [mul_assoc, inv_mul_cancel_left]
    simpa only [mul_assoc] using
      congrArg (fun a : A => frame (S (0, 0)) * a * (frame (S (1, 1)))⁻¹) hS

end PoincareConjecture.M76.IncompressibleGluing
