import PoincareConjecture.Definitions.M59BasepointTransport
import PoincareConjecture.Proofs.M59.Mathlib.CubeTransportMultiplication










set_option autoImplicit false

open scoped Topology unitInterval

noncomputable section

universe u

namespace PoincareConjecture



def m59GenLoopWhisker (X : Type u) [TopologicalSpace X] (n : ℕ) :
    M59GenLoopWhisker X n where
  whisker := GenLoop.boundaryTransport
  respects_homotopy := GenLoop.boundaryTransport_homotopic



theorem m59GenLoopWhisker_map_mk {X : Type u} [TopologicalSpace X] {n : ℕ}
    {x y : X} (p : Path x y) (a : GenLoop (Fin n) X x) :
    M59GenLoopWhisker.map (m59GenLoopWhisker X n) p ⟦a⟧ =
      ⟦GenLoop.boundaryTransport p a⟧ := rfl




def m59HigherBasepointTransport (X : Type u) [TopologicalSpace X] (n : ℕ) :
    M59HigherBasepointTransport X n where
  whisker := m59GenLoopWhisker X n
  map_refl a := Quotient.inductionOn a fun a =>
    Quotient.sound (GenLoop.boundaryTransport_refl a)
  map_trans p q a := Quotient.inductionOn a fun a =>
    Quotient.sound (GenLoop.boundaryTransport_trans p q a)
  map_left_inverse p a := Quotient.inductionOn a fun a =>
    Quotient.sound (GenLoop.boundaryTransport_symm p a)
  map_one p _ := Quotient.sound (GenLoop.boundaryTransport_const p)
  map_mul p _ a b := by
    let i : Fin n := Classical.choice inferInstance
    refine Quotient.inductionOn₂ a b ?_
    intro a b
    exact (congrArg (M59GenLoopWhisker.map (m59GenLoopWhisker X n) p)
      (HomotopyGroup.mul_spec (i := i) (p := a) (q := b))).trans
        ((Quotient.sound (GenLoop.boundaryTransport_transAt i p b a)).trans
          (HomotopyGroup.mul_spec (i := i)
            (p := GenLoop.boundaryTransport p a) (q := GenLoop.boundaryTransport p b)).symm)



theorem m59HigherBasepointTransport_path_homotopic
    {X : Type u} [TopologicalSpace X] {n : ℕ} {x y : X} {p q : Path x y}
    (h : p.Homotopic q) (a : HomotopyGroup.Pi n X x) :
    (m59HigherBasepointTransport X n).map p a =
      (m59HigherBasepointTransport X n).map q a :=
  Quotient.inductionOn a fun a => Quotient.sound (GenLoop.boundaryTransport_path_homotopic h a)

end PoincareConjecture
