import Mathlib.Topology.Homotopy.HomotopyGroup








set_option autoImplicit false

noncomputable section

universe u v

namespace Poincare.Topology

variable {X : Type u} {Y : Type v}
variable [TopologicalSpace X] [TopologicalSpace Y]

def genLoopPostcomp (n : Nat) (f : C(X, Y)) (x : X) :
    GenLoop (Fin (n + 1)) X x -> GenLoop (Fin (n + 1)) Y (f x) :=
  fun a => ⟨f.comp a.val, fun t ht => congrArg f (a.property t ht)⟩

theorem genLoopPostcomp_val (n : Nat) (f : C(X, Y)) (x : X)
    (a : GenLoop (Fin (n + 1)) X x) :
    (genLoopPostcomp n f x a).val = f.comp a.val := rfl

def homotopyGroupPostcomp (n : Nat) (f : C(X, Y)) (x : X) :
    HomotopyGroup (Fin (n + 1)) X x →*
      HomotopyGroup (Fin (n + 1)) Y (f x) := by
  let F : HomotopyGroup (Fin (n + 1)) X x ->
      HomotopyGroup (Fin (n + 1)) Y (f x) :=
    Quotient.map (genLoopPostcomp n f x) (by
      intro a b h
      change a.val.HomotopicRel b.val (Cube.boundary (Fin (n + 1))) at h
      change (f.comp a.val).HomotopicRel (f.comp b.val) (Cube.boundary (Fin (n + 1)))
      exact h.comp_continuousMap f)
  refine { toFun := F, map_one' := ?_, map_mul' := ?_ }
  · rw [HomotopyGroup.one_def, HomotopyGroup.one_def]
    change (Quotient.mk _ (genLoopPostcomp n f x GenLoop.const) :
      HomotopyGroup (Fin (n + 1)) Y (f x)) = Quotient.mk _ GenLoop.const
    apply congrArg (fun b : GenLoop (Fin (n + 1)) Y (f x) =>
      (Quotient.mk _ b : HomotopyGroup (Fin (n + 1)) Y (f x)))
    apply GenLoop.ext
    intro t
    rfl
  · intro a b
    refine Quotient.inductionOn₂ a b ?_
    intro p q
    let p' : HomotopyGroup (Fin (n + 1)) X x := Quotient.mk _ p
    let q' : HomotopyGroup (Fin (n + 1)) X x := Quotient.mk _ q
    change F (p' * q') = F p' * F q'
    have hsource : p' * q' =
        (Quotient.mk _ (GenLoop.transAt 0 q p) :
          HomotopyGroup (Fin (n + 1)) X x) :=
      HomotopyGroup.mul_spec (i := (0 : Fin (n + 1))) (p := p) (q := q)
    have htarget : F p' * F q' =
        (Quotient.mk _
          (GenLoop.transAt 0 (genLoopPostcomp n f x q) (genLoopPostcomp n f x p)) :
          HomotopyGroup (Fin (n + 1)) Y (f x)) :=
      HomotopyGroup.mul_spec (i := (0 : Fin (n + 1)))
        (p := genLoopPostcomp n f x p) (q := genLoopPostcomp n f x q)
    have ht : genLoopPostcomp n f x (GenLoop.transAt 0 q p) =
        GenLoop.transAt 0 (genLoopPostcomp n f x q) (genLoopPostcomp n f x p) := by
      apply GenLoop.ext
      intro t
      change f (GenLoop.transAt 0 q p t) =
        GenLoop.transAt 0 (genLoopPostcomp n f x q) (genLoopPostcomp n f x p) t
      simp only [GenLoop.transAt, GenLoop.coe_copy]
      split_ifs <;> rfl
    rw [hsource, htarget]
    change (Quotient.mk _ (genLoopPostcomp n f x (GenLoop.transAt 0 q p)) :
        HomotopyGroup (Fin (n + 1)) Y (f x)) =
      Quotient.mk _
        (GenLoop.transAt 0 (genLoopPostcomp n f x q) (genLoopPostcomp n f x p))
    exact congrArg (fun c : GenLoop (Fin (n + 1)) Y (f x) =>
      (Quotient.mk _ c : HomotopyGroup (Fin (n + 1)) Y (f x))) ht

theorem homotopyGroupPostcomp_mk (n : Nat) (f : C(X, Y)) (x : X)
    (a : GenLoop (Fin (n + 1)) X x) :
    homotopyGroupPostcomp n f x
        (Quotient.mk _ a : HomotopyGroup (Fin (n + 1)) X x) =
      (Quotient.mk _ (genLoopPostcomp n f x a) :
        HomotopyGroup (Fin (n + 1)) Y (f x)) := rfl

end Poincare.Topology
