import PoincareConjecture.Proofs.Horizon.Topology.Homotopy.Groups.HomotopyPostcomposition
import Mathlib.Topology.Homeomorph.Lemmas








set_option autoImplicit false

universe u v

namespace Poincare.Topology

noncomputable section

theorem homotopyGroupPostcomp_homeomorph_bijective
    {X : Type u} [TopologicalSpace X] {Y : Type v} [TopologicalSpace Y]
    (n : Nat) (e : X ≃ₜ Y) (x : X) :
    Function.Bijective (homotopyGroupPostcomp n (e : C(X, Y)) x) := by
  constructor
  · intro a b
    refine Quotient.inductionOn₂ a b ?_
    intro p q hpq
    have hrel : GenLoop.Homotopic (genLoopPostcomp n (e : C(X, Y)) x p)
        (genLoopPostcomp n (e : C(X, Y)) x q) := Quotient.exact hpq
    change ((e : C(X, Y)).comp p.val).HomotopicRel
      ((e : C(X, Y)).comp q.val) (Cube.boundary (Fin (n + 1))) at hrel
    obtain ⟨H⟩ := hrel.comp_continuousMap (e.symm : C(Y, X))
    apply Quotient.sound
    refine ⟨H.cast ?_ ?_⟩
    · ext z
      exact e.symm_apply_apply (p z)
    · ext z
      exact e.symm_apply_apply (q z)
  · intro a
    obtain ⟨p, rfl⟩ := Quotient.exists_rep a
    let q : GenLoop (Fin (n + 1)) X x :=
      ⟨(e.symm : C(Y, X)).comp p.val, fun z hz =>
        (congrArg e.symm (GenLoop.boundary p z hz)).trans (e.symm_apply_apply x)⟩
    refine ⟨Quotient.mk _ q, ?_⟩
    change (Quotient.mk _ (genLoopPostcomp n (e : C(X, Y)) x q) :
      HomotopyGroup.Pi (n + 1) Y (e x)) = Quotient.mk _ p
    apply congrArg (fun r : GenLoop (Fin (n + 1)) Y (e x) =>
      (Quotient.mk _ r : HomotopyGroup.Pi (n + 1) Y (e x)))
    apply GenLoop.ext
    intro z
    exact e.apply_symm_apply (p z)

def homotopyGroupHomeomorph
    {X : Type u} [TopologicalSpace X] {Y : Type v} [TopologicalSpace Y]
    (n : Nat) (e : X ≃ₜ Y) (x : X) :
    HomotopyGroup.Pi (n + 1) X x ≃* HomotopyGroup.Pi (n + 1) Y (e x) :=
  MulEquiv.ofBijective (homotopyGroupPostcomp n (e : C(X, Y)) x)
    (homotopyGroupPostcomp_homeomorph_bijective n e x)

end

end Poincare.Topology
