import PoincareConjecture.Definitions.Ch15.SurgeryComparison
import PoincareConjecture.Proofs.M40.Mathlib.HomotopyGroupFunctoriality

set_option autoImplicit false

open scoped Topology unitInterval

universe u v

namespace PoincareConjecture.Proofs.M40

noncomputable section

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

theorem surgeryHomotopyMap_eq_postcomp (n : ℕ) (f : C(X, Y)) (x : X) :
    surgeryHomotopyMap (n := n + 1) f (show f x = f x from rfl) =
      M02.Topology.homotopyGroupPostcomp n f x := rfl

theorem surgeryHomotopyMap_eq_of_homotopic [SimplyConnectedSpace Y]
    {x : X} {y : Y} {n : ℕ} (f g : C(X, Y)) (hf : f x = y) (hg : g x = y)
    (hfg : f.Homotopic g) (a : HomotopyGroup.Pi n X x) :
    surgeryHomotopyMap f hf a = surgeryHomotopyMap g hg a := by
  obtain ⟨H⟩ := hfg
  induction a using Quotient.inductionOn with | h a =>
    let p : Path y y :=
      { toFun := fun t => H (t, x)
        continuous_toFun := H.continuous.comp (continuous_id.prodMk continuous_const)
        source' := (H.apply_zero x).trans hf
        target' := (H.apply_one x).trans hg }
    apply Quotient.sound
    apply Topology.homotopicRel_of_uniform_boundary_trace
      (surgeryMappedGenLoop f hf a) (surgeryMappedGenLoop g hg a)
      (H.compContinuousMap a.val) p
    intro t z
    exact congrArg (fun w => H (t, w)) (a.property z.val z.property)

theorem surgeryHomotopyMap_bijective_of_homotopyEquiv
    [SimplyConnectedSpace X] [SimplyConnectedSpace Y]
    {x : X} {y : Y} (n : ℕ) (f : C(X, Y)) (hf : f x = y)
    (he : ∃ e : ContinuousMap.HomotopyEquiv X Y, e.toFun = f) :
    Function.Bijective (surgeryHomotopyMap (n := n + 1) f hf) := by
  obtain ⟨e, rfl⟩ := he
  subst y
  rw [surgeryHomotopyMap_eq_postcomp]
  exact Topology.homotopyGroupPostcomp_bijective_of_homotopyEquiv n e x

theorem surgeryPiThree_bijective_of_homotopyEquiv
    [SimplyConnectedSpace X] [SimplyConnectedSpace Y]
    {x : X} {y : Y} (f : C(X, Y)) (hf : f x = y)
    (he : ∃ e : ContinuousMap.HomotopyEquiv X Y, e.toFun = f) :
    Function.Bijective (surgeryHomotopyMap (n := 3) f hf) :=
  surgeryHomotopyMap_bijective_of_homotopyEquiv 2 f hf he

end

end PoincareConjecture.Proofs.M40
