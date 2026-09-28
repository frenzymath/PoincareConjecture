import PoincareConjecture.Proofs.M59.Mathlib.CubeTransport
import Mathlib.Topology.Homotopy.HomotopyGroup












set_option autoImplicit false

open scoped Topology unitInterval

universe u v w

namespace GenLoop.HomotopyAlong

open PoincareConjecture.Proofs.M02

variable {N : Type w} [Finite N] {X : Type u} {Y : Type v}
  [TopologicalSpace X] [TopologicalSpace Y]



def ofMapHomotopy {f g : C(X, Y)} (H : f.Homotopy g) {x : X} (a : GenLoop N X x) :
    HomotopyAlong (H.evalAt x) (mapGenLoop f rfl a) (mapGenLoop g rfl a) where
  toHomotopy := H.comp (ContinuousMap.Homotopy.refl a.val)
  boundary_path t z := congrArg (fun x => H (t, x)) (GenLoop.boundary a z z.2)



theorem endpoint_homotopic_of_initial {x y : X} {p : Path x y}
    {a c : GenLoop N X x} {b d : GenLoop N X y}
    (H : HomotopyAlong p a b) (G : HomotopyAlong p c d) (h : GenLoop.Homotopic a c) :
    GenLoop.Homotopic b d := by
  obtain ⟨K⟩ := h
  obtain ⟨L⟩ := ((ofRel K).trans G).change_path (Path.Homotopic.refl_trans p)
  exact H.endpoint_homotopic L

end GenLoop.HomotopyAlong

namespace PoincareConjecture.Proofs.M59

open PoincareConjecture.Proofs.M02



theorem homotopyGroupMap_injective_of_leftHomotopyInverse
    {N : Type w} [Finite N] {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) (g : C(Y, X))
    (H : (g.comp f).Homotopy (ContinuousMap.id X)) (x : X) :
    Function.Injective (homotopyGroupMap N f (rfl : f x = f x)) := by
  intro a b
  refine Quotient.inductionOn₂ a b ?_
  intro a b h
  apply Quotient.sound
  exact (GenLoop.HomotopyAlong.ofMapHomotopy H a).endpoint_homotopic_of_initial
    (GenLoop.HomotopyAlong.ofMapHomotopy H b)
    (mapGenLoop_homotopic g rfl (Quotient.exact h))



def pathEvaluation {X : Type u} [TopologicalSpace X] (t : I) : C(C(I, X), X) :=
  ⟨fun f => f t, by fun_prop⟩



def pathConstant {X : Type u} [TopologicalSpace X] : C(X, C(I, X)) :=
  ⟨ContinuousMap.const I, ContinuousMap.continuous_const'⟩

private def shrinkTime : C(I × I, I) :=
  ⟨fun v => unitInterval.symm v.1 * v.2, by
    apply Continuous.subtype_mk
    change Continuous (fun v : I × I => (1 - (v.1 : ℝ)) * (v.2 : ℝ))
    fun_prop⟩



def pathSpaceShrink {X : Type u} [TopologicalSpace X] :
    (ContinuousMap.id C(I, X)).Homotopy
      (pathConstant.comp (pathEvaluation 0)) where
  toFun v := ⟨fun s => v.2 (shrinkTime (v.1, s)),
    v.2.continuous.comp (shrinkTime.continuous.comp (continuous_const.prodMk continuous_id))⟩
  continuous_toFun := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun v : (I × C(I, X)) × I => v.1.2 (shrinkTime (v.1.1, v.2)))
    exact (continuous_snd.comp continuous_fst).eval
      (shrinkTime.continuous.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd))
  map_zero_left f := by ext s; simp [shrinkTime]
  map_one_left f := by ext s; simp [shrinkTime, pathConstant, pathEvaluation]



theorem homotopyGroupMap_pathEvaluation_injective
    {N : Type w} [Finite N] {X : Type u} [TopologicalSpace X] (r : C(I, X)) :
    Function.Injective (homotopyGroupMap N (pathEvaluation 0) (rfl : r 0 = r 0)) :=
  homotopyGroupMap_injective_of_leftHomotopyInverse
    (pathEvaluation 0) pathConstant pathSpaceShrink.symm r



theorem pathSpace_homotopyGroup_subsingleton
    {N : Type w} [Finite N] {X : Type u} [TopologicalSpace X] (r : C(I, X))
    (h : Subsingleton (HomotopyGroup N X (r 0))) :
    Subsingleton (HomotopyGroup N C(I, X) r) :=
  ⟨fun _a _b => homotopyGroupMap_pathEvaluation_injective r (h.elim _ _)⟩

end PoincareConjecture.Proofs.M59
