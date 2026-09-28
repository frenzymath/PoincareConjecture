import PoincareConjecture.Proofs.M59.Mathlib.LoopComparison
import PoincareConjecture.Proofs.M59.Mathlib.PathSpaceHomotopy
import PoincareConjecture.Proofs.M59.Sec4_1_Whiskering.GenLoopWhisker











set_option autoImplicit false

open scoped Topology unitInterval

noncomputable section

namespace PoincareConjecture.Proofs.M59

open PoincareConjecture.Proofs.M02

variable {S X : Type*} [TopologicalSpace S] [TopologicalSpace X]



def constantMapPath {x y : X} (r : Path x y) :
    Path (ContinuousMap.const S x) (ContinuousMap.const S y) :=
  r.map ContinuousMap.continuous_const'




def loopHomotopyPathCube [LocallyCompactSpace S]
    {N : Type*} [Finite N] {x y : X} {r : Path x y}
    {a : GenLoop N C(S, X) (ContinuousMap.const S x)}
    {b : GenLoop N C(S, X) (ContinuousMap.const S y)}
    (H : GenLoop.HomotopyAlong (constantMapPath r) a b) :
    GenLoop N C(S, C(I, X)) (ContinuousMap.const S r.toContinuousMap) :=
  ⟨⟨fun v => ⟨fun z => ⟨fun t => H.toHomotopy (t, v) z,
      (H.toHomotopy.continuous.comp (continuous_id.prodMk continuous_const)).eval
        continuous_const⟩, by
      apply ContinuousMap.continuous_of_continuous_uncurry
      change Continuous (fun w : S × I => H.toHomotopy (w.2, v) w.1)
      exact (H.toHomotopy.continuous.comp (continuous_snd.prodMk continuous_const)).eval
        continuous_fst⟩, by
    apply ContinuousMap.continuous_of_continuous_uncurry
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun w : ((I^N) × S) × I => H.toHomotopy (w.2, w.1.1) w.1.2)
    exact (H.toHomotopy.continuous.comp
      (continuous_snd.prodMk (continuous_fst.comp continuous_fst))).eval
        (continuous_snd.comp continuous_fst)⟩, by
    intro v hv
    ext z t
    exact congrArg (fun f : C(S, X) => f z) (H.boundary_path t ⟨v, hv⟩)⟩



theorem loopHomotopyPathCube_zero [LocallyCompactSpace S]
    {N : Type*} [Finite N] {x y : X} {r : Path x y}
    {a : GenLoop N C(S, X) (ContinuousMap.const S x)}
    {b : GenLoop N C(S, X) (ContinuousMap.const S y)}
    (H : GenLoop.HomotopyAlong (constantMapPath r) a b) :
    mapGenLoop (postcomposeMap S (pathEvaluation 0))
      (postcomposeMap_const S (pathEvaluation 0) r.source) (loopHomotopyPathCube H) = a := by
  ext v z
  exact congrArg (fun f : C(S, X) => f z) (H.toHomotopy.apply_zero v)



theorem loopHomotopyPathCube_one [LocallyCompactSpace S]
    {N : Type*} [Finite N] {x y : X} {r : Path x y}
    {a : GenLoop N C(S, X) (ContinuousMap.const S x)}
    {b : GenLoop N C(S, X) (ContinuousMap.const S y)}
    (H : GenLoop.HomotopyAlong (constantMapPath r) a b) :
    mapGenLoop (postcomposeMap S (pathEvaluation 1))
      (postcomposeMap_const S (pathEvaluation 1) r.target) (loopHomotopyPathCube H) = b := by
  ext v z
  exact congrArg (fun f : C(S, X) => f z) (H.toHomotopy.apply_one v)



def pathCubeEvaluationHomotopy
    {N : Type*} [Finite N] {x y : X} (r : Path x y)
    (a : GenLoop N C(I, X) r.toContinuousMap) :
    GenLoop.HomotopyAlong r
      (mapGenLoop (pathEvaluation 0) r.source a)
      (mapGenLoop (pathEvaluation 1) r.target a) where
  toFun v := a v.2 v.1
  continuous_toFun := (a.val.continuous.comp continuous_snd).eval continuous_fst
  map_zero_left _ := rfl
  map_one_left _ := rfl
  boundary_path t v := congrArg (fun f : C(I, X) => f t) (GenLoop.boundary a v v.2)



theorem pathEvaluation_transport (n : Nat) {x y : X} (r : Path x y)
    (a : HomotopyGroup.Pi n C(I, X) r.toContinuousMap) :
    (m59HigherBasepointTransport X n).map r
      (homotopyGroupMap (Fin n) (pathEvaluation 0) r.source a) =
      homotopyGroupMap (Fin n) (pathEvaluation 1) r.target a := by
  refine Quotient.inductionOn a fun a => ?_
  exact Quotient.sound (GenLoop.boundaryTransport_homotopic_of_homotopyAlong
    (pathCubeEvaluationHomotopy r a))

namespace CubeBoundaryQuotient




theorem loopHomotopyEquiv_homotopyAlong
    [T2Space S] [LocallyCompactSpace S]
    (q : CubeBoundaryQuotient (Fin 1) S) (n : Nat) [Nonempty (Fin n)]
    {x y : X} (hpiX : Subsingleton (HomotopyGroup.Pi n X x))
    (hpiY : Subsingleton (HomotopyGroup.Pi n X y)) (r : Path x y)
    {a : GenLoop (Fin n) C(S, X) (ContinuousMap.const S x)}
    {b : GenLoop (Fin n) C(S, X) (ContinuousMap.const S y)}
    (H : GenLoop.HomotopyAlong (constantMapPath r) a b) :
    (m59HigherBasepointTransport X (n + 1)).map r (q.loopHomotopyEquiv n x hpiX ⟦a⟧) =
      q.loopHomotopyEquiv n y hpiY ⟦b⟧ := by
  have hp : Subsingleton (HomotopyGroup.Pi n X (r 0)) := by
    simpa only [r.source] using hpiX
  let hpPath := pathSpace_homotopyGroup_subsingleton r.toContinuousMap hp
  let A := loopHomotopyPathCube H
  have h0 := q.loopHomotopyEquiv_naturality n hpPath hpiX
    (pathEvaluation 0) r.source (⟦A⟧ : HomotopyGroup.Pi n C(S, C(I, X)) _)
  have h1 := q.loopHomotopyEquiv_naturality n hpPath hpiY
    (pathEvaluation 1) r.target (⟦A⟧ : HomotopyGroup.Pi n C(S, C(I, X)) _)
  have hA0 : homotopyGroupMap (Fin n) (postcomposeMap S (pathEvaluation 0))
      (postcomposeMap_const S (pathEvaluation 0) r.source) ⟦A⟧ = ⟦a⟧ :=
    congrArg Quotient.mk'' (loopHomotopyPathCube_zero H)
  have hA1 : homotopyGroupMap (Fin n) (postcomposeMap S (pathEvaluation 1))
      (postcomposeMap_const S (pathEvaluation 1) r.target) ⟦A⟧ = ⟦b⟧ :=
    congrArg Quotient.mk'' (loopHomotopyPathCube_one H)
  rw [hA0] at h0
  rw [hA1] at h1
  rw [h0, h1]
  exact pathEvaluation_transport (n + 1) r _

end CubeBoundaryQuotient

end PoincareConjecture.Proofs.M59
