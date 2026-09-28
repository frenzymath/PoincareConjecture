import PoincareConjecture.Proofs.M59.Mathlib.CoveringLoopFamilies
import PoincareConjecture.Proofs.M59.Mathlib.LoopComparison

set_option autoImplicit false

open scoped Topology unitInterval

namespace Path

theorem homotopic_of_subsingleton_fundamentalGroup
    {X : Type*} [TopologicalSpace X] {x y : X}
    (h : Subsingleton (FundamentalGroup X x)) (p q : Path x y) : p.Homotopic q := by
  apply Homotopic.Quotient.eq.mp
  let P : Homotopic.Quotient x y := Homotopic.Quotient.mk p
  let Q : Homotopic.Quotient x y := Homotopic.Quotient.mk q
  have hloop : P.trans Q.symm = Homotopic.Quotient.refl x := h.elim _ _
  have heq := congrArg (fun r : Homotopic.Quotient x x => r.trans Q) hloop
  simpa only [Homotopic.Quotient.trans_assoc, Homotopic.Quotient.symm_trans,
    Homotopic.Quotient.trans_refl, Homotopic.Quotient.refl_trans] using heq

end Path

namespace PoincareConjecture.Proofs.M59.CubeBoundaryQuotient

variable {S E : Type*} [TopologicalSpace S] [T2Space S] [LocallyCompactSpace S]
  [TopologicalSpace E] [SimplyConnectedSpace E]
  (q : CubeBoundaryQuotient (Fin 1) S)

include q

theorem fundamentalGroup_continuousLoop_subsingleton (c : E)
    (hpi : Subsingleton (HomotopyGroup.Pi 2 E c)) :
    Subsingleton (FundamentalGroup C(S, E) (ContinuousMap.const S c)) := by
  let hpiOne : Subsingleton (HomotopyGroup.Pi 1 E c) :=
    HomotopyGroup.pi1MulEquivFundamentalGroup.injective.subsingleton
  let : Subsingleton (HomotopyGroup.Pi 2 E c) := hpi
  let : Subsingleton (HomotopyGroup.Pi 1 C(S, E) (ContinuousMap.const S c)) :=
    (q.loopHomotopyEquiv 1 c hpiOne).injective.subsingleton
  exact HomotopyGroup.pi1MulEquivFundamentalGroup.surjective.subsingleton

theorem continuousLoop_path_homotopic_constant {c c' : E}
    (hpi : Subsingleton (HomotopyGroup.Pi 2 E c))
    (L : Path (ContinuousMap.const S c) (ContinuousMap.const S c')) (r : Path c c') :
    L.Homotopic (r.map ContinuousMap.continuous_const') :=
  Path.homotopic_of_subsingleton_fundamentalGroup
    (q.fundamentalGroup_continuousLoop_subsingleton c hpi) L _

theorem continuousLoop_homotopyAlong_constant {N : Type*} [Finite N]
    {c c' : E} (hpi : Subsingleton (HomotopyGroup.Pi 2 E c))
    {A : GenLoop N C(S, E) (ContinuousMap.const S c)}
    {B : GenLoop N C(S, E) (ContinuousMap.const S c')}
    {L : Path (ContinuousMap.const S c) (ContinuousMap.const S c')}
    (H : GenLoop.HomotopyAlong L A B) (r : Path c c') :
    Nonempty (GenLoop.HomotopyAlong (r.map ContinuousMap.continuous_const') A B) :=
  H.change_path (q.continuousLoop_path_homotopic_constant hpi L r)

end PoincareConjecture.Proofs.M59.CubeBoundaryQuotient
