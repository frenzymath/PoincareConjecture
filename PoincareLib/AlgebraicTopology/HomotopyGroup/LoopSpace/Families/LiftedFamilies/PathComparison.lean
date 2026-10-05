import PoincareLib.AlgebraicTopology.HomotopyGroup.LoopSpace.Comparison.CoveringLoopFamilies
import PoincareLib.AlgebraicTopology.HomotopyGroup.LoopSpace.Comparison.LoopComparison

/-!
# Paths between constant loops on the simply connected cover

The continuous-loop comparison in dimension one shows that a simply
connected space with vanishing pi2 has trivial pi1 in its constant-loop
component. Consequently a lifted boundary path may be replaced by a path
of constant loops. Source: Morgan--Tian Claim 18.16, printed p. 430;
Hatcher, Section 4.1 and Proposition 4A.2, printed pp. 341-342 and 422.
-/

set_option autoImplicit false

open scoped Topology unitInterval

namespace Path

/-- Triviality of the fundamental group at the initial point makes any two
paths with the same endpoints homotopic. No connectedness of the whole
space is required. Source: Hatcher, Section 1.1, path cancellation. -/
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

namespace PoincareMT.Proofs.M59.CubeBoundaryQuotient

variable {S E : Type*} [TopologicalSpace S] [T2Space S] [LocallyCompactSpace S]
  [TopologicalSpace E] [SimplyConnectedSpace E]
  (q : CubeBoundaryQuotient (Fin 1) S)

include q

/-- If the simply connected target has vanishing pi2, the component of
constant continuous circle maps has trivial pi1.
Source: MT Claim 18.16, printed p. 430, in dimension one. -/
theorem fundamentalGroup_continuousLoop_subsingleton (c : E)
    (hpi : Subsingleton (HomotopyGroup.Pi 2 E c)) :
    Subsingleton (FundamentalGroup C(S, E) (ContinuousMap.const S c)) := by
  let hpiOne : Subsingleton (HomotopyGroup.Pi 1 E c) :=
    HomotopyGroup.pi1MulEquivFundamentalGroup.injective.subsingleton
  let : Subsingleton (HomotopyGroup.Pi 2 E c) := hpi
  let : Subsingleton (HomotopyGroup.Pi 1 C(S, E) (ContinuousMap.const S c)) :=
    (q.loopHomotopyEquiv 1 c hpiOne).injective.subsingleton
  exact HomotopyGroup.pi1MulEquivFundamentalGroup.surjective.subsingleton

/-- A path of circle maps between constant loops is homotopic to the
constant-loop path induced by any path between their covering points.
Source: Hatcher 4A.2, printed p. 422; MT Claim 18.16, printed p. 430. -/
theorem continuousLoop_path_homotopic_constant {c c' : E}
    (hpi : Subsingleton (HomotopyGroup.Pi 2 E c))
    (L : Path (ContinuousMap.const S c) (ContinuousMap.const S c')) (r : Path c c') :
    L.Homotopic (r.map ContinuousMap.continuous_const') :=
  Path.homotopic_of_subsingleton_fundamentalGroup
    (q.fundamentalGroup_continuousLoop_subsingleton c hpi) L _

/-- Replace the lifted side trace by constant-loop transport while fixing
both endpoint cubes exactly. Source: Hatcher, Section 4.1, pp. 341-342,
and Proposition 4A.2, p. 422. -/
theorem continuousLoop_homotopyAlong_constant {N : Type*} [Finite N]
    {c c' : E} (hpi : Subsingleton (HomotopyGroup.Pi 2 E c))
    {A : GenLoop N C(S, E) (ContinuousMap.const S c)}
    {B : GenLoop N C(S, E) (ContinuousMap.const S c')}
    {L : Path (ContinuousMap.const S c) (ContinuousMap.const S c')}
    (H : GenLoop.HomotopyAlong L A B) (r : Path c c') :
    Nonempty (GenLoop.HomotopyAlong (r.map ContinuousMap.continuous_const') A B) :=
  H.change_path (q.continuousLoop_path_homotopic_constant hpi L r)

end PoincareMT.Proofs.M59.CubeBoundaryQuotient
