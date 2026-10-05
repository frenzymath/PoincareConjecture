import PoincareLib.Topology.Manifold.Surgery.Reconstruction.Assembly.SliceDecomposition
import PoincareLib.Topology.Manifold.Surgery.Reconstruction.Assembly.DisjointUnionSum
import PoincareLib.Topology.Manifold.Surgery.Reconstruction.Assembly.StepLift
import PoincareLib.Topology.Manifold.Surgery.Reconstruction.Assembly.SourceTransport

/-!
# Whole-survivor substitution in a local reconstruction

Reconstruct the complete survivor slice, retain the discarded pieces in a
disjoint summand, then perform the local reconstruction operations. This is
the inductive step in Morgan--Tian Corollary 15.4, pp. 358-359.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Topology

universe u v

namespace PoincareMT

/-- Substitute an assembly of the whole post-surgery slice, adjoining exactly
the local non-survivor pieces. Source: MT Corollary 15.4, pp. 358-359. -/
noncomputable def SurgeryTopologyConclusion.substitute
    {A B : GeneralizedSliceCarrier.{u}} {ι : Type v}
    {pieces : ι → GeneralizedSliceCarrier.{u}}
    (S : SurgeryTopologyConclusion A B) (R : M72IndexedAssembly pieces B)
    (hpieces : ∀ i, Nonempty (pieces i).carrier) :
    M72IndexedAssembly
      (Sum.elim pieces
        (fun j : {i : Fin S.piece_count // S.kind i ≠ .survivor} => S.piece j.val)) A := by
  classical
  let Q := S.discardedAssembly
  let p := fun j : Fin R.count => pieces (R.index j)
  let q := fun j : Fin Q.count => S.piece (Q.index j).val
  have hq : ∀ j, Nonempty (q j).carrier := fun j =>
    ⟨(S.piece_connected (Q.index j).val).nonempty.choose⟩
  let D : SmoothDisjointUnionData q S.discardedCarrier := Q.assembly.disjoint_union
  let T : SmoothFiniteConnectedSumAssembly (Fin.append p q)
      (B.sum S.discardedCarrier) := {
    initial := R.assembly.initial.sum S.discardedCarrier
    disjoint_union := R.assembly.disjoint_union.append D
      (fun j => hpieces (R.index j)) hq
    operations := SmoothConnectedSumStep.reflTransGen_sumRight S.discardedCarrier
      R.assembly.operations }
  let e := finSumFinEquiv.symm.trans (Equiv.sumCongr R.index Q.index)
  refine ⟨R.count + Q.count, e, ?_⟩
  apply (T.compOperations S.splitDiffeomorph S.reconstruction.operations).reindexOfEq
    (Equiv.refl _)
  intro j
  cases j using Fin.addCases with
  | left j => simp [e, p, Fin.append_left]
  | right j => simp [e, q, Fin.append_right]

end PoincareMT
