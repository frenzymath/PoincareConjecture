import PoincareConjecture.Proofs.M72.Cor15_4_Assembly.SliceDecomposition
import PoincareConjecture.Proofs.M72.Cor15_4_Assembly.DisjointUnionSum
import PoincareConjecture.Proofs.M72.Cor15_4_Assembly.StepLift
import PoincareConjecture.Proofs.M72.Cor15_4_Assembly.SourceTransport

set_option autoImplicit false

open scoped Manifold ContDiff Topology

universe u v

namespace PoincareConjecture

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

end PoincareConjecture
