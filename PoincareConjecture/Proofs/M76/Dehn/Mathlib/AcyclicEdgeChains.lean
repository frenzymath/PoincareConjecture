import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FiniteChainCoordinates
import Mathlib.Combinatorics.SimpleGraph.Acyclic

set_option autoImplicit false

open scoped BigOperators

namespace PreAbstractSimplicialComplex.ModTwoCochains

variable {ι : Type*} (A : PreAbstractSimplicialComplex ι)

open Classical in

def edgeInGraph (T : SimpleGraph ι) (e : Edge A) : Prop :=
  ∃ u v, T.Adj u v ∧ e.val = {u, v}

open Classical in

theorem reachableCut_value_eq (G : SimpleGraph ι) (u : ι) {v w : ι}
    (hvw : G.Adj v w) :
    (if G.Reachable u v then (1 : ZMod 2) else 0) =
      (if G.Reachable u w then (1 : ZMod 2) else 0) := by
  have h : G.Reachable u v ↔ G.Reachable u w :=
    ⟨fun h => h.trans hvw.reachable, fun h => h.trans hvw.symm.reachable⟩
  rw [h]

variable [Finite ι]

open Classical in

theorem edgeChain_eq_zero_of_acyclic_support (T : SimpleGraph ι) (hT : T.IsAcyclic)
    (c : Module.Dual (ZMod 2) (Edge A → ZMod 2))
    (hc : (vertexCoboundary A).dualMap c = 0)
    (hsupport : ∀ e : Edge A, ¬edgeInGraph A T e → c (Pi.single e 1) = 0) : c = 0 := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  apply (Pi.basisFun (ZMod 2) (Edge A)).ext
  intro e
  rw [Pi.basisFun_apply]
  change c (Pi.single e 1) = 0
  by_cases heT : edgeInGraph A T e
  · obtain ⟨u, v, huv, he⟩ := heT
    let G := T.deleteEdges {s(u, v)}
    have hnot : ¬G.Reachable u v :=
      SimpleGraph.isBridge_iff.mp (SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp hT huv)
    let a : ι → ZMod 2 := fun w => if G.Reachable u w then 1 else 0
    have hae : vertexCoboundary A a e = 1 := by
      rw [vertexCoboundary_apply, he, Finset.sum_pair huv.ne]
      simp only [a, if_pos (SimpleGraph.Reachable.refl u), if_neg hnot, add_zero]
    have haq (q : Edge A) (hqT : edgeInGraph A T q) (hqe : q ≠ e) :
        vertexCoboundary A a q = 0 := by
      obtain ⟨w, z, hwz, hq⟩ := hqT
      have hadj : G.Adj w z := by
        apply SimpleGraph.deleteEdges_adj.mpr
        refine ⟨hwz, ?_⟩
        simp only [Set.mem_singleton_iff]
        intro hpair
        apply hqe
        apply Subtype.ext
        have hp := congrArg Sym2.toFinset hpair
        simp only [Sym2.toFinset_mk_eq] at hp
        exact hq.trans (hp.trans he.symm)
      have hav : a w = a z := reachableCut_value_eq G u hadj
      rw [vertexCoboundary_apply, hq, Finset.sum_pair hwz.ne, hav]
      exact CharTwo.add_self_eq_zero (a z)
    have hzero := congrArg (fun d : Module.Dual (ZMod 2) (ι → ZMod 2) => d a) hc
    change c (vertexCoboundary A a) = 0 at hzero
    rw [dual_apply_eq_sum_coordinates] at hzero
    have hsum : (∑ q : Edge A, vertexCoboundary A a q * c (Pi.single q 1)) =
        c (Pi.single e 1) := by
      calc
        _ = vertexCoboundary A a e * c (Pi.single e 1) := by
          apply Finset.sum_eq_single e
          · intro q _ hqe
            by_cases hqT : edgeInGraph A T q
            · rw [haq q hqT hqe, zero_mul]
            · rw [hsupport q hqT, mul_zero]
          · simp
        _ = c (Pi.single e 1) := by rw [hae, one_mul]
    exact hsum.symm.trans hzero
  · exact hsupport e heT

end PreAbstractSimplicialComplex.ModTwoCochains
