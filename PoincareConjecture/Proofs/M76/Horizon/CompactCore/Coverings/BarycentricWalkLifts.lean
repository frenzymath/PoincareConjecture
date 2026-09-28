import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Coverings.BarycentricEdgePaths
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Coverings.CocycleWalkValue
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.GraphWalkPaths



set_option autoImplicit false

namespace AbstractSimplicialComplex

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (A : AbstractSimplicialComplex ι)

noncomputable def barycentricWalkPath {u v : ι} (w : A.edgeGraph.Walk u v) :
    Path (A.toPreAbstractSimplicialComplex.barycentricVertex u (A.singleton_mem u))
      (A.toPreAbstractSimplicialComplex.barycentricVertex v (A.singleton_mem v)) :=
  w.realizePath (fun u => A.toPreAbstractSimplicialComplex.barycentricVertex u
    (A.singleton_mem u)) (fun h => A.barycentricEdgePath h)

theorem exists_barycentricWalk_lift
    (c : A.toPreAbstractSimplicialComplex.ModTwoEdgeCocycle)
    {u v : ι} (w : A.edgeGraph.Walk u v) (b : ZMod 2) :
    ∃ L : Path
      ((c.bundle.localTriv u).toOpenPartialHomeomorph.symm
        (A.toPreAbstractSimplicialComplex.barycentricVertex u (A.singleton_mem u), b))
      ((c.bundle.localTriv v).toOpenPartialHomeomorph.symm
        (A.toPreAbstractSimplicialComplex.barycentricVertex v (A.singleton_mem v),
          b + c.walkValue w)),
      ∀ t, c.bundle.proj (L t) = A.barycentricWalkPath w t := by
  induction w generalizing b with
  | nil =>
    refine ⟨(Path.refl _).cast rfl (by simp [PreAbstractSimplicialComplex.ModTwoEdgeCocycle.walkValue]), ?_⟩
    intro t
    rfl
  | cons h w ih =>
    obtain ⟨P, hP⟩ := A.exists_barycentricEdge_lift c h b
    obtain ⟨Q, hQ⟩ := ih (b + c.value _ _)
    refine ⟨(P.trans Q).cast rfl (by
      simp only [PreAbstractSimplicialComplex.ModTwoEdgeCocycle.walkValue, add_assoc]), ?_⟩
    intro t
    change c.bundle.proj ((P.trans Q) t) =
      ((A.barycentricEdgePath h).trans (A.barycentricWalkPath w)) t
    simp only [Path.trans_apply]
    split_ifs
    · exact hP _
    · exact hQ _

end AbstractSimplicialComplex
