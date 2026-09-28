import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Coverings.BarycentricWalkLifts









set_option autoImplicit false

theorem IsCoveringMap.not_homotopic_refl_of_lift_ne
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {f : E → X}
    (hf : IsCoveringMap f) {x : X} {a b : E} (p : Path x x) (L : Path a b)
    (hL : ∀ t, f (L t) = p t) (hne : a ≠ b) : ¬p.Homotopic (Path.refl x) := by
  intro hp
  have hzero : p 0 = f a := by simpa using (hL 0).symm
  have hx : x = f a := by simpa using hzero
  have heq : L.toContinuousMap = hf.liftPath p.toContinuousMap a hzero :=
    (hf.eq_liftPath_iff' hzero).mpr ⟨funext hL, L.source⟩
  have hend := hf.liftPath_apply_one_eq_of_homotopicRel hp a hzero hx
  rw [← heq] at hend
  change L 1 = hf.liftPath (ContinuousMap.const unitInterval x) a hx 1 at hend
  rw [hf.liftPath_const hx] at hend
  exact hne (by simpa using hend.symm)

namespace AbstractSimplicialComplex

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (A : AbstractSimplicialComplex ι)

theorem barycentricWalk_not_homotopic_refl_of_value_ne_zero
    (c : A.toPreAbstractSimplicialComplex.ModTwoEdgeCocycle)
    {u : ι} (w : A.edgeGraph.Walk u u) (hw : c.walkValue w ≠ 0) :
    ¬(A.barycentricWalkPath w).Homotopic (Path.refl _) := by
  obtain ⟨L, hL⟩ := A.exists_barycentricWalk_lift c w 0
  apply c.isCoveringMap.not_homotopic_refl_of_lift_ne (A.barycentricWalkPath w) L hL
  intro heq
  have hcoord := congrArg (c.bundle.localTriv u).toOpenPartialHomeomorph heq
  have hmem := A.toPreAbstractSimplicialComplex.barycentricVertex_mem_openVertexStar
    u (A.singleton_mem u)
  have hleft (b : ZMod 2) := (c.bundle.localTriv u).toOpenPartialHomeomorph.right_inv
    (show (A.toPreAbstractSimplicialComplex.barycentricVertex u (A.singleton_mem u), b) ∈
      (c.bundle.localTriv u).target from ⟨hmem, Set.mem_univ _⟩)
  rw [hleft, hleft] at hcoord
  exact hw (by simpa using (congrArg Prod.snd hcoord).symm)

end AbstractSimplicialComplex
