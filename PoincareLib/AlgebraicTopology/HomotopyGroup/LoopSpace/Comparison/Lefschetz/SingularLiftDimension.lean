import PoincareLib.AlgebraicTopology.HomotopyGroup.LoopSpace.Comparison.Lefschetz.SingularLift

/-!
# Coverings reflect degeneracy of lifted simplices

A degenerate base simplex factors through a simplex degeneracy. A candidate
factorization of its lift is obtained by restricting to the corresponding
face. It agrees with the original lift on that face, and covering uniqueness
then gives equality on the whole simplex. Thus lifting does not increase
the dimension of the finite model.
Source: Hatcher, Proposition 1.33, pp. 61-62, and Theorem 2.27, pp. 128-130.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits
open scoped Simplicial

universe u

namespace PoincareMT.Proofs.M59

variable {E X : Type u} [TopologicalSpace E] [TopologicalSpace X]
  (p : C(E, X))

/-- Two simplex lifts with the same projection and one equal face agree.
Source: uniqueness of lifts, Hatcher, Proposition 1.34, p. 62. -/
theorem singular_simplex_eq_of_projection_and_face
    (hp : IsCoveringMap p) {n : ℕ}
    (s t : (TopCat.toSSet.obj (TopCat.of E)) _⦋n + 1⦌) (i : Fin (n + 2))
    (hproj : (TopCat.toSSet.map (TopCat.ofHom p)).app _ s =
      (TopCat.toSSet.map (TopCat.ofHom p)).app _ t)
    (hface : (TopCat.toSSet.obj (TopCat.of E)).δ i s =
      (TopCat.toSSet.obj (TopCat.of E)).δ i t) : s = t := by
  apply ((TopCat.of E).toSSetObjEquiv _).injective
  apply ContinuousMap.coe_injective
  have hpoint := congrArg
    (fun z => (TopCat.of E).toSSetObjEquiv _ z (stdSimplex.vertex 0)) hface
  apply hp.eq_of_comp_eq ((TopCat.of E).toSSetObjEquiv _ s).continuous
    ((TopCat.of E).toSSetObjEquiv _ t).continuous _ _ hpoint
  exact congrArg (fun z => ((TopCat.of X).toSSetObjEquiv _ z).toFun) hproj

variable (A : SSet.{u}) (χ : A ⟶ TopCat.toSSet.obj (TopCat.of X))

/-- A lifted simplex with degenerate projection is degenerate.
Source: Hatcher, Proposition 1.34, p. 62, applied to simplices. -/
theorem singularLift_degenerate_of_base_degenerate (hp : IsCoveringMap p)
    {n : ℕ} (z : (singularLiftSSet p A χ) _⦋n⦌)
    (hbase : z.val.1 ∈ A.degenerate n) :
    z ∈ (singularLiftSSet p A χ).degenerate n := by
  cases n with
  | zero => simp only [SSet.degenerate_zero, Set.mem_empty_iff_false] at hbase
  | succ n =>
      let D := singularLiftSSet p A χ
      rw [SSet.degenerate_eq_iUnion_range_σ, Set.mem_iUnion] at hbase ⊢
      obtain ⟨i, s, hs⟩ := hbase
      let w := D.δ i.castSucc z
      have hbase' : (D.σ i w).val.1 = z.val.1 := by
        change A.σ i (A.δ i.castSucc z.val.1) = z.val.1
        rw [← hs, A.δ_comp_σ_self_apply]
      refine ⟨i, w, ?_⟩
      apply Subtype.ext
      apply Prod.ext hbase'
      apply singular_simplex_eq_of_projection_and_face p hp _ _ i.castSucc
      · exact (D.σ i w).property.trans
          ((congrArg (fun s => χ.app _ s) hbase').trans z.property.symm)
      · change (TopCat.toSSet.obj (TopCat.of E)).δ i.castSucc
          ((TopCat.toSSet.obj (TopCat.of E)).σ i w.val.2) =
            (TopCat.toSSet.obj (TopCat.of E)).δ i.castSucc z.val.2
        rw [SSet.δ_comp_σ_self_apply]
        rfl

/-- Every nondegenerate lifted simplex projects to a nondegenerate
base simplex. Source: Hatcher, Theorem 2.27, pp. 128-130. -/
theorem singularLift_nonDegenerate_base (hp : IsCoveringMap p)
    {n : ℕ} (z : (singularLiftSSet p A χ).nonDegenerate n) :
    z.val.val.1 ∈ A.nonDegenerate n := by
  by_contra h
  have hd := singularLift_degenerate_of_base_degenerate p A χ hp z.val
    ((A.mem_degenerate_iff_notMem_nonDegenerate _).mpr h)
  exact ((singularLiftSSet p A χ).mem_degenerate_iff_notMem_nonDegenerate _).mp hd z.property

/-- A covering preserves every finite dimension bound on the lifted
simplicial model. Source: Hatcher, Theorem 2.27, pp. 128-130. -/
theorem singularLift_hasDimensionLT (hp : IsCoveringMap p) (d : ℕ)
    [A.HasDimensionLT d] : (singularLiftSSet p A χ).HasDimensionLT d where
  degenerate_eq_top n hn := by
    apply Set.eq_univ_of_forall
    intro z
    apply singularLift_degenerate_of_base_degenerate p A χ hp z
    rw [A.degenerate_eq_univ_of_hasDimensionLT d n hn]
    exact Set.mem_univ _

end PoincareMT.Proofs.M59
