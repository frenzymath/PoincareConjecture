import PoincareConjecture.Proofs.M59.Mathlib.Lefschetz.TraceExact
import PoincareConjecture.Proofs.M02.Topology.IntegralHomologyZero
import PoincareConjecture.Proofs.M02.Topology.IntegralThreeManifoldTop
import PoincareConjecture.Proofs.M02.HurewiczRepresentatives
import PoincareConjecture.Statements.M40ComparisonHomotopy
import Mathlib.LinearAlgebra.Dimension.Free











set_option autoImplicit false

noncomputable section

open CategoryTheory Limits HomologicalComplex
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Proofs.M59

open M02 M02.Topology



theorem compactThree_integralHomology_two_isZero
    (P02 : RepairedClosedTopologyProvider.{u})
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [SecondCountableTopology M]
    [CompactSpace M] [SimplyConnectedSpace M] :
    IsZero (integralHomology M 2) := by
  obtain ⟨T⟩ := P02 (M := M)
  apply isZero_integral_singularHomology_of_homotopy_vanishing
    (TopCat.of M) T.basepoint 1
  intro k hk hkn
  have hcases : k = 1 ∨ k = 2 := by omega
  rcases hcases with rfl | rfl
  · exact HomotopyGroup.pi1EquivFundamentalGroup.injective.subsingleton
  · exact T.pi_two_subsingleton




theorem compactThree_integralHomology_above_isZero
    {M : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] (n : ℕ) :
    IsZero (integralHomology M (n + 4)) := by
  exact ((integralThreeManifoldCompactSupport (Set.univ : Set M)
    isCompact_univ).1 n).of_iso (integralHomologySupportUnivIso M (n + 4))




theorem compactThree_integralHomology_isZero
    (P02 : RepairedClosedTopologyProvider.{u})
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [SecondCountableTopology M]
    [CompactSpace M] [SimplyConnectedSpace M]
    (n : ℕ) (hzero : n ≠ 0) (hthree : n ≠ 3) :
    IsZero (integralHomology M n) := by
  rcases n with _ | n
  · exact (hzero rfl).elim
  rcases n with _ | n
  · exact isZero_integral_singularHomology_one (TopCat.of M)
  rcases n with _ | n
  · exact compactThree_integralHomology_two_isZero P02
  rcases n with _ | n
  · exact (hthree rfl).elim
  · exact compactThree_integralHomology_above_isZero n




theorem compactThree_integralHomology_free
    (P02 : RepairedClosedTopologyProvider.{u})
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [SecondCountableTopology M]
    [CompactSpace M] [SimplyConnectedSpace M] (n : ℕ) :
    Module.Free ℤ (integralHomology M n) := by
  classical
  by_cases hzero : n = 0
  · subst n
    let := integralHomologyZeroAugmentation_isIso M
    exact Module.Free.of_equiv (asIso (integralHomologyZeroAugmentation M)).toLinearEquiv.symm
  by_cases hthree : n = 3
  · subst n
    obtain ⟨e⟩ := nonempty_integralThreeManifoldTop_equiv_int
      (Classical.choice (inferInstance : Nonempty M))
    exact Module.Free.of_equiv e.symm
  · let := ModuleCat.isZero_iff_subsingleton.mp
      (compactThree_integralHomology_isZero P02 (M := M) n hzero hthree)
    exact Module.Free.of_subsingleton ℤ (integralHomology M n)



theorem compactThree_integralHomology_finite
    (P02 : RepairedClosedTopologyProvider.{u})
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [SecondCountableTopology M]
    [CompactSpace M] [SimplyConnectedSpace M] (n : ℕ) :
    Module.Finite ℤ (integralHomology M n) := by
  classical
  by_cases hzero : n = 0
  · subst n
    let := integralHomologyZeroAugmentation_isIso M
    exact Module.Finite.of_surjective
      (asIso (integralHomologyZeroAugmentation M)).inv.hom
      (asIso (integralHomologyZeroAugmentation M)).toLinearEquiv.symm.surjective
  by_cases hthree : n = 3
  · subst n
    obtain ⟨e⟩ := nonempty_integralThreeManifoldTop_equiv_int
      (Classical.choice (inferInstance : Nonempty M))
    exact Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective
  · let := ModuleCat.isZero_iff_subsingleton.mp
      (compactThree_integralHomology_isZero P02 (M := M) n hzero hthree)
    infer_instance




theorem trace_integralHomologyMap_zero
    {X : Type u} [TopologicalSpace X] [PathConnectedSpace X] (f : C(X, X)) :
    LinearMap.trace ℤ (integralHomology X 0)
      (homologyMap (integralChainsFunctor.map (TopCat.ofHom f)) 0).hom = 1 := by
  let := integralHomologyZeroAugmentation_isIso X
  let e := asIso (integralHomologyZeroAugmentation X)
  let := Module.Free.of_equiv e.toLinearEquiv.symm
  let := Module.Finite.of_surjective e.inv.hom e.toLinearEquiv.symm.surjective
  rw [ModuleCat.trace_eq_of_iso e _ (𝟙 _) (by
    rw [Category.comp_id]
    change _ ≫ integralHomologyZeroAugmentation X = integralHomologyZeroAugmentation X
    exact integralHomologyZeroAugmentation_natural f)]
  change LinearMap.trace ℤ (ULift.{u} ℤ) LinearMap.id = 1
  simp only [LinearMap.trace_id, finrank_ulift, Module.finrank_self, Nat.cast_one]

set_option backward.isDefEq.respectTransparency false in


theorem compactThree_homologyMap_eq_id_of_trace_one
    {M : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [SimplyConnectedSpace M]
    (f : C(M, M))
    (h : LinearMap.trace ℤ (integralHomology M 3)
      (homologyMap (integralChainsFunctor.map (TopCat.ofHom f)) 3).hom = 1) :
    surgeryThirdHomologyMap f = LinearMap.id := by
  obtain ⟨e⟩ := nonempty_integralThreeManifoldTop_equiv_int
    (Classical.choice (inferInstance : Nonempty M))
  let := Module.Free.of_equiv e.symm
  let := Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective
  have hrank : Module.finrank ℤ (integralHomology M 3) = 1 := by
    rw [e.finrank_eq, Module.finrank_self]
  let F := (homologyMap (integralChainsFunctor.map (TopCat.ofHom f)) 3).hom
  obtain ⟨c, hc, _⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hrank F
  have hc1 : c = 1 := by
    change LinearMap.trace ℤ (integralHomology M 3) F = 1 at h
    simpa only [hc, map_smul, LinearMap.trace_id, hrank, Nat.cast_one, smul_eq_mul,
      mul_one] using h
  change F = LinearMap.id
  rw [hc, hc1]
  ext z
  simp only [LinearMap.smul_apply, LinearMap.id_apply, one_smul]

end PoincareConjecture.Proofs.M59
