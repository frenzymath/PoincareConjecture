import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Counting.CocycleSingularValues
import Mathlib.Algebra.Field.ZMod








set_option autoImplicit false

open CategoryTheory Limits
open scoped Simplicial BigOperators

universe u

namespace PreAbstractSimplicialComplex.ModTwoEdgeCocycle

open PoincareConjecture.M76.CutGraph

variable {ι : Type u} [Fintype ι] {A : PreAbstractSimplicialComplex ι}

noncomputable def singularCochain (c : A.ModTwoEdgeCocycle) (R : ModuleCat.{u} (ZMod 2)) :
    ((TopCat.toSSet.obj (TopCat.of A.barycentricSpace)).chainComplex R).X 1 ⟶ R :=
  Sigma.desc (fun s => c.singularValue s • 𝟙 R)

theorem singularCochain_simplex (c : A.ModTwoEdgeCocycle) (R : ModuleCat.{u} (ZMod 2))
    (s : (TopCat.toSSet.obj (TopCat.of A.barycentricSpace)) _⦋1⦌) :
    (TopCat.toSSet.obj (TopCat.of A.barycentricSpace)).ιChainComplex s ≫
      c.singularCochain R = c.singularValue s • 𝟙 R := Sigma.ι_desc _ _

theorem boundary_singularCochain (c : A.ModTwoEdgeCocycle) (R : ModuleCat.{u} (ZMod 2)) :
    ((TopCat.toSSet.obj (TopCat.of A.barycentricSpace)).chainComplex R).d 2 1 ≫
      c.singularCochain R = 0 := by
  apply SSet.chainComplex_hom_ext
  intro s
  rw [← Category.assoc, SSet.ιChainComplex_d, Preadditive.sum_comp]
  simp only [Preadditive.zsmul_comp, singularCochain_simplex, comp_zero]
  simp_rw [← smul_assoc]
  rw [← Finset.sum_smul, c.singularValue_cocycle s, zero_smul]



noncomputable def homologyEvaluation (c : A.ModTwoEdgeCocycle)
    (R : ModuleCat.{u} (ZMod 2)) :
    (TopCat.toSSet.obj (TopCat.of A.barycentricSpace)).homology R 1 ⟶ R := by
  let C := (TopCat.toSSet.obj (TopCat.of A.barycentricSpace)).chainComplex R
  have h : C.toCycles 2 1 ≫ (C.iCycles 1 ≫ c.singularCochain R) = 0 := by
    rw [← Category.assoc, HomologicalComplex.toCycles_i]
    exact c.boundary_singularCochain R
  exact (C.homologyIsCokernel 2 1 (by simp)).desc
    (CokernelCofork.ofπ (C.iCycles 1 ≫ c.singularCochain R) h)

theorem homologyπ_evaluation (c : A.ModTwoEdgeCocycle) (R : ModuleCat.{u} (ZMod 2)) :
    ((TopCat.toSSet.obj (TopCat.of A.barycentricSpace)).chainComplex R).homologyπ 1 ≫
      c.homologyEvaluation R =
    ((TopCat.toSSet.obj (TopCat.of A.barycentricSpace)).chainComplex R).iCycles 1 ≫
      c.singularCochain R := by
  unfold homologyEvaluation
  exact Cofork.IsColimit.π_desc
    (((TopCat.toSSet.obj (TopCat.of A.barycentricSpace)).chainComplex R).homologyIsCokernel
      2 1 (by simp))

theorem singularCycleClass_evaluation (c : A.ModTwoEdgeCocycle)
    (R : ModuleCat.{u} (ZMod 2))
    {V I : Type*} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]
    (ends : I → Bool → V) (a : V → A.barycentricSpace)
    (p : ∀ i, Path (a (ends i false)) (a (ends i true)))
    (z : LinearMap.ker (incidenceBoundary (K := ZMod 2) ends)) :
    singularCycleClass R (TopCat.of A.barycentricSpace) ends a p z ≫
      c.homologyEvaluation R = (∑ i, z.val i * c.pathValue (p i)) • 𝟙 R := by
  change (singularCycleLift R (TopCat.of A.barycentricSpace) ends a p z ≫ _) ≫ _ = _
  rw [Category.assoc, homologyπ_evaluation, ← Category.assoc]
  dsimp only [singularCycleLift, LinearMap.coe_mk, AddHom.coe_mk]
  rw [HomologicalComplex.liftCycles_i]
  simp only [singularEdgeChain, LinearMap.sum_apply, LinearMap.smulRight_apply,
    LinearMap.proj_apply, Preadditive.sum_comp, Linear.smul_comp,
    singularCochain_simplex, singularValue_pathSimplex, smul_smul]
  exact Finset.sum_smul.symm

end PreAbstractSimplicialComplex.ModTwoEdgeCocycle
