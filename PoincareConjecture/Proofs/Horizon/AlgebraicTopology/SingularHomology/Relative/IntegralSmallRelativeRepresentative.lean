import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Relative.IntegralSmallRelativeChains
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.MayerVietoris.IntegralMayerVietoris
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.HomologicalAlgebra.ModuleComplexHomologyClass


set_option autoImplicit false

noncomputable section

open CategoryTheory HomologicalComplex

universe u v

namespace Poincare.Topology

theorem exists_integralSmallRelativeRepresentative_three
    {X : Type u} [TopologicalSpace X] {I : Type v}
    (U : I → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : (⋃ i, U i) = Set.univ) (A : Set X)
    (z : integralRelativeHomology A 3) :
    ∃ c : (integralChains X).X 3,
      c ∈ integralSmallChains U 3 ∧
      (integralChains X).d 3 2 c ∈
        LinearMap.range ((integralSubspaceChains A).f 2).hom ∧
      ∃ hcycle : (integralRelativeChains A).d 3 2
          ((integralRelativeProjection A).f 3 c) = 0,
        moduleComplexHomologyClass (integralRelativeChains A) 4 3 2
          (by simp) (by simp) ⟨(integralRelativeProjection A).f 3 c, hcycle⟩ = z := by
  let F := integralSmallRelativeComparison U A
  let : IsIso (homologyMap F 3) :=
    integralSmallRelativeComparison_homology_isIso U hU hcover A 3
  let e := asIso (homologyMap F 3)
  obtain ⟨r, hr⟩ := moduleComplexHomologyClass_surjective
    (integralSmallRelativeChains U A) 4 3 2 (by simp) (by simp) (e.inv z)
  obtain ⟨c, hc⟩ := integralProjection_surjective (integralSmallSubspaceChains U A) 3 r.val
  change (integralSmallChainComplex U).X 3 at c
  change (integralSmallRelativeProjection U A).f 3 c = r.val at hc
  let r' := moduleHomologyCycleMap
    ((shortComplexFunctor' (ModuleCat.{u} Int) (ComplexShape.down Nat) 4 3 2).map F) r
  have hval : r'.val = (integralRelativeProjection A).f 3 c.val := by
    change F.f 3 r.val = (integralRelativeProjection A).f 3 c.val
    rw [← hc]
    exact congrArg (fun f => f.f 3 c) (integralSmallRelativeComparison_projection U A)
  have hcycle : (integralRelativeChains A).d 3 2
      ((integralRelativeProjection A).f 3 c.val) = 0 := by
    rw [← hval]
    exact r'.property
  have hdc : (integralChains X).d 3 2 c.val ∈
      LinearMap.range ((integralSubspaceChains A).f 2).hom := by
    apply (integralProjection_eq_zero_iff (integralSubspaceChains A) 2 _).mp
    have hcomm := congrArg (fun f => f c.val) ((integralRelativeProjection A).comm 3 2)
    change (integralRelativeChains A).d 3 2
        ((integralRelativeProjection A).f 3 c.val) =
      (integralRelativeProjection A).f 2 ((integralChains X).d 3 2 c.val) at hcomm
    exact hcomm.symm.trans hcycle
  refine ⟨c.val, c.property, hdc, hcycle, ?_⟩
  have hclass : moduleComplexHomologyClass (integralRelativeChains A) 4 3 2
      (by simp) (by simp) r' = z := by
    rw [← moduleComplexHomologyClass_map F 4 3 2 (by simp) (by simp) r]
    exact (congrArg e.hom hr).trans (e.inv_hom_id_apply z)
  have hr' : (⟨(integralRelativeProjection A).f 3 c.val, hcycle⟩ :
      LinearMap.ker ((integralRelativeChains A).sc' 4 3 2).g.hom) = r' :=
    Subtype.ext hval.symm
  rw [hr']
  exact hclass

end Poincare.Topology
