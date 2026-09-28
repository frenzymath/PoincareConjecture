import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Duality.CapProduct.IntegralSupportCapHomology
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Cohomology.IntegralCochains
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.MayerVietoris.IntegralSupportMayerVietoris
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.HomologicalAlgebra.ModuleComplexHomologyClass

set_option autoImplicit false

noncomputable section

open CategoryTheory HomologicalComplex

universe u

namespace Poincare.Topology

variable {X : Type u} [TopologicalSpace X]

private theorem supportRelativeMap_id_eq_restriction {K L : Set X} (h : K ⊆ L) :
    integralRelativeMap (ContinuousMap.id X)
        (show Set.MapsTo (ContinuousMap.id X) Lᶜ Kᶜ from fun _ hx hKL => hx (h hKL)) =
      integralSupportRestriction h := by
  apply (cancel_epi (integralRelativeProjection Lᶜ)).mp
  rw [integralRelativeMap_projection, integralSupportRestriction_projection]
  simp

private theorem supportCochainPushforward_eq_dualMap {K L : Set X} (h : K ⊆ L) :
    integralSupportCohomologyPushforward h 1 =
      homologyMap (integralDualMap
        (integralRelativeMap (ContinuousMap.id X)
          (show Set.MapsTo (ContinuousMap.id X) Lᶜ Kᶜ from
            fun _ hx hKL => hx (h hKL)))) 1 := rfl

theorem integralSupportCapHomologyOne_naturality
    {K L : Set X} (h : K ⊆ L)
    (z : integralSupportHomology L 3)
    (phi : integralSupportCohomology K 1) :
    integralSupportCapHomologyOne Lᶜ z
        (integralSupportCohomologyPushforward h 1 phi) =
      integralSupportCapHomologyOne Kᶜ
        (integralSupportHomologyRestriction h 3 z) phi := by
  obtain ⟨cz, hcz⟩ := moduleComplexHomologyClass_surjective
    (integralRelativeChains Lᶜ) 4 3 2 (by simp) (by simp) z
  obtain ⟨cphi, hcphi⟩ := moduleComplexHomologyClass_surjective
    (integralRelativeCochains Kᶜ) 0 1 2 (by simp) (by simp) phi
  let f : integralRelativeChains Lᶜ ⟶ integralRelativeChains Kᶜ :=
    integralRelativeMap (ContinuousMap.id X)
      (show Set.MapsTo (ContinuousMap.id X) Lᶜ Kᶜ from
        fun _ hx hKL => hx (h hKL))
  let g : integralRelativeCochains Kᶜ ⟶ integralRelativeCochains Lᶜ :=
    integralDualMap f
  have hf : homologyMap f 3 = integralSupportHomologyRestriction h 3 := by
    dsimp [f]
    rw [supportRelativeMap_id_eq_restriction h]
    rfl
  have hg : homologyMap g 1 = integralSupportCohomologyPushforward h 1 := by
    rfl
  have hcz' :
      moduleComplexHomologyClass (integralRelativeChains Kᶜ) 4 3 2 (by simp) (by simp)
          (moduleHomologyCycleMap
            ((shortComplexFunctor' (ModuleCat.{u} Int) (ComplexShape.down Nat) 4 3 2).map f) cz) =
        integralSupportHomologyRestriction h 3 z := by
    rw [← hcz, ← hf]
    exact (moduleComplexHomologyClass_map f 4 3 2 (by simp) (by simp) cz).symm
  have hcphi' :
      moduleComplexHomologyClass (integralRelativeCochains Lᶜ) 0 1 2 (by simp) (by simp)
          (moduleHomologyCycleMap
            ((shortComplexFunctor' (ModuleCat.{u} Int) (ComplexShape.up Nat) 0 1 2).map g) cphi) =
        integralSupportCohomologyPushforward h 1 phi := by
    rw [← hcphi, ← hg]
    exact (moduleComplexHomologyClass_map g 0 1 2 (by simp) (by simp) cphi).symm
  have hres :
      integralSupportHomologyRestriction h 3
          (moduleComplexHomologyClass (integralRelativeChains Lᶜ) 4 3 2
            (by simp) (by simp) cz) =
        moduleComplexHomologyClass (integralRelativeChains Kᶜ) 4 3 2
          (by simp) (by simp)
          (moduleHomologyCycleMap
            ((shortComplexFunctor' (ModuleCat.{u} Int) (ComplexShape.down Nat) 4 3 2).map f)
              cz) := by
    simpa [hcz] using hcz'.symm
  have hpush :
      integralSupportCohomologyPushforward h 1
          (moduleComplexHomologyClass (integralRelativeCochains Kᶜ) 0 1 2
            (by simp) (by simp) cphi) =
        moduleComplexHomologyClass (integralRelativeCochains Lᶜ) 0 1 2
          (by simp) (by simp)
          (moduleHomologyCycleMap
            ((shortComplexFunctor' (ModuleCat.{u} Int) (ComplexShape.up Nat) 0 1 2).map g)
              cphi) := by
    simpa [hcphi] using hcphi'.symm
  rw [← hcz, ← hcphi, hpush, hres]
  simp only [moduleComplexHomologyClass]
  rw [integralSupportCapHomologyOne_class, integralSupportCapHomologyOne_class]
  apply congrArg (fun t =>
    ((integralChains X).homologyIsoSc' 3 2 1 (by simp) (by simp)).inv t)
  change moduleHomologyClass ((integralChains X).sc' 3 2 1)
      ⟨integralSupportCap Lᶜ 2 1 cz.val
          (moduleHomologyCycleMap
            ((shortComplexFunctor' (ModuleCat.{u} Int) (ComplexShape.up Nat) 0 1 2).map g)
              cphi).val,
        ?_⟩ = _
  congr 1
  apply Subtype.ext
  change integralSupportCap Lᶜ 2 1 cz.val (g.f 1 cphi.val) =
    integralSupportCap Kᶜ 2 1 (f.f 3 cz.val) cphi.val
  have hn := integralSupportCap_naturality (X := X) (Y := X)
    (ContinuousMap.id X)
    (show Set.MapsTo (ContinuousMap.id X) Lᶜ Kᶜ from
      fun _ hx hKL => hx (h hKL)) 2 1 cz.val cphi.val
  simpa [f, g, supportRelativeMap_id_eq_restriction h] using hn

theorem integralSupportCapHomologyTwo_naturality
    {K L : Set X} (h : K ⊆ L)
    (z : integralSupportHomology L 3)
    (phi : integralSupportCohomology K 2) :
    integralSupportCapHomologyTwo Lᶜ z
        (integralSupportCohomologyPushforward h 2 phi) =
      integralSupportCapHomologyTwo Kᶜ
        (integralSupportHomologyRestriction h 3 z) phi := by
  obtain ⟨cz, hcz⟩ := moduleComplexHomologyClass_surjective
    (integralRelativeChains Lᶜ) 4 3 2 (by simp) (by simp) z
  obtain ⟨cphi, hcphi⟩ := moduleComplexHomologyClass_surjective
    (integralRelativeCochains Kᶜ) 1 2 3 (by simp) (by simp) phi
  let f : integralRelativeChains Lᶜ ⟶ integralRelativeChains Kᶜ :=
    integralRelativeMap (ContinuousMap.id X)
      (show Set.MapsTo (ContinuousMap.id X) Lᶜ Kᶜ from
        fun _ hx hKL => hx (h hKL))
  let g : integralRelativeCochains Kᶜ ⟶ integralRelativeCochains Lᶜ :=
    integralDualMap f
  have hf : homologyMap f 3 = integralSupportHomologyRestriction h 3 := by
    dsimp [f]
    rw [supportRelativeMap_id_eq_restriction h]
    rfl
  have hg : homologyMap g 2 = integralSupportCohomologyPushforward h 2 := by
    rfl
  have hcz' :
      moduleComplexHomologyClass (integralRelativeChains Kᶜ) 4 3 2 (by simp) (by simp)
          (moduleHomologyCycleMap
            ((shortComplexFunctor' (ModuleCat.{u} Int) (ComplexShape.down Nat) 4 3 2).map f) cz) =
        integralSupportHomologyRestriction h 3 z := by
    rw [← hcz]
    exact (moduleComplexHomologyClass_map f 4 3 2 (by simp) (by simp) cz).symm.trans
      (by rw [hf])
  have hcphi' :
      moduleComplexHomologyClass (integralRelativeCochains Lᶜ) 1 2 3 (by simp) (by simp)
          (moduleHomologyCycleMap
            ((shortComplexFunctor' (ModuleCat.{u} Int) (ComplexShape.up Nat) 1 2 3).map g) cphi) =
        integralSupportCohomologyPushforward h 2 phi := by
    rw [← hcphi, ← hg]
    exact (moduleComplexHomologyClass_map g 1 2 3 (by simp) (by simp) cphi).symm
  have hres :
      integralSupportHomologyRestriction h 3
          (moduleComplexHomologyClass (integralRelativeChains Lᶜ) 4 3 2
            (by simp) (by simp) cz) =
        moduleComplexHomologyClass (integralRelativeChains Kᶜ) 4 3 2
          (by simp) (by simp)
          (moduleHomologyCycleMap
            ((shortComplexFunctor' (ModuleCat.{u} Int) (ComplexShape.down Nat) 4 3 2).map f)
              cz) := by
    simpa [hcz] using hcz'.symm
  have hpush :
      integralSupportCohomologyPushforward h 2
          (moduleComplexHomologyClass (integralRelativeCochains Kᶜ) 1 2 3
            (by simp) (by simp) cphi) =
        moduleComplexHomologyClass (integralRelativeCochains Lᶜ) 1 2 3
          (by simp) (by simp)
          (moduleHomologyCycleMap
            ((shortComplexFunctor' (ModuleCat.{u} Int) (ComplexShape.up Nat) 1 2 3).map g)
              cphi) := by
    simpa [hcphi] using hcphi'.symm
  rw [← hcz, ← hcphi, hpush, hres]
  simp only [moduleComplexHomologyClass]
  rw [integralSupportCapHomologyTwo_class, integralSupportCapHomologyTwo_class]
  apply congrArg (fun t =>
    ((integralChains X).homologyIsoSc' 2 1 0 (by simp) (by simp)).inv t)
  change moduleHomologyClass ((integralChains X).sc' 2 1 0)
      ⟨integralSupportCap Lᶜ 1 2 cz.val
          (moduleHomologyCycleMap
            ((shortComplexFunctor' (ModuleCat.{u} Int) (ComplexShape.up Nat) 1 2 3).map g)
              cphi).val,
        ?_⟩ = _
  congr 1
  apply Subtype.ext
  change integralSupportCap Lᶜ 1 2 cz.val (g.f 2 cphi.val) =
    integralSupportCap Kᶜ 1 2 (f.f 3 cz.val) cphi.val
  have hn := integralSupportCap_naturality (X := X) (Y := X)
    (ContinuousMap.id X)
    (show Set.MapsTo (ContinuousMap.id X) Lᶜ Kᶜ from
      fun _ hx hKL => hx (h hKL)) 1 2 cz.val cphi.val
  simpa [f, g, supportRelativeMap_id_eq_restriction h] using hn

theorem integralSupportCapHomologyThree_naturality
    {K L : Set X} (h : K ⊆ L)
    (z : integralSupportHomology L 3)
    (phi : integralSupportCohomology K 3) :
    integralSupportCapHomologyThree Lᶜ z
        (integralSupportCohomologyPushforward h 3 phi) =
      integralSupportCapHomologyThree Kᶜ
        (integralSupportHomologyRestriction h 3 z) phi := by
  obtain ⟨cz, hcz⟩ := moduleComplexHomologyClass_surjective
    (integralRelativeChains Lᶜ) 4 3 2 (by simp) (by simp) z
  obtain ⟨cphi, hcphi⟩ := moduleComplexHomologyClass_surjective
    (integralRelativeCochains Kᶜ) 2 3 4 (by simp) (by simp) phi
  let f : integralRelativeChains Lᶜ ⟶ integralRelativeChains Kᶜ :=
    integralRelativeMap (ContinuousMap.id X)
      (show Set.MapsTo (ContinuousMap.id X) Lᶜ Kᶜ from
        fun _ hx hKL => hx (h hKL))
  let g : integralRelativeCochains Kᶜ ⟶ integralRelativeCochains Lᶜ :=
    integralDualMap f
  have hf : homologyMap f 3 = integralSupportHomologyRestriction h 3 := by
    dsimp [f]
    rw [supportRelativeMap_id_eq_restriction h]
    rfl
  have hg : homologyMap g 3 = integralSupportCohomologyPushforward h 3 := by
    rfl
  have hcz' :
      moduleComplexHomologyClass (integralRelativeChains Kᶜ) 4 3 2 (by simp) (by simp)
          (moduleHomologyCycleMap
            ((shortComplexFunctor' (ModuleCat.{u} Int) (ComplexShape.down Nat) 4 3 2).map f) cz) =
        integralSupportHomologyRestriction h 3 z := by
    rw [← hcz]
    exact (moduleComplexHomologyClass_map f 4 3 2 (by simp) (by simp) cz).symm.trans
      (by rw [hf])
  have hcphi' :
      moduleComplexHomologyClass (integralRelativeCochains Lᶜ) 2 3 4 (by simp) (by simp)
          (moduleHomologyCycleMap
            ((shortComplexFunctor' (ModuleCat.{u} Int) (ComplexShape.up Nat) 2 3 4).map g) cphi) =
        integralSupportCohomologyPushforward h 3 phi := by
    rw [← hcphi, ← hg]
    exact (moduleComplexHomologyClass_map g 2 3 4 (by simp) (by simp) cphi).symm
  have hres :
      integralSupportHomologyRestriction h 3
          (moduleComplexHomologyClass (integralRelativeChains Lᶜ) 4 3 2
            (by simp) (by simp) cz) =
        moduleComplexHomologyClass (integralRelativeChains Kᶜ) 4 3 2
          (by simp) (by simp)
          (moduleHomologyCycleMap
            ((shortComplexFunctor' (ModuleCat.{u} Int) (ComplexShape.down Nat) 4 3 2).map f)
              cz) := by
    simpa [hcz] using hcz'.symm
  have hpush :
      integralSupportCohomologyPushforward h 3
          (moduleComplexHomologyClass (integralRelativeCochains Kᶜ) 2 3 4
            (by simp) (by simp) cphi) =
        moduleComplexHomologyClass (integralRelativeCochains Lᶜ) 2 3 4
          (by simp) (by simp)
          (moduleHomologyCycleMap
            ((shortComplexFunctor' (ModuleCat.{u} Int) (ComplexShape.up Nat) 2 3 4).map g)
              cphi) := by
    simpa [hcphi] using hcphi'.symm
  rw [← hcz, ← hcphi, hpush, hres]
  simp only [moduleComplexHomologyClass]
  rw [integralSupportCapHomologyThree_class, integralSupportCapHomologyThree_class]
  apply congrArg (fun t =>
    ((integralChains X).homologyIsoSc' 1 0 0 (by simp) (by simp)).inv t)
  change moduleHomologyClass ((integralChains X).sc' 1 0 0)
      ⟨integralSupportCap Lᶜ 0 3 cz.val
          (moduleHomologyCycleMap
            ((shortComplexFunctor' (ModuleCat.{u} Int) (ComplexShape.up Nat) 2 3 4).map g)
              cphi).val,
        ?_⟩ = _
  congr 1
  apply Subtype.ext
  change integralSupportCap Lᶜ 0 3 cz.val (g.f 3 cphi.val) =
    integralSupportCap Kᶜ 0 3 (f.f 3 cz.val) cphi.val
  have hn := integralSupportCap_naturality (X := X) (Y := X)
    (ContinuousMap.id X)
    (show Set.MapsTo (ContinuousMap.id X) Lᶜ Kᶜ from
      fun _ hx hKL => hx (h hKL)) 0 3 cz.val cphi.val
  simpa [f, g, supportRelativeMap_id_eq_restriction h] using hn

end Poincare.Topology
