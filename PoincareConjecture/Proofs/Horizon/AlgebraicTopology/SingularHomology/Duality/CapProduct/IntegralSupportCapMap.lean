import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Duality.CapProduct.IntegralSupportCapHomology
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Duality.CapProduct.IntegralSupportCapNaturality
set_option autoImplicit false

noncomputable section

open CategoryTheory HomologicalComplex

universe u

namespace Poincare.Topology

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem integralSupportCapHomologyOne_map
    (f : C(X, Y)) {A : Set X} {B : Set Y} (hf : Set.MapsTo f A B)
    (z : integralRelativeHomology A 3) (phi : integralRelativeCohomology B 1) :
    homologyMap (integralChainsFunctor.map (TopCat.ofHom f)) 2
        (integralSupportCapHomologyOne A z
          (homologyMap (integralDualMap (integralRelativeMap f hf)) 1 phi)) =
      integralSupportCapHomologyOne B
        (homologyMap (integralRelativeMap f hf) 3 z) phi := by
  obtain ⟨cz, hcz⟩ := moduleComplexHomologyClass_surjective
    (integralRelativeChains A) 4 3 2 (by simp) (by simp) z
  obtain ⟨cphi, hcphi⟩ := moduleComplexHomologyClass_surjective
    (integralRelativeCochains B) 0 1 2 (by simp) (by simp) phi
  let fr := integralRelativeMap f hf
  let g := integralDualMap fr
  let F := integralChainsFunctor.map (TopCat.ofHom f)
  rw [← hcz, ← hcphi]
  have hres := moduleComplexHomologyClass_map fr 4 3 2 (by simp) (by simp) cz
  have hpush := moduleComplexHomologyClass_map g 0 1 2 (by simp) (by simp) cphi
  rw [hres, hpush]
  let phix := moduleHomologyCycleMap
    ((shortComplexFunctor' (ModuleCat.{u} Int) (ComplexShape.up Nat) 0 1 2).map g) cphi
  let zy := moduleHomologyCycleMap
    ((shortComplexFunctor' (ModuleCat.{u} Int) (ComplexShape.down Nat) 4 3 2).map fr) cz
  have hcapX : (integralChains X).d 2 1 (integralSupportCap A 2 1 cz.val phix.val) = 0 := by
    have hb := integralSupportCap_three_one_boundary A cz.val phix.val
    have hz : (integralRelativeChains A).d 3 2 cz.val = 0 := cz.property
    have hp : (integralRelativeCochains A).d 1 2 phix.val = 0 := phix.property
    rw [hz, hp] at hb
    have hzero : integralSupportCap A 1 1
        (0 : (integralRelativeChains A).X 2) phix.val = 0 := by
      rw [LinearMap.map_zero]
      exact LinearMap.zero_apply _
    rw [(integralSupportCap A 1 2 cz.val).map_zero, hzero] at hb
    simpa using hb
  have hcapY : (integralChains Y).d 2 1 (integralSupportCap B 2 1 zy.val cphi.val) = 0 := by
    have hb := integralSupportCap_three_one_boundary B zy.val cphi.val
    have hz : (integralRelativeChains B).d 3 2 zy.val = 0 := zy.property
    have hp : (integralRelativeCochains B).d 1 2 cphi.val = 0 := cphi.property
    rw [hz, hp] at hb
    have hzero : integralSupportCap B 1 1
        (0 : (integralRelativeChains B).X 2) cphi.val = 0 := by
      rw [LinearMap.map_zero]
      exact LinearMap.zero_apply _
    rw [(integralSupportCap B 1 2 zy.val).map_zero, hzero] at hb
    simpa using hb
  let capX : LinearMap.ker (((integralChains X).sc' 3 2 1).g.hom) :=
    ⟨integralSupportCap A 2 1 cz.val phix.val, hcapX⟩
  let capY : LinearMap.ker (((integralChains Y).sc' 3 2 1).g.hom) :=
    ⟨integralSupportCap B 2 1 zy.val cphi.val, hcapY⟩
  simp only [moduleComplexHomologyClass]
  rw [integralSupportCapHomologyOne_class, integralSupportCapHomologyOne_class]
  change homologyMap F 2
      (moduleComplexHomologyClass (integralChains X) 3 2 1 (by simp) (by simp) capX) =
    moduleComplexHomologyClass (integralChains Y) 3 2 1 (by simp) (by simp) capY
  rw [moduleComplexHomologyClass_map]
  apply congrArg ((integralChains Y).homologyIsoSc' 3 2 1 (by simp) (by simp)).inv
  apply congrArg (fun z => moduleHomologyClass ((integralChains Y).sc' 3 2 1) z)
  apply Subtype.ext
  exact integralSupportCap_naturality f hf 2 1 cz.val cphi.val

theorem integralSupportCapHomologyTwo_map
    (f : C(X, Y)) {A : Set X} {B : Set Y} (hf : Set.MapsTo f A B)
    (z : integralRelativeHomology A 3) (phi : integralRelativeCohomology B 2) :
    homologyMap (integralChainsFunctor.map (TopCat.ofHom f)) 1
        (integralSupportCapHomologyTwo A z
          (homologyMap (integralDualMap (integralRelativeMap f hf)) 2 phi)) =
      integralSupportCapHomologyTwo B
        (homologyMap (integralRelativeMap f hf) 3 z) phi := by
  obtain ⟨cz, hcz⟩ := moduleComplexHomologyClass_surjective
    (integralRelativeChains A) 4 3 2 (by simp) (by simp) z
  obtain ⟨cphi, hcphi⟩ := moduleComplexHomologyClass_surjective
    (integralRelativeCochains B) 1 2 3 (by simp) (by simp) phi
  let fr := integralRelativeMap f hf
  let g := integralDualMap fr
  let F := integralChainsFunctor.map (TopCat.ofHom f)
  rw [← hcz, ← hcphi]
  have hres := moduleComplexHomologyClass_map fr 4 3 2 (by simp) (by simp) cz
  have hpush := moduleComplexHomologyClass_map g 1 2 3 (by simp) (by simp) cphi
  rw [hres, hpush]
  let phix := moduleHomologyCycleMap
    ((shortComplexFunctor' (ModuleCat.{u} Int) (ComplexShape.up Nat) 1 2 3).map g) cphi
  let zy := moduleHomologyCycleMap
    ((shortComplexFunctor' (ModuleCat.{u} Int) (ComplexShape.down Nat) 4 3 2).map fr) cz
  have hcapX : (integralChains X).d 1 0 (integralSupportCap A 1 2 cz.val phix.val) = 0 := by
    have hz : (integralRelativeChains A).d 3 2 cz.val = 0 := cz.property
    have hp : (integralRelativeCochains A).d 2 3 phix.val = 0 := phix.property
    have hb := integralSupportCap_three_two_boundary A cz.val phix.val
    rw [hz, hp] at hb
    have hzero : integralSupportCap A 0 2
        (0 : (integralRelativeChains A).X 2) phix.val = 0 := by
      rw [LinearMap.map_zero]
      exact LinearMap.zero_apply _
    rw [hzero, (integralSupportCap A 0 3 cz.val).map_zero] at hb
    simpa using hb
  have hcapY : (integralChains Y).d 1 0 (integralSupportCap B 1 2 zy.val cphi.val) = 0 := by
    have hz : (integralRelativeChains B).d 3 2 zy.val = 0 := zy.property
    have hp : (integralRelativeCochains B).d 2 3 cphi.val = 0 := cphi.property
    have hb := integralSupportCap_three_two_boundary B zy.val cphi.val
    rw [hz, hp] at hb
    have hzero : integralSupportCap B 0 2
        (0 : (integralRelativeChains B).X 2) cphi.val = 0 := by
      rw [LinearMap.map_zero]
      exact LinearMap.zero_apply _
    rw [hzero, (integralSupportCap B 0 3 zy.val).map_zero] at hb
    simpa using hb
  let capX : LinearMap.ker (((integralChains X).sc' 2 1 0).g.hom) :=
    ⟨integralSupportCap A 1 2 cz.val phix.val, hcapX⟩
  let capY : LinearMap.ker (((integralChains Y).sc' 2 1 0).g.hom) :=
    ⟨integralSupportCap B 1 2 zy.val cphi.val, hcapY⟩
  simp only [moduleComplexHomologyClass]
  rw [integralSupportCapHomologyTwo_class, integralSupportCapHomologyTwo_class]
  change homologyMap F 1
      (moduleComplexHomologyClass (integralChains X) 2 1 0 (by simp) (by simp) capX) =
    moduleComplexHomologyClass (integralChains Y) 2 1 0 (by simp) (by simp) capY
  rw [moduleComplexHomologyClass_map]
  apply congrArg ((integralChains Y).homologyIsoSc' 2 1 0 (by simp) (by simp)).inv
  apply congrArg (fun z => moduleHomologyClass ((integralChains Y).sc' 2 1 0) z)
  apply Subtype.ext
  exact integralSupportCap_naturality f hf 1 2 cz.val cphi.val

theorem integralSupportCapHomologyThree_map
    (f : C(X, Y)) {A : Set X} {B : Set Y} (hf : Set.MapsTo f A B)
    (z : integralRelativeHomology A 3) (phi : integralRelativeCohomology B 3) :
    homologyMap (integralChainsFunctor.map (TopCat.ofHom f)) 0
        (integralSupportCapHomologyThree A z
          (homologyMap (integralDualMap (integralRelativeMap f hf)) 3 phi)) =
      integralSupportCapHomologyThree B
        (homologyMap (integralRelativeMap f hf) 3 z) phi := by
  obtain ⟨cz, hcz⟩ := moduleComplexHomologyClass_surjective
    (integralRelativeChains A) 4 3 2 (by simp) (by simp) z
  obtain ⟨cphi, hcphi⟩ := moduleComplexHomologyClass_surjective
    (integralRelativeCochains B) 2 3 4 (by simp) (by simp) phi
  let fr := integralRelativeMap f hf
  let g := integralDualMap fr
  let F := integralChainsFunctor.map (TopCat.ofHom f)
  rw [← hcz, ← hcphi]
  have hres := moduleComplexHomologyClass_map fr 4 3 2 (by simp) (by simp) cz
  have hpush := moduleComplexHomologyClass_map g 2 3 4 (by simp) (by simp) cphi
  rw [hres, hpush]
  let phix := moduleHomologyCycleMap
    ((shortComplexFunctor' (ModuleCat.{u} Int) (ComplexShape.up Nat) 2 3 4).map g) cphi
  let zy := moduleHomologyCycleMap
    ((shortComplexFunctor' (ModuleCat.{u} Int) (ComplexShape.down Nat) 4 3 2).map fr) cz
  have hcapX : (integralChains X).d 0 0 (integralSupportCap A 0 3 cz.val phix.val) = 0 := by
    rw [(integralChains X).shape 0 0 (by simp)]
    simp
  have hcapY : (integralChains Y).d 0 0 (integralSupportCap B 0 3 zy.val cphi.val) = 0 := by
    rw [(integralChains Y).shape 0 0 (by simp)]
    simp
  let capX : LinearMap.ker (((integralChains X).sc' 1 0 0).g.hom) :=
    ⟨integralSupportCap A 0 3 cz.val phix.val, hcapX⟩
  let capY : LinearMap.ker (((integralChains Y).sc' 1 0 0).g.hom) :=
    ⟨integralSupportCap B 0 3 zy.val cphi.val, hcapY⟩
  simp only [moduleComplexHomologyClass]
  rw [integralSupportCapHomologyThree_class, integralSupportCapHomologyThree_class]
  change homologyMap F 0
      (moduleComplexHomologyClass (integralChains X) 1 0 0 (by simp) (by simp) capX) =
    moduleComplexHomologyClass (integralChains Y) 1 0 0 (by simp) (by simp) capY
  rw [moduleComplexHomologyClass_map]
  apply congrArg ((integralChains Y).homologyIsoSc' 1 0 0 (by simp) (by simp)).inv
  apply congrArg (fun z => moduleHomologyClass ((integralChains Y).sc' 1 0 0) z)
  apply Subtype.ext
  exact integralSupportCap_naturality f hf 0 3 cz.val cphi.val

end Poincare.Topology
