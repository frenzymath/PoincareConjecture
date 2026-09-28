import PoincareConjecture.Proofs.M02.Topology.IntegralSupportCapBoundary
import PoincareConjecture.Proofs.M02.Topology.ModuleBilinearHomology









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory

universe u

namespace PoincareConjecture.Proofs.M02.Topology

noncomputable section

attribute [local instance 2000] Submodule.Quotient.module
attribute [local instance 2000] Submodule.module

variable {X : Type u} [TopologicalSpace X]

private def transportBilinearHomology
    {S T U S' T' U' : ModuleCat.{u} Int}
    (eS : S ≅ S') (eT : T ≅ T') (eU : U ≅ U')
    (F : S' →ₗ[Int] (T' →ₗ[Int] U')) : S →ₗ[Int] (T →ₗ[Int] U) := by
  let G : S →+ (T →ₗ[Int] U) :=
    { toFun := fun z => eU.inv.hom.comp ((F (eS.hom z)).comp eT.hom.hom)
      map_zero' := by
        ext phi
        change eU.inv (F (eS.hom 0) (eT.hom phi)) = 0
        rw [map_zero, F.map_zero, LinearMap.zero_apply, map_zero]
      map_add' := by
        intro z w
        apply LinearMap.ext
        intro phi
        change eU.inv (F (eS.hom (z + w)) (eT.hom phi)) =
          eU.inv (F (eS.hom z) (eT.hom phi)) + eU.inv (F (eS.hom w) (eT.hom phi))
        rw [map_add, F.map_add, LinearMap.add_apply, map_add] }
  exact
    { toFun := G
      map_add' := G.map_add
      map_smul' := fun a z => by
        convert! map_zsmul G a z
        ext
        apply int_smul_eq_zsmul }

private theorem cycle_one (A : Set X) (z : LinearMap.ker
    ((integralRelativeChains A).sc' 4 3 2).g.hom)
    (phi : LinearMap.ker ((integralRelativeCochains A).sc' 0 1 2).g.hom) :
    (integralChains X).d 2 1 (integralSupportCap A 2 1 z.val phi.val) = 0 := by
  have hz : (integralRelativeChains A).d 3 2 z.val = 0 := z.property
  have hp : (integralRelativeCochains A).d 1 2 phi.val = 0 := phi.property
  have hb := integralSupportCap_three_one_boundary A
    (c := (z.val : (integralRelativeChains A).X 3))
    (phi := (phi.val : (integralRelativeCochains A).X 1))
  simpa only [Nat.reduceAdd] using hb ▸ (by rw [hz, hp]; simp)

private theorem boundary_left_one (A : Set X)
    (a : ((integralRelativeChains A).sc' 4 3 2).X₁)
    (phi : LinearMap.ker ((integralRelativeCochains A).sc' 0 1 2).g.hom) :
    integralSupportCap A 2 1 (((integralRelativeChains A).sc' 4 3 2).f a) phi.val ∈
      LinearMap.range (((integralChains X).sc' 3 2 1).f).hom := by
  have hp : (integralRelativeCochains A).d 1 2 phi.val = 0 := phi.property
  refine ⟨-integralSupportCap A 3 1 a phi.val, ?_⟩
  change (integralChains X).d 3 2 (-integralSupportCap A 3 1 a phi.val) =
    integralSupportCap A 2 1 ((integralRelativeChains A).d 4 3 a) phi.val
  have hb := integralSupportCap_four_one_boundary A
    (c := (a : (integralRelativeChains A).X 4))
    (phi := (phi.val : (integralRelativeCochains A).X 1))
  rw [map_neg]
  rw [hp] at hb
  simpa only [map_zero, zero_sub, neg_neg] using congrArg Neg.neg hb

private theorem boundary_right_one (A : Set X)
    (z : LinearMap.ker ((integralRelativeChains A).sc' 4 3 2).g.hom)
    (b : ((integralRelativeCochains A).sc' 0 1 2).X₁) :
    integralSupportCap A 2 1 z.val (((integralRelativeCochains A).sc' 0 1 2).f b) ∈
      LinearMap.range (((integralChains X).sc' 3 2 1).f).hom := by
  have hz : (integralRelativeChains A).d 3 2 z.val = 0 := z.property
  refine ⟨-integralSupportCap A 3 0 z.val b, ?_⟩
  change (integralChains X).d 3 2 (-integralSupportCap A 3 0 z.val b) =
    integralSupportCap A 2 1 z.val ((integralRelativeCochains A).d 0 1 b)
  have hb := integralSupportCap_three_zero_boundary A
    (c := (z.val : (integralRelativeChains A).X 3))
    (phi := (b : (integralRelativeCochains A).X 0))
  rw [map_neg]
  rw [hz] at hb
  simpa only [map_zero, LinearMap.zero_apply, zero_sub, neg_neg] using congrArg Neg.neg hb

def integralSupportCapHomologyOneShort (A : Set X) :
    ((integralRelativeChains A).sc' 4 3 2).homology →ₗ[Int]
      (((integralRelativeCochains A).sc' 0 1 2).homology →ₗ[Int]
        ((integralChains X).sc' 3 2 1).homology) :=
  moduleBilinearHomology ((integralRelativeChains A).sc' 4 3 2)
    ((integralRelativeCochains A).sc' 0 1 2) ((integralChains X).sc' 3 2 1)
    (integralSupportCap A 2 1) (cycle_one A) (boundary_left_one A) (boundary_right_one A)

theorem integralSupportCapHomologyOneShort_class (A : Set X)
    (z : LinearMap.ker ((integralRelativeChains A).sc' 4 3 2).g.hom)
    (phi : LinearMap.ker ((integralRelativeCochains A).sc' 0 1 2).g.hom) :
    integralSupportCapHomologyOneShort A
      (moduleHomologyClass ((integralRelativeChains A).sc' 4 3 2) z)
      (moduleHomologyClass ((integralRelativeCochains A).sc' 0 1 2) phi) =
    moduleHomologyClass ((integralChains X).sc' 3 2 1)
      ⟨integralSupportCap A 2 1 z.val phi.val, cycle_one A z phi⟩ :=
  moduleBilinearHomology_class _ _ _ _ _ _ _ z phi

def integralSupportCapHomologyOne (A : Set X) :
    integralRelativeHomology A 3 →ₗ[Int]
      (integralRelativeCohomology A 1 →ₗ[Int] integralHomology X 2) :=
  transportBilinearHomology
    ((integralRelativeChains A).homologyIsoSc' 4 3 2 (by simp) (by simp))
    ((integralRelativeCochains A).homologyIsoSc' 0 1 2 (by simp) (by simp))
    ((integralChains X).homologyIsoSc' 3 2 1 (by simp) (by simp))
    (integralSupportCapHomologyOneShort A)

private theorem cycle_two (A : Set X) (z : LinearMap.ker
    ((integralRelativeChains A).sc' 4 3 2).g.hom)
    (phi : LinearMap.ker ((integralRelativeCochains A).sc' 1 2 3).g.hom) :
    (integralChains X).d 1 0 (integralSupportCap A 1 2 z.val phi.val) = 0 := by
  have hz : (integralRelativeChains A).d 3 2 z.val = 0 := z.property
  have hp : (integralRelativeCochains A).d 2 3 phi.val = 0 := phi.property
  have hb := integralSupportCap_three_two_boundary A
    (c := (z.val : (integralRelativeChains A).X 3))
    (phi := (phi.val : (integralRelativeCochains A).X 2))
  simpa only [Nat.reduceAdd] using hb ▸ (by rw [hz, hp]; simp)

private theorem boundary_left_two (A : Set X)
    (a : ((integralRelativeChains A).sc' 4 3 2).X₁)
    (phi : LinearMap.ker ((integralRelativeCochains A).sc' 1 2 3).g.hom) :
    integralSupportCap A 1 2 (((integralRelativeChains A).sc' 4 3 2).f a) phi.val ∈
      LinearMap.range (((integralChains X).sc' 2 1 0).f).hom := by
  have hp : (integralRelativeCochains A).d 2 3 phi.val = 0 := phi.property
  refine ⟨integralSupportCap A 2 2 a phi.val, ?_⟩
  change (integralChains X).d 2 1 (integralSupportCap A 2 2 a phi.val) =
    integralSupportCap A 1 2 ((integralRelativeChains A).d 4 3 a) phi.val
  have hb := integralSupportCap_four_two_boundary A
    (c := (a : (integralRelativeChains A).X 4))
    (phi := (phi.val : (integralRelativeCochains A).X 2))
  rw [hp] at hb
  simpa only [map_zero, sub_zero] using hb

private theorem boundary_right_two (A : Set X)
    (z : LinearMap.ker ((integralRelativeChains A).sc' 4 3 2).g.hom)
    (b : ((integralRelativeCochains A).sc' 1 2 3).X₁) :
    integralSupportCap A 1 2 z.val (((integralRelativeCochains A).sc' 1 2 3).f b) ∈
      LinearMap.range (((integralChains X).sc' 2 1 0).f).hom := by
  have hz : (integralRelativeChains A).d 3 2 z.val = 0 := z.property
  refine ⟨integralSupportCap A 2 1 z.val b, ?_⟩
  change (integralChains X).d 2 1 (integralSupportCap A 2 1 z.val b) =
    integralSupportCap A 1 2 z.val ((integralRelativeCochains A).d 1 2 b)
  have hb := integralSupportCap_three_one_boundary A
    (c := (z.val : (integralRelativeChains A).X 3))
    (phi := (b : (integralRelativeCochains A).X 1))
  rw [hz] at hb
  simpa only [map_zero, LinearMap.zero_apply, sub_zero] using hb

def integralSupportCapHomologyTwoShort (A : Set X) :
    ((integralRelativeChains A).sc' 4 3 2).homology →ₗ[Int]
      (((integralRelativeCochains A).sc' 1 2 3).homology →ₗ[Int]
        ((integralChains X).sc' 2 1 0).homology) :=
  moduleBilinearHomology ((integralRelativeChains A).sc' 4 3 2)
    ((integralRelativeCochains A).sc' 1 2 3) ((integralChains X).sc' 2 1 0)
    (integralSupportCap A 1 2) (cycle_two A) (boundary_left_two A) (boundary_right_two A)

theorem integralSupportCapHomologyTwoShort_class (A : Set X)
    (z : LinearMap.ker ((integralRelativeChains A).sc' 4 3 2).g.hom)
    (phi : LinearMap.ker ((integralRelativeCochains A).sc' 1 2 3).g.hom) :
    integralSupportCapHomologyTwoShort A
      (moduleHomologyClass ((integralRelativeChains A).sc' 4 3 2) z)
      (moduleHomologyClass ((integralRelativeCochains A).sc' 1 2 3) phi) =
    moduleHomologyClass ((integralChains X).sc' 2 1 0)
      ⟨integralSupportCap A 1 2 z.val phi.val, cycle_two A z phi⟩ :=
  moduleBilinearHomology_class _ _ _ _ _ _ _ z phi

def integralSupportCapHomologyTwo (A : Set X) :
    integralRelativeHomology A 3 →ₗ[Int]
      (integralRelativeCohomology A 2 →ₗ[Int] integralHomology X 1) :=
  transportBilinearHomology
    ((integralRelativeChains A).homologyIsoSc' 4 3 2 (by simp) (by simp))
    ((integralRelativeCochains A).homologyIsoSc' 1 2 3 (by simp) (by simp))
    ((integralChains X).homologyIsoSc' 2 1 0 (by simp) (by simp))
    (integralSupportCapHomologyTwoShort A)

private theorem cycle_three (A : Set X) (z : LinearMap.ker
    ((integralRelativeChains A).sc' 4 3 2).g.hom)
    (phi : LinearMap.ker ((integralRelativeCochains A).sc' 2 3 4).g.hom) :
    (integralChains X).d 0 0 (integralSupportCap A 0 3 z.val phi.val) = 0 := by
  rw [(integralChains X).shape 0 0 (by simp)]
  simp

private theorem boundary_left_three (A : Set X)
    (a : ((integralRelativeChains A).sc' 4 3 2).X₁)
    (phi : LinearMap.ker ((integralRelativeCochains A).sc' 2 3 4).g.hom) :
    integralSupportCap A 0 3 (((integralRelativeChains A).sc' 4 3 2).f a) phi.val ∈
      LinearMap.range (((integralChains X).sc' 1 0 0).f).hom := by
  have hp : (integralRelativeCochains A).d 3 4 phi.val = 0 := phi.property
  refine ⟨-integralSupportCap A 1 3 a phi.val, ?_⟩
  change (integralChains X).d 1 0 (-integralSupportCap A 1 3 a phi.val) =
    integralSupportCap A 0 3 ((integralRelativeChains A).d 4 3 a) phi.val
  have hb := integralSupportCap_four_three_boundary A
    (c := (a : (integralRelativeChains A).X 4))
    (phi := (phi.val : (integralRelativeCochains A).X 3))
  rw [map_neg]
  rw [hp] at hb
  simpa only [map_zero, zero_sub, neg_neg] using congrArg Neg.neg hb

private theorem boundary_right_three (A : Set X)
    (z : LinearMap.ker ((integralRelativeChains A).sc' 4 3 2).g.hom)
    (b : ((integralRelativeCochains A).sc' 2 3 4).X₁) :
    integralSupportCap A 0 3 z.val (((integralRelativeCochains A).sc' 2 3 4).f b) ∈
      LinearMap.range (((integralChains X).sc' 1 0 0).f).hom := by
  have hz : (integralRelativeChains A).d 3 2 z.val = 0 := z.property
  refine ⟨-integralSupportCap A 1 2 z.val b, ?_⟩
  change (integralChains X).d 1 0 (-integralSupportCap A 1 2 z.val b) =
    integralSupportCap A 0 3 z.val ((integralRelativeCochains A).d 2 3 b)
  have hb := integralSupportCap_three_two_boundary A
    (c := (z.val : (integralRelativeChains A).X 3))
    (phi := (b : (integralRelativeCochains A).X 2))
  rw [map_neg]
  rw [hz] at hb
  simpa only [map_zero, LinearMap.zero_apply, zero_sub, neg_neg] using congrArg Neg.neg hb

def integralSupportCapHomologyThreeShort (A : Set X) :
    ((integralRelativeChains A).sc' 4 3 2).homology →ₗ[Int]
      (((integralRelativeCochains A).sc' 2 3 4).homology →ₗ[Int]
        ((integralChains X).sc' 1 0 0).homology) :=
  moduleBilinearHomology ((integralRelativeChains A).sc' 4 3 2)
    ((integralRelativeCochains A).sc' 2 3 4) ((integralChains X).sc' 1 0 0)
    (integralSupportCap A 0 3) (cycle_three A) (boundary_left_three A) (boundary_right_three A)

theorem integralSupportCapHomologyThreeShort_class (A : Set X)
    (z : LinearMap.ker ((integralRelativeChains A).sc' 4 3 2).g.hom)
    (phi : LinearMap.ker ((integralRelativeCochains A).sc' 2 3 4).g.hom) :
    integralSupportCapHomologyThreeShort A
      (moduleHomologyClass ((integralRelativeChains A).sc' 4 3 2) z)
      (moduleHomologyClass ((integralRelativeCochains A).sc' 2 3 4) phi) =
    moduleHomologyClass ((integralChains X).sc' 1 0 0)
      ⟨integralSupportCap A 0 3 z.val phi.val, cycle_three A z phi⟩ :=
  moduleBilinearHomology_class _ _ _ _ _ _ _ z phi

def integralSupportCapHomologyThree (A : Set X) :
    integralRelativeHomology A 3 →ₗ[Int]
      (integralRelativeCohomology A 3 →ₗ[Int] integralHomology X 0) :=
  transportBilinearHomology
    ((integralRelativeChains A).homologyIsoSc' 4 3 2 (by simp) (by simp))
    ((integralRelativeCochains A).homologyIsoSc' 2 3 4 (by simp) (by simp))
    ((integralChains X).homologyIsoSc' 1 0 0 (by simp) (by simp))
    (integralSupportCapHomologyThreeShort A)

theorem integralSupportCapHomologyOne_apply (A : Set X)
    (z : integralRelativeHomology A 3) (phi : integralRelativeCohomology A 1) :
    integralSupportCapHomologyOne A z phi =
      ((integralChains X).homologyIsoSc' 3 2 1 (by simp) (by simp)).inv
        (integralSupportCapHomologyOneShort A
          (((integralRelativeChains A).homologyIsoSc' 4 3 2 (by simp) (by simp)).hom z)
          (((integralRelativeCochains A).homologyIsoSc' 0 1 2 (by simp) (by simp)).hom phi)) := rfl

theorem integralSupportCapHomologyTwo_apply (A : Set X)
    (z : integralRelativeHomology A 3) (phi : integralRelativeCohomology A 2) :
    integralSupportCapHomologyTwo A z phi =
      ((integralChains X).homologyIsoSc' 2 1 0 (by simp) (by simp)).inv
        (integralSupportCapHomologyTwoShort A
          (((integralRelativeChains A).homologyIsoSc' 4 3 2 (by simp) (by simp)).hom z)
          (((integralRelativeCochains A).homologyIsoSc' 1 2 3 (by simp) (by simp)).hom phi)) := rfl

theorem integralSupportCapHomologyThree_apply (A : Set X)
    (z : integralRelativeHomology A 3) (phi : integralRelativeCohomology A 3) :
    integralSupportCapHomologyThree A z phi =
      ((integralChains X).homologyIsoSc' 1 0 0 (by simp) (by simp)).inv
        (integralSupportCapHomologyThreeShort A
          (((integralRelativeChains A).homologyIsoSc' 4 3 2 (by simp) (by simp)).hom z)
          (((integralRelativeCochains A).homologyIsoSc' 2 3 4 (by simp) (by simp)).hom phi)) := rfl

theorem integralSupportCapHomologyOne_class (A : Set X)
    (z : LinearMap.ker ((integralRelativeChains A).sc' 4 3 2).g.hom)
    (phi : LinearMap.ker ((integralRelativeCochains A).sc' 0 1 2).g.hom) :
    let eS := (integralRelativeChains A).homologyIsoSc' 4 3 2 (by simp) (by simp)
    let eT := (integralRelativeCochains A).homologyIsoSc' 0 1 2 (by simp) (by simp)
    let eU := (integralChains X).homologyIsoSc' 3 2 1 (by simp) (by simp)
    integralSupportCapHomologyOne A
      (eS.inv (moduleHomologyClass ((integralRelativeChains A).sc' 4 3 2) z))
      (eT.inv (moduleHomologyClass ((integralRelativeCochains A).sc' 0 1 2) phi)) =
    eU.inv (moduleHomologyClass ((integralChains X).sc' 3 2 1)
      ⟨integralSupportCap A 2 1 z.val phi.val, cycle_one A z phi⟩) := by
  dsimp only
  rw [integralSupportCapHomologyOne_apply, Iso.inv_hom_id_apply,
    Iso.inv_hom_id_apply, integralSupportCapHomologyOneShort_class]

theorem integralSupportCapHomologyTwo_class (A : Set X)
    (z : LinearMap.ker ((integralRelativeChains A).sc' 4 3 2).g.hom)
    (phi : LinearMap.ker ((integralRelativeCochains A).sc' 1 2 3).g.hom) :
    let eS := (integralRelativeChains A).homologyIsoSc' 4 3 2 (by simp) (by simp)
    let eT := (integralRelativeCochains A).homologyIsoSc' 1 2 3 (by simp) (by simp)
    let eU := (integralChains X).homologyIsoSc' 2 1 0 (by simp) (by simp)
    integralSupportCapHomologyTwo A
      (eS.inv (moduleHomologyClass ((integralRelativeChains A).sc' 4 3 2) z))
      (eT.inv (moduleHomologyClass ((integralRelativeCochains A).sc' 1 2 3) phi)) =
    eU.inv (moduleHomologyClass ((integralChains X).sc' 2 1 0)
      ⟨integralSupportCap A 1 2 z.val phi.val, cycle_two A z phi⟩) := by
  dsimp only
  rw [integralSupportCapHomologyTwo_apply, Iso.inv_hom_id_apply,
    Iso.inv_hom_id_apply, integralSupportCapHomologyTwoShort_class]

theorem integralSupportCapHomologyThree_class (A : Set X)
    (z : LinearMap.ker ((integralRelativeChains A).sc' 4 3 2).g.hom)
    (phi : LinearMap.ker ((integralRelativeCochains A).sc' 2 3 4).g.hom) :
    let eS := (integralRelativeChains A).homologyIsoSc' 4 3 2 (by simp) (by simp)
    let eT := (integralRelativeCochains A).homologyIsoSc' 2 3 4 (by simp) (by simp)
    let eU := (integralChains X).homologyIsoSc' 1 0 0 (by simp) (by simp)
    integralSupportCapHomologyThree A
      (eS.inv (moduleHomologyClass ((integralRelativeChains A).sc' 4 3 2) z))
      (eT.inv (moduleHomologyClass ((integralRelativeCochains A).sc' 2 3 4) phi)) =
    eU.inv (moduleHomologyClass ((integralChains X).sc' 1 0 0)
      ⟨integralSupportCap A 0 3 z.val phi.val, cycle_three A z phi⟩) := by
  dsimp only
  rw [integralSupportCapHomologyThree_apply, Iso.inv_hom_id_apply,
    Iso.inv_hom_id_apply, integralSupportCapHomologyThreeShort_class]

end

end PoincareConjecture.Proofs.M02.Topology
