import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.LinearAlgebra.Quotient.Basic

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits HomologicalComplex

universe u v

namespace Poincare.Topology

attribute [local instance 2000] Submodule.Quotient.module
attribute [local instance 2000] Submodule.module

def moduleComplexCycleClass (C : ChainComplex (ModuleCat.{u} Int) Nat) (n : Nat) :
    (C.sc n).moduleCatLeftHomologyData.K →ₗ[Int] C.homology n :=
  (C.sc n).moduleCatHomologyIso.toLinearEquiv.symm.toLinearMap.comp
    (LinearMap.range (C.sc n).moduleCatToCycles).mkQ

theorem moduleComplexCycleClass_surjective
    (C : ChainComplex (ModuleCat.{u} Int) Nat) (n : Nat) :
    Function.Surjective (moduleComplexCycleClass C n) := by
  apply (C.sc n).moduleCatHomologyIso.toLinearEquiv.symm.surjective.comp
  exact Submodule.mkQ_surjective _

theorem moduleComplexCycleClass_eq (C : ChainComplex (ModuleCat.{u} Int) Nat) (n : Nat)
    (z : (C.sc n).moduleCatLeftHomologyData.K) :
    moduleComplexCycleClass C n z =
      C.homologyπ n ((C.sc n).moduleCatCyclesIso.inv z) := by
  exact (congrArg (fun f => f z) (C.sc n).moduleCatCyclesIso_inv_π).symm

def moduleComplexCycleMap
    {C D : ChainComplex (ModuleCat.{u} Int) Nat} (f : C ⟶ D) (n : Nat) :
    (C.sc n).moduleCatLeftHomologyData.K →ₗ[Int]
      (D.sc n).moduleCatLeftHomologyData.K :=
  (f.f n).hom.comp (LinearMap.ker (C.sc n).g.hom).subtype |>.codRestrict _ (by
    intro z
    change D.d n ((ComplexShape.down Nat).next n) (f.f n z.val) = 0
    have hf := congrArg (fun k => k z.val) (f.comm n ((ComplexShape.down Nat).next n))
    change D.d n ((ComplexShape.down Nat).next n) (f.f n z.val) =
      f.f _ (C.d n ((ComplexShape.down Nat).next n) z.val) at hf
    rw [hf, show C.d n ((ComplexShape.down Nat).next n) z.val = 0 from z.property,
      map_zero])

theorem moduleComplexCycleClass_map
    {C D : ChainComplex (ModuleCat.{u} Int) Nat} (f : C ⟶ D) (n : Nat)
    (z : (C.sc n).moduleCatLeftHomologyData.K) :
    homologyMap f n (moduleComplexCycleClass C n z) =
      moduleComplexCycleClass D n (moduleComplexCycleMap f n z) := by
  have hz : (D.sc n).moduleCatCyclesIso.hom
      (cyclesMap f n ((C.sc n).moduleCatCyclesIso.inv z)) = moduleComplexCycleMap f n z := by
    apply Subtype.ext
    have hi := congrArg (fun k => k ((C.sc n).moduleCatCyclesIso.inv z)) (cyclesMap_i f n)
    change D.iCycles n (cyclesMap f n ((C.sc n).moduleCatCyclesIso.inv z)) =
      f.f n (C.iCycles n ((C.sc n).moduleCatCyclesIso.inv z)) at hi
    have hC := congrArg (fun k => k z) (C.sc n).moduleCatCyclesIso_inv_iCycles
    have hD := congrArg (fun k => k (cyclesMap f n ((C.sc n).moduleCatCyclesIso.inv z)))
      (D.sc n).moduleCatCyclesIso_hom_i
    exact hD.trans (hi.trans (congrArg (f.f n) hC))
  rw [moduleComplexCycleClass_eq, moduleComplexCycleClass_eq]
  have h := congrArg (fun k => k ((C.sc n).moduleCatCyclesIso.inv z))
    (homologyπ_naturality (φ := f) (i := n))
  change homologyMap f n (C.homologyπ n ((C.sc n).moduleCatCyclesIso.inv z)) =
    D.homologyπ n (cyclesMap f n ((C.sc n).moduleCatCyclesIso.inv z)) at h
  rw [← hz]
  simpa only [Iso.hom_inv_id_apply] using h

section Equivalence

variable (C : ChainComplex (ModuleCat.{u} Int) Nat)
  (D : ChainComplex (ModuleCat.{v} Int) Nat)
  (e : ∀ n, C.X n ≃ₗ[Int] D.X n)
  (he : ∀ i j (x : C.X i), e j (C.d i j x) = D.d i j (e i x))

def moduleComplexCycleEquiv (n : Nat) :
    (C.sc n).moduleCatLeftHomologyData.K ≃ₗ[Int]
      (D.sc n).moduleCatLeftHomologyData.K where
  toFun z := ⟨e n z.val, by
    change D.d n ((ComplexShape.down Nat).next n) (e n z.val) = 0
    rw [← he, show C.d n ((ComplexShape.down Nat).next n) z.val = 0 from z.property,
      map_zero]⟩
  invFun z := ⟨(e n).symm z.val, by
    change C.d n ((ComplexShape.down Nat).next n) ((e n).symm z.val) = 0
    apply (e ((ComplexShape.down Nat).next n)).injective
    rw [map_zero, he, LinearEquiv.apply_symm_apply]
    exact z.property⟩
  left_inv z := by apply Subtype.ext; exact (e n).symm_apply_apply z.val
  right_inv z := by apply Subtype.ext; exact (e n).apply_symm_apply z.val
  map_add' z w := by apply Subtype.ext; exact (e n).map_add z.val w.val
  map_smul' a z := by apply Subtype.ext; exact (e n).map_smul a z.val

theorem moduleComplexCycleEquiv_boundaries (n : Nat) :
    (LinearMap.range (C.sc n).moduleCatToCycles).map
        (moduleComplexCycleEquiv C D e he n).toLinearMap =
      LinearMap.range (D.sc n).moduleCatToCycles := by
  ext z
  constructor
  · rintro ⟨a, ⟨x, rfl⟩, rfl⟩
    refine ⟨e ((ComplexShape.down Nat).prev n) x, ?_⟩
    apply Subtype.ext
    exact (he _ n x).symm
  · rintro ⟨x, rfl⟩
    refine ⟨(C.sc n).moduleCatToCycles ((e ((ComplexShape.down Nat).prev n)).symm x),
      ⟨_, rfl⟩, ?_⟩
    apply Subtype.ext
    change e n (C.d ((ComplexShape.down Nat).prev n) n
      ((e ((ComplexShape.down Nat).prev n)).symm x)) = D.d _ n x
    rw [he, LinearEquiv.apply_symm_apply]

def moduleComplexHomologyEquiv (n : Nat) : C.homology n ≃ₗ[Int] D.homology n :=
  (C.sc n).moduleCatHomologyIso.toLinearEquiv.trans
    ((Submodule.Quotient.equiv _ _ (moduleComplexCycleEquiv C D e he n)
      (moduleComplexCycleEquiv_boundaries C D e he n)).trans
        (D.sc n).moduleCatHomologyIso.toLinearEquiv.symm)

theorem moduleComplexHomologyEquiv_class (n : Nat)
    (z : (C.sc n).moduleCatLeftHomologyData.K) :
    moduleComplexHomologyEquiv C D e he n (moduleComplexCycleClass C n z) =
      moduleComplexCycleClass D n (moduleComplexCycleEquiv C D e he n z) := by
  change (D.sc n).moduleCatHomologyIso.toLinearEquiv.symm
      ((Submodule.Quotient.equiv _ _ (moduleComplexCycleEquiv C D e he n)
        (moduleComplexCycleEquiv_boundaries C D e he n))
          ((C.sc n).moduleCatHomologyIso.toLinearEquiv
            ((C.sc n).moduleCatHomologyIso.toLinearEquiv.symm
              ((LinearMap.range (C.sc n).moduleCatToCycles).mkQ z)))) =
    (D.sc n).moduleCatHomologyIso.toLinearEquiv.symm
      ((LinearMap.range (D.sc n).moduleCatToCycles).mkQ
        (moduleComplexCycleEquiv C D e he n z))
  rw [LinearEquiv.apply_symm_apply]
  rfl

end Equivalence

theorem moduleComplexHomologyEquiv_naturality
    {C C' : ChainComplex (ModuleCat.{u} Int) Nat}
    {D D' : ChainComplex (ModuleCat.{v} Int) Nat}
    (e : ∀ n, C.X n ≃ₗ[Int] D.X n)
    (he : ∀ i j (x : C.X i), e j (C.d i j x) = D.d i j (e i x))
    (e' : ∀ n, C'.X n ≃ₗ[Int] D'.X n)
    (he' : ∀ i j (x : C'.X i), e' j (C'.d i j x) = D'.d i j (e' i x))
    (f : C ⟶ C') (g : D ⟶ D')
    (hfg : ∀ n (x : C.X n), e' n (f.f n x) = g.f n (e n x))
    (n : Nat) (a : C.homology n) :
    moduleComplexHomologyEquiv C' D' e' he' n (homologyMap f n a) =
      homologyMap g n (moduleComplexHomologyEquiv C D e he n a) := by
  obtain ⟨z, rfl⟩ := moduleComplexCycleClass_surjective C n a
  rw [moduleComplexCycleClass_map, moduleComplexHomologyEquiv_class,
    moduleComplexHomologyEquiv_class, moduleComplexCycleClass_map]
  congr 1
  apply Subtype.ext
  exact hfg n z.val

end Poincare.Topology
