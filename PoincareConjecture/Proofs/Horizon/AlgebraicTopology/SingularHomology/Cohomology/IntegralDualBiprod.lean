import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Cohomology.IntegralCochains
import Mathlib.Algebra.Homology.HomologicalComplexBiprod









set_option autoImplicit false

noncomputable section

open CategoryTheory Limits HomologicalComplex

universe u

namespace Poincare.Topology

variable {C D E : ChainComplex (ModuleCat.{u} Int) Nat}

@[simp]
theorem integralDualMap_id (C : ChainComplex (ModuleCat.{u} Int) Nat) :
    integralDualMap (𝟙 C) = 𝟙 (integralDualComplex C) := by
  ext n phi
  change 𝟙 (C.X n) ≫ (show C.X n ⟶ integralCoefficient from phi) = phi
  exact Category.id_comp _

@[simp]
theorem integralDualMap_comp (f : C ⟶ D) (g : D ⟶ E) :
    integralDualMap (f ≫ g) = integralDualMap g ≫ integralDualMap f := by
  ext n phi
  change (f.f n ≫ g.f n) ≫ (show E.X n ⟶ integralCoefficient from phi) =
    f.f n ≫ (g.f n ≫ phi)
  exact Category.assoc _ _ _

@[simp]
theorem integralDualMap_zero : integralDualMap (0 : C ⟶ D) = 0 := by
  ext n phi
  change (0 : C.X n ⟶ D.X n) ≫ (show D.X n ⟶ integralCoefficient from phi) = 0
  exact zero_comp

@[simp]
theorem integralDualMap_add (f g : C ⟶ D) :
    integralDualMap (f + g) = integralDualMap f + integralDualMap g := by
  ext n phi
  change (f.f n + g.f n) ≫ (show D.X n ⟶ integralCoefficient from phi) =
    f.f n ≫ phi + g.f n ≫ phi
  exact Preadditive.add_comp _ _ _ (f.f n) (g.f n)
    (show D.X n ⟶ integralCoefficient from phi)

@[simp]
theorem integralDualMap_neg (f : C ⟶ D) :
    integralDualMap (-f) = -integralDualMap f := by
  ext n phi
  change (-f.f n) ≫ (show D.X n ⟶ integralCoefficient from phi) = -(f.f n ≫ phi)
  exact Preadditive.neg_comp (f.f n) (show D.X n ⟶ integralCoefficient from phi)

def integralDualBiprodIso (C D : ChainComplex (ModuleCat.{u} Int) Nat) :
    integralDualComplex (C ⊞ D) ≅ integralDualComplex C ⊞ integralDualComplex D where
  hom := biprod.lift (integralDualMap biprod.inl) (integralDualMap biprod.inr)
  inv := biprod.desc (integralDualMap biprod.fst) (integralDualMap biprod.snd)
  hom_inv_id := by
    rw [biprod.lift_desc, ← integralDualMap_comp, ← integralDualMap_comp,
      ← integralDualMap_add, biprod.total, integralDualMap_id]
  inv_hom_id := by
    apply biprod.hom_ext'
    · apply biprod.hom_ext
      · simp [← integralDualMap_comp]
      · simp [← integralDualMap_comp]
    · apply biprod.hom_ext
      · simp [← integralDualMap_comp]
      · simp [← integralDualMap_comp]

@[reassoc (attr := simp)]
theorem integralDualBiprodIso_hom_fst (C D : ChainComplex (ModuleCat.{u} Int) Nat) :
    (integralDualBiprodIso C D).hom ≫ biprod.fst =
      integralDualMap (biprod.inl : C ⟶ C ⊞ D) := biprod.lift_fst _ _

@[reassoc (attr := simp)]
theorem integralDualBiprodIso_hom_snd (C D : ChainComplex (ModuleCat.{u} Int) Nat) :
    (integralDualBiprodIso C D).hom ≫ biprod.snd =
      integralDualMap (biprod.inr : D ⟶ C ⊞ D) := biprod.lift_snd _ _

end Poincare.Topology
