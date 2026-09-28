import PoincareConjecture.Proofs.M02.Topology.IntegralCochains

set_option autoImplicit false

noncomputable section

open CategoryTheory

universe u

namespace PoincareConjecture.Proofs.M02.Topology

def integralFrontFace (p q : Nat) :
    C(integralSimplex q, integralSimplex (p + q)) :=
  ⟨stdSimplex.map (Fin.castLE (Nat.le_add_left (q + 1) p)),
    stdSimplex.continuous_map (Fin.castLE (Nat.le_add_left (q + 1) p))⟩

def integralBackFace (p q : Nat) :
    C(integralSimplex p, integralSimplex (p + q)) :=
  let b : Fin (p + 1) -> Fin (p + q + 1) := fun i =>
    Fin.cast (congrArg Nat.succ (Nat.add_comm q p)) (Fin.natAdd q i)
  ⟨stdSimplex.map b, stdSimplex.continuous_map b⟩

variable {X : Type u} [TopologicalSpace X]

def integralCap (p q : Nat) :
    (integralChains X).X (p + q) →ₗ[Int]
      ((integralCochains X).X q →ₗ[Int] (integralChains X).X p) := by
  let E (s : C(integralSimplex (p + q), X)) :
      (integralCochains X).X q →ₗ[Int] (integralChains X).X p := by
    change ((integralChains X).X q ⟶ integralCoefficient.{u}) →ₗ[Int]
      (integralChains X).X p
    let ev : ((integralChains X).X q ⟶ integralCoefficient.{u}) →ₗ[Int]
        ULift.{u} Int :=
      (LinearMap.applyₗ (R := Int)
        (integralSingularGenerator (s.comp (integralFrontFace p q)) (ULift.up 1))).comp
          (ModuleCat.homLinearEquiv (S := Int)).toLinearMap
    let c := (ULift.moduleEquiv : ULift.{u} Int ≃ₗ[Int] Int).toLinearMap.comp ev
    let v := integralSingularGenerator (s.comp (integralBackFace p q)) (ULift.up 1)
    exact
      { toFun := fun phi => c phi • v
        map_add' := by
          intro phi psi
          rw [c.map_add]
          exact add_zsmul v (c phi) (c psi)
        map_smul' := by
          intro a phi
          rw [c.map_smul]
          calc
            (a • c phi) • v = a • (c phi • v) := by
              simpa only [zsmul_eq_mul, Int.cast_id] using (mul_smul a (c phi) v)
            _ = _ := (Int.cast_smul_eq_zsmul Int a (c phi • v)).symm }
  exact (Finsupp.lsum Int (fun s : C(integralSimplex (p + q), X) =>
    (ULift.moduleEquiv : ULift.{u} Int ≃ₗ[Int] Int).toLinearMap.smulRight (E s))).comp
      (integralChainCoordinates X (p + q)).toLinearMap

theorem integralCap_generator (p q : Nat)
    (s : C(integralSimplex (p + q), X)) (phi : (integralCochains X).X q) :
    integralCap p q (integralSingularGenerator s (ULift.up 1)) phi =
      ((show (integralChains X).X q ⟶ integralCoefficient.{u} from phi)
        (integralSingularGenerator (s.comp (integralFrontFace p q)) (ULift.up 1))).down •
          integralSingularGenerator (s.comp (integralBackFace p q)) (ULift.up 1) := by
  change (integralChains X).X q ⟶ integralCoefficient.{u} at phi
  unfold integralCap
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [integralChainCoordinates_generator, Finsupp.lsum_single]
  simp
  rfl

end PoincareConjecture.Proofs.M02.Topology
