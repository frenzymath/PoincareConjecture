import PoincareConjecture.Proofs.M34.Mathlib.FiniteBilinearCoordinates
import PoincareConjecture.Proofs.M34.Standard.DifferenceFluxAlgebra

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 8

open scoped BigOperators

noncomputable section

namespace PoincareConjecture.M34.DifferenceEnergy

def cyclicRicciGradient (n : ℕ) : Gamma n →ₗ[ℝ] Gamma n where
  toFun C i j k := -C i j k - C j k i + C k i j
  map_add' C C' := by
    ext i j k
    simp only [Pi.add_apply]
    ring
  map_smul' r C := by
    ext i j k
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    ring

def ricciGradientCoordinates {n dS : ℕ}
    (qS : FS n ≃L[ℝ] EuclideanSpace ℝ (Fin dS)) :
    (Fin dS × Fin n → ℝ) →ₗ[ℝ] Gamma n where
  toFun d i j k := ∑ beta : Fin dS,
    (∑ l : Fin n, raw (qS.symm (EuclideanSpace.single beta 1)) l l j k) * d (beta, i)
  map_add' d d' := by
    ext i j k
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' r d := by
    ext i j k
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro beta _
    ring

def ricciGradientCurvature {n : ℕ} (gamma : Gamma n) : FS n →ₗ[ℝ] Gamma n where
  toFun S i j k :=
    -(∑ p : Fin n, gamma i j p * ∑ l : Fin n, raw S l l p k) -
      ∑ p : Fin n, gamma i k p * ∑ l : Fin n, raw S l l j p
  map_add' S S' := by
    ext i j k
    simp only [raw, map_add, add_apply, Pi.add_apply, mul_add, Finset.sum_add_distrib]
    ring
  map_smul' r S := by
    ext i j k
    simp only [raw, map_smul, smul_apply, Pi.smul_apply, RingHom.id_apply,
      smul_eq_mul, Finset.mul_sum]
    simp only [mul_left_comm _ r]
    simp only [mul_neg, mul_sub, Finset.mul_sum]

def ricciGradientConnection {n : ℕ} (R1 : Raw n) : FA n →ₗ[ℝ] Gamma n where
  toFun A i j k :=
    -(∑ p : Fin n, ag A i j p * ∑ l : Fin n, R1 l l p k) -
      ∑ p : Fin n, ag A i k p * ∑ l : Fin n, R1 l l j p
  map_add' A A' := by
    ext i j k
    simp only [ag, map_add, add_apply, Pi.add_apply, add_mul, Finset.sum_add_distrib]
    ring
  map_smul' r A := by
    ext i j k
    simp only [ag, map_smul, smul_apply, Pi.smul_apply, RingHom.id_apply,
      smul_eq_mul, Finset.mul_sum, mul_assoc]
    simp only [mul_neg, mul_sub, Finset.mul_sum]

def connectionRaise {n : ℕ} (I0 : Inverse n) : Gamma n →ₗ[ℝ] FA n where
  toFun P := ContinuousLinearMap.piLpBilinearFromCoordinates (p := 2) (q := 2)
    (fun j i => I0 (∑ k : Fin n, P i j k • EuclideanSpace.proj k))
  map_add' P Q := by
    have h : (fun j i => I0 (∑ k : Fin n, (P + Q) i j k • EuclideanSpace.proj k)) =
        (fun j i => I0 (∑ k : Fin n, P i j k • EuclideanSpace.proj k)) +
          (fun j i => I0 (∑ k : Fin n, Q i j k • EuclideanSpace.proj k)) := by
      funext j i
      simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, map_add]
    rw [h, map_add]
  map_smul' r P := by
    have h : (fun j i => I0 (∑ k : Fin n, (r • P) i j k • EuclideanSpace.proj k)) =
        r • (fun j i => I0 (∑ k : Fin n, P i j k • EuclideanSpace.proj k)) := by
      funext j i
      simp only [Pi.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum, map_smul]
    rw [h, map_smul]
    rfl

def connectionMetricRate {n : ℕ} (I0 : Inverse n) (vp : Fin n → Fin n → V n) :
    FH n →ₗ[ℝ] FA n where
  toFun H := ContinuousLinearMap.piLpBilinearFromCoordinates (p := 2) (q := 2)
    (fun j i => -I0 (H (vp i j)))
  map_add' H H' := by
    have h : (fun j i => -I0 ((H + H') (vp i j))) =
        (fun j i => -I0 (H (vp i j))) + (fun j i => -I0 (H' (vp i j))) := by
      funext j i
      simp only [add_apply, map_add, neg_add, Pi.add_apply]
    rw [h, map_add]
  map_smul' r H := by
    have h : (fun j i => -I0 ((r • H) (vp i j))) =
        r • (fun j i => -I0 (H (vp i j))) := by
      funext j i
      simp only [smul_apply, map_smul, Pi.smul_apply, smul_neg]
    rw [h, map_smul]
    rfl

def connectionDerivativeRate {n dS : ℕ}
    (qS : FS n ≃L[ℝ] EuclideanSpace ℝ (Fin dS)) (I0 : Inverse n) :
    (Fin dS × Fin n → ℝ) →ₗ[ℝ] FA n :=
  (connectionRaise I0).comp ((cyclicRicciGradient n).comp (ricciGradientCoordinates qS))

def connectionConnectionRate {n : ℕ} (I0 : Inverse n) (R1 : Raw n) : FA n →ₗ[ℝ] FA n :=
  (connectionRaise I0).comp ((cyclicRicciGradient n).comp (ricciGradientConnection R1))

def connectionCurvatureRate {n : ℕ} (I0 : Inverse n) (gamma : Gamma n) : FS n →ₗ[ℝ] FA n :=
  (connectionRaise I0).comp ((cyclicRicciGradient n).comp (ricciGradientCurvature gamma))

def connectionEnergyCoordinates {n dA : ℕ}
    (qA : FA n ≃L[ℝ] EuclideanSpace ℝ (Fin dA)) : FA n →ₗ[ℝ] (Fin dA → ℝ) :=
  LinearMap.pi fun alpha => (EuclideanSpace.proj alpha).toLinearMap.comp qA.toLinearMap

def connectionDifferenceRate {n dS : ℕ}
    (qS : FS n ≃L[ℝ] EuclideanSpace ℝ (Fin dS)) (I0 : Inverse n)
    (gamma : Gamma n) (R1 : Raw n) (vp : Fin n → Fin n → V n)
    (d : Fin dS × Fin n → ℝ) (H : FH n) (A : FA n) (S : FS n) : FA n :=
  connectionDerivativeRate qS I0 d + connectionMetricRate I0 vp H +
    connectionConnectionRate I0 R1 A + connectionCurvatureRate I0 gamma S

end PoincareConjecture.M34.DifferenceEnergy
