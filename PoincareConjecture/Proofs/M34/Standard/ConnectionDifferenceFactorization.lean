import PoincareConjecture.Proofs.M34.Standard.ConnectionDifferenceAlgebra
import PoincareConjecture.Proofs.M34.Standard.CanonicalRicciGradient

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 8

open scoped BigOperators

namespace PoincareConjecture.M34.DifferenceEnergy

theorem curvatureAction_trace_difference {n : ℕ}
    (gamma0 gamma1 : Gamma n) (R0 R1 : Raw n) (A : FA n) (S : FS n)
    (hA : ag A = gamma0 - gamma1) (hS : raw S = R0 - R1) (i j k : Fin n) :
    (∑ l : Fin n, curvatureAction gamma0 i R0 l l j k) -
        (∑ l : Fin n, curvatureAction gamma1 i R1 l l j k) =
      ricciGradientCurvature gamma0 S i j k + ricciGradientConnection R1 A i j k := by
  rw [curvatureAction_trace, curvatureAction_trace]
  dsimp only [ricciGradientCurvature, ricciGradientConnection,
    LinearMap.coe_mk, AddHom.coe_mk]
  rw [hA, hS]
  simp only [Pi.sub_apply, Finset.sum_sub_distrib, mul_sub, sub_mul]
  ring

theorem connectionRaise_difference {n : ℕ} (G0 G1 : FH n)
    (hG0 : G0.IsInvertible) (hG1 : G1.IsInvertible) (P0 P1 : Gamma n) :
    connectionRaise G0.inverse P0 - connectionRaise G1.inverse P1 =
      connectionRaise G0.inverse (P0 - P1) +
        connectionMetricRate G0.inverse
          (fun i j => G1.inverse (∑ k : Fin n, P1 i j k • EuclideanSpace.proj k))
          (G0 - G1) := by
  let L : (Fin n → Fin n → V n) →L[ℝ] FA n :=
    ContinuousLinearMap.piLpBilinearFromCoordinates
  change L (fun j i => G0.inverse (∑ k : Fin n, P0 i j k • EuclideanSpace.proj k)) -
      L (fun j i => G1.inverse (∑ k : Fin n, P1 i j k • EuclideanSpace.proj k)) =
    L (fun j i => G0.inverse (∑ k : Fin n, (P0 - P1) i j k • EuclideanSpace.proj k)) +
      L (fun j i => -G0.inverse
        ((G0 - G1) (G1.inverse (∑ k : Fin n, P1 i j k • EuclideanSpace.proj k))))
  rw [← map_sub, ← map_add]
  congr 1
  funext j i
  simp only [Pi.sub_apply, Pi.add_apply, sub_smul, Finset.sum_sub_distrib,
    sub_apply, map_sub, hG0.inverse_apply_self, hG1.self_apply_inverse]
  abel

theorem connectionDifferenceRate_factorization {n dS : ℕ}
    (qS : FS n ≃L[ℝ] EuclideanSpace ℝ (Fin dS))
    (G0 G1 : FH n) (hG0 : G0.IsInvertible) (hG1 : G1.IsInvertible)
    (C0 C1 : Gamma n) (gamma : Gamma n) (R1 : Raw n)
    (d : Fin dS × Fin n → ℝ) (A : FA n) (S : FS n)
    (hC : C0 - C1 = ricciGradientCoordinates qS d +
      ricciGradientConnection R1 A + ricciGradientCurvature gamma S) :
    connectionRaise G0.inverse (cyclicRicciGradient n C0) -
        connectionRaise G1.inverse (cyclicRicciGradient n C1) =
      connectionDifferenceRate qS G0.inverse gamma R1
        (fun i j => G1.inverse (∑ k : Fin n,
          cyclicRicciGradient n C1 i j k • EuclideanSpace.proj k)) d (G0 - G1) A S := by
  rw [connectionRaise_difference G0 G1 hG0 hG1, ← map_sub, hC, map_add, map_add,
    map_add, map_add]
  dsimp only [connectionDifferenceRate, connectionDerivativeRate,
    connectionConnectionRate, connectionCurvatureRate, LinearMap.comp_apply]
  abel

end PoincareConjecture.M34.DifferenceEnergy
