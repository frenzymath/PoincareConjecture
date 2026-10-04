import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Geometry.Metric.ConnectionDifferenceAlgebra
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Analysis.Coordinates.FiniteCoordinateBounds

/-!
# Ordinary curvature derivatives in fixed energy coordinates

The raw component maps are continuous linear functionals. Finite coordinate
reconstruction therefore identifies the actual derivative of every raw
component, and its Ricci trace, with the chosen scalar energy-coordinate
derivatives. This is Morgan-Tian Section 12.5, pp. 309-319 and the owned
canonical-connection-difference-rate derivation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
-- Raw curvature components evaluate three nested Hom fibers.
set_option maxSynthPendingDepth 8

open scoped BigOperators

namespace PoincareMT.M34.DifferenceEnergy

/-- Each raised curvature entry is a continuous linear functional on the
fixed tensor fiber (Section 12.5, pp. 309-319). -/
noncomputable def rawComponent {n : ℕ} (l j k m : Fin n) : FS n →L[ℝ] ℝ where
  toFun R := raw R l j k m
  map_add' R S := by simp only [raw, map_add, add_apply]
  map_smul' r R := by simp only [raw, map_smul, smul_apply, RingHom.id_apply]
  cont := by unfold raw; fun_prop

/-- Fixed curvature coordinates reconstruct every raw component
(Section 12.5, pp. 309-319). -/
theorem raw_eq_sum_coordinates {n dS : ℕ}
    (qS : FS n ≃L[ℝ] EuclideanSpace ℝ (Fin dS)) (S : FS n) (l j k m : Fin n) :
    raw S l j k m = ∑ beta : Fin dS,
      raw (qS.symm (EuclideanSpace.single beta 1)) l j k m * qS S beta := by
  simpa only [rawComponent, ContinuousLinearMap.coe_mk', LinearMap.coe_mk,
    AddHom.coe_mk, smul_eq_mul, mul_comm] using
      (rawComponent l j k m).toLinearMap.apply_eq_sum_equiv_coordinates qS S

/-- Actual ordinary differentiation commutes with finite reconstruction
from scalar curvature energy coordinates (Section 12.5, pp. 309-319). -/
theorem fderiv_raw_eq_sum_coordinates
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n dS : ℕ}
    (qS : FS n ≃L[ℝ] EuclideanSpace ℝ (Fin dS)) {S : E → FS n} {x : E}
    (hS : DifferentiableAt ℝ S x) (v : E) (l j k m : Fin n) :
    fderiv ℝ (fun y => raw (S y) l j k m) x v =
      ∑ beta : Fin dS, raw (qS.symm (EuclideanSpace.single beta 1)) l j k m *
        fderiv ℝ (fun y => qS (S y) beta) x v := by
  have hleft := congrArg (fun L => L v)
    ((rawComponent l j k m).hasFDerivAt.comp x hS.hasFDerivAt).fderiv
  have hright (beta : Fin dS) :
      fderiv ℝ (fun y => qS (S y) beta) x v = qS (fderiv ℝ S x v) beta := by
    let L : FS n →L[ℝ] ℝ := (EuclideanSpace.proj beta).comp qS.toContinuousLinearMap
    exact congrArg (fun A => A v) (L.hasFDerivAt.comp x hS.hasFDerivAt).fderiv
  change fderiv ℝ (fun y => raw (S y) l j k m) x v = raw (fderiv ℝ S x v) l j k m at hleft
  rw [hleft]
  simp_rw [hright]
  exact raw_eq_sum_coordinates qS _ l j k m

/-- Tracing the actual raw derivatives gives the derivative-input map
used in the native connection rate (Section 12.5, pp. 309-319). -/
theorem sum_fderiv_raw_eq_ricciGradientCoordinates {n dS : ℕ}
    (qS : FS n ≃L[ℝ] EuclideanSpace ℝ (Fin dS)) {S : V n → FS n} {x : V n}
    (hS : DifferentiableAt ℝ S x) (i j k : Fin n) :
    (∑ l : Fin n, fderiv ℝ (fun y => raw (S y) l l j k) x (EuclideanSpace.single i 1)) =
      ricciGradientCoordinates qS
        (fun beta => fderiv ℝ (fun y => qS (S y) beta.1) x
          (EuclideanSpace.single beta.2 1)) i j k := by
  simp_rw [fderiv_raw_eq_sum_coordinates qS hS]
  dsimp only [ricciGradientCoordinates, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.sum_comm]
  simp only [Finset.sum_mul]

end PoincareMT.M34.DifferenceEnergy
