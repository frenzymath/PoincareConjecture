import PoincareLib.Geometry.RicciFlow.Local.Energy.Coefficients.CompactFiniteCoefficient
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.Local.Energy.Coefficients.CompactFiniteCoefficient
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.Local.Energy.Comparison.RateFiniteAlgebra
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.Local.Energy.Comparison.ScalarEnergyComparison
import PoincareLib.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.Ricci.Operator

/-!
# Polynomial factors of the actual curvature difference flux

These are the finite algebraic factors displayed by M03's public
curvature-difference coordinate PDE. The parameters are inverse metrics,
connection coefficients and the background curvature gradient; no flow or
chart index enters the factors. In particular compact parameter bounds can
be taken before choosing any translated chart.
This is the local energy preparation for Morgan-Tian Section 12.5,
pp. 309-319; see uniform-difference-energy-coefficients.md.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
-- The tensor fibers are nested continuous linear-map spaces.
set_option maxSynthPendingDepth 8

open scoped BigOperators ContDiff

noncomputable section

namespace PoincareMT.M34.DifferenceEnergy

/-- The fixed model vector space for the coordinate algebra
(Section 12.5, pp. 309-319). -/
abbrev V (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The metric-difference fiber (Section 12.5, pp. 309-319). -/
abbrev FH (n : ℕ) := V n →L[ℝ] V n →L[ℝ] ℝ

/-- The connection-difference fiber, section then direction
(Section 12.5, pp. 309-319). -/
abbrev FA (n : ℕ) := V n →L[ℝ] V n →L[ℝ] V n

/-- The raised curvature-difference fiber (Section 12.5, pp. 309-319). -/
abbrev FS (n : ℕ) := V n →L[ℝ] V n →L[ℝ] V n →L[ℝ] V n

/-- Connection entries indexed by direction, section, and output
(Section 12.5, pp. 309-319). -/
abbrev Gamma (n : ℕ) := Fin n → Fin n → Fin n → ℝ

/-- Raw raised curvature entries, output before three inputs
(Section 12.5, pp. 309-319). -/
abbrev Raw (n : ℕ) := Fin n → Fin n → Fin n → Fin n → ℝ

/-- A vector of raw curvature arrays (Section 12.5, pp. 309-319). -/
abbrev Flux (n : ℕ) := Fin n → Raw n

/-- The inverse bilinear coefficient acts on model covectors
(Section 12.5, pp. 309-319). -/
abbrev Inverse (n : ℕ) := (V n →L[ℝ] ℝ) →L[ℝ] V n

/-- Actual tensor components in the fixed coordinate basis
(Section 12.5, pp. 309-319). -/
def raw {n : ℕ} (T : FS n) (l j k m : Fin n) : ℝ :=
  EuclideanSpace.proj l (T (EuclideanSpace.single j 1)
    (EuclideanSpace.single k 1) (EuclideanSpace.single m 1))

/-- Connection-difference components with the geometric argument order
(Section 12.5, pp. 309-319). -/
def ag {n : ℕ} (T : FA n) (i j l : Fin n) : ℝ :=
  EuclideanSpace.proj l (T (EuclideanSpace.single j 1) (EuclideanSpace.single i 1))

/-- The connection action corrects the raised slot positively and all
three covariant slots negatively (Section 12.5, pp. 309-319). -/
def curvatureAction {n : ℕ} (gamma : Gamma n) (d : Fin n) : Raw n →ₗ[ℝ] Raw n where
  toFun T l j k m := ∑ p : Fin n,
    (gamma d p l * T p j k m - gamma d j p * T l p k m -
      gamma d k p * T l j p m - gamma d m p * T l j k p)
  map_add' T U := by
    ext l j k m
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    ring
  map_smul' r T := by
    ext l j k m
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    ring

/-- The raised divergence action includes its positive trace term
(Section 12.5, pp. 309-319). -/
def divergenceAction {n : ℕ} (gamma : Gamma n) : Flux n →ₗ[ℝ] Raw n where
  toFun T l j k m := ∑ i : Fin n,
    (curvatureAction gamma i (T i) l j k m + ∑ p : Fin n, gamma i p i * T p l j k m)
  map_add' T U := by
    ext l j k m
    simp only [Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]
    ring
  map_smul' r T := by
    ext l j k m
    simp only [Pi.smul_apply, map_smul, RingHom.id_apply, smul_eq_mul,
      mul_add, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    apply Finset.sum_congr rfl
    intro p _
    ring

/-- Fixed linear contraction from raw arrays to chosen curvature
energy coordinates (Section 12.5, pp. 309-319). -/
def curvatureContraction {n dS : ℕ} (qS : FS n ≃L[ℝ] EuclideanSpace ℝ (Fin dS)) :
    Raw n →ₗ[ℝ] (Fin dS → ℝ) where
  toFun T alpha := ∑ l, ∑ j, ∑ k, ∑ m,
    qS ((EuclideanSpace.proj j).smulRight ((EuclideanSpace.proj k).smulRight
      ((EuclideanSpace.proj m).smulRight (EuclideanSpace.single l 1)))) alpha * T l j k m
  map_add' T U := by
    ext alpha
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' r T := by
    ext alpha
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro m _
    ring

/-- The flux term linear in the metric difference, using the exact
inverse-difference factorization (Section 12.5, pp. 309-319). -/
def metricFlux {n : ℕ} (I0 I1 : Inverse n) (kp : Flux n) : FH n →ₗ[ℝ] Flux n where
  toFun H i l j k m := ∑ d : Fin n,
    -EuclideanSpace.proj i (I0 (H (I1 (EuclideanSpace.proj d)))) * kp d l j k m
  map_add' H H' := by
    ext i l j k m
    simp only [add_apply, map_add, Pi.add_apply,
      neg_add, add_mul, Finset.sum_add_distrib]
  map_smul' r H := by
    ext i l j k m
    simp only [smul_apply, map_smul, Pi.smul_apply,
      RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    ring

/-- The flux term linear in the connection difference
(Section 12.5, pp. 309-319). -/
def connectionFlux {n : ℕ} (I0 : Inverse n) (R1 : Raw n) : FA n →ₗ[ℝ] Flux n where
  toFun A i l j k m := ∑ d : Fin n,
    EuclideanSpace.proj i (I0 (EuclideanSpace.proj d)) * curvatureAction (ag A) d R1 l j k m
  map_add' A A' := by
    ext i l j k m
    simp only [curvatureAction, ag, LinearMap.coe_mk, AddHom.coe_mk,
      add_apply, map_add, Pi.add_apply,
      add_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_add, mul_sub]
    ring
  map_smul' r A := by
    ext i l j k m
    simp only [curvatureAction, ag, LinearMap.coe_mk, AddHom.coe_mk,
      smul_apply, map_smul, Pi.smul_apply,
      RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    apply Finset.sum_congr rfl
    intro b _
    ring

/-- The flux term linear in the curvature difference
(Section 12.5, pp. 309-319). -/
def curvatureFlux {n : ℕ} (I0 : Inverse n) (gamma : Gamma n) : FS n →ₗ[ℝ] Flux n where
  toFun S i l j k m := ∑ d : Fin n,
    EuclideanSpace.proj i (I0 (EuclideanSpace.proj d)) * curvatureAction gamma d (raw S) l j k m
  map_add' S S' := by
    ext i l j k m
    simp only [curvatureAction, raw, LinearMap.coe_mk, AddHom.coe_mk,
      add_apply, map_add, Pi.add_apply,
      mul_add, Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_sub]
    ring
  map_smul' r S := by
    ext i l j k m
    simp only [curvatureAction, raw, LinearMap.coe_mk, AddHom.coe_mk,
      smul_apply, map_smul, Pi.smul_apply,
      RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    apply Finset.sum_congr rfl
    intro b _
    ring

/-- The principal derivative flux, linear in the coordinate curvature
gradient (Section 12.5, pp. 309-319). -/
def principalFlux {n dS : ℕ} (I0 : Inverse n)
    (qS : FS n ≃L[ℝ] EuclideanSpace ℝ (Fin dS)) :
    (Fin dS × Fin n → ℝ) →ₗ[ℝ] Flux n where
  toFun d i l j k m := ∑ b : Fin n, EuclideanSpace.proj i (I0 (EuclideanSpace.proj b)) *
    ∑ beta : Fin dS, raw (qS.symm (EuclideanSpace.single beta 1)) l j k m * d (beta, b)
  map_add' d d' := by
    ext i l j k m
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' r d := by
    ext i l j k m
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro beta _
    ring

/-- The extra connection-difference contribution to the raised
divergence remainder (Section 12.5, pp. 309-319). -/
def connectionRemainder {n : ℕ} (vp : Flux n) : FA n →ₗ[ℝ] Raw n where
  toFun A := divergenceAction (ag A) vp
  map_add' A A' := by
    ext l j k m
    simp only [divergenceAction, curvatureAction, ag, LinearMap.coe_mk, AddHom.coe_mk,
      add_apply, map_add, Pi.add_apply,
      add_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    ring
  map_smul' r A := by
    ext l j k m
    simp only [divergenceAction, curvatureAction, ag, LinearMap.coe_mk, AddHom.coe_mk,
      smul_apply, map_smul, Pi.smul_apply,
      RingHom.id_apply, smul_eq_mul, Finset.mul_sum, mul_add]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    · apply Finset.sum_congr rfl
      intro b _
      ring
    · apply Finset.sum_congr rfl
      intro b _
      ring

/-- The unfactored flux appearing in the actual lower M03 curvature
difference PDE (Section 12.5, pp. 309-319). -/
def curvatureDifferenceFlux {n : ℕ} (I0 I1 : Inverse n) (gamma : Gamma n)
    (R1 : Raw n) (kp : Flux n) (H : FH n) (A : FA n) (S : FS n) : Flux n :=
  fun i l j k m => ∑ d : Fin n,
    (EuclideanSpace.proj i (I0 (EuclideanSpace.proj d)) *
        curvatureAction gamma d (raw S) l j k m +
      -EuclideanSpace.proj i (I0 (H (I1 (EuclideanSpace.proj d)))) * kp d l j k m +
      EuclideanSpace.proj i (I0 (EuclideanSpace.proj d)) *
        curvatureAction (ag A) d R1 l j k m)

/-- The actual displayed flux is exactly the sum of its three linear
factors, with no term omitted (Section 12.5, pp. 309-319). -/
theorem curvatureDifferenceFlux_eq {n : ℕ} (I0 I1 : Inverse n) (gamma : Gamma n)
    (R1 : Raw n) (kp : Flux n) (H : FH n) (A : FA n) (S : FS n) :
    curvatureDifferenceFlux I0 I1 gamma R1 kp H A S =
      metricFlux I0 I1 kp H + connectionFlux I0 R1 A + curvatureFlux I0 gamma S := by
  funext i l j k m
  simp only [curvatureDifferenceFlux, metricFlux, connectionFlux, curvatureFlux,
    LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply, Finset.sum_add_distrib]
  ring

end PoincareMT.M34.DifferenceEnergy
