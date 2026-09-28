import PoincareConjecture.Proofs.M34.Prop12_7_Asymptotics.EndCylinderChartBounds
import PoincareConjecture.Proofs.M34.Prop12_7_Asymptotics.EndCylinderChartMap
import PoincareConjecture.Proofs.M34.Mathlib.LinearPrecomposeLocalJets

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.M34

local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

noncomputable def cylinderCoordinateLinearMap : RoundCylinderCoordinates →L[ℝ] E₃ :=
  ((EuclideanSpace.proj 0).comp (ContinuousLinearMap.fst ℝ E₂ ℝ)).smulRight
      (EuclideanSpace.single 0 1) +
    ((EuclideanSpace.proj 1).comp (ContinuousLinearMap.fst ℝ E₂ ℝ)).smulRight
      (EuclideanSpace.single 1 1) +
    (ContinuousLinearMap.snd ℝ E₂ ℝ).smulRight (EuclideanSpace.single 2 1)

theorem cylinderCoordinateLinearMap_apply (p : RoundCylinderCoordinates) :
    cylinderCoordinateLinearMap p = WithLp.toLp 2 ![p.1 0, p.1 1, p.2] := by
  ext i
  fin_cases i <;> simp [cylinderCoordinateLinearMap]

theorem endSphereCylinderMap_eq_comp {g : RiemannianMetric 3 StandardCapSpace}
    (e : StandardCylindricalEnd g) (q : UnitTwoSphere) :
    endSphereCylinderMap e q = endStereographicChart e q ∘ cylinderCoordinateLinearMap := by
  funext p
  have hh : cylinderHorizontal (cylinderCoordinateLinearMap p) = p.1 := by
    ext i
    fin_cases i <;> simp [cylinderHorizontal_apply, cylinderCoordinateLinearMap_apply]
  simp only [Function.comp_apply, endStereographicChart, sphereCylinderChart,
    hh, endSphereCylinderMap]
  congr 2
  simp [cylinderCoordinateLinearMap_apply]

theorem cylinderCoordinateLinearMap_center_mem {r : ℝ}
    (hr : r ∈ Icc (17 / 5 : ℝ) (23 / 5)) :
    cylinderCoordinateLinearMap (0, r) ∈ endCylinderChartRegion := by
  have heq : cylinderCoordinateLinearMap (0, r) = EuclideanSpace.single 2 r := by
    ext i
    fin_cases i <;> simp [cylinderCoordinateLinearMap_apply]
  rw [heq]
  constructor
  · rw [Metric.mem_ball, dist_zero_right, PiLp.norm_single, Real.norm_eq_abs,
      abs_of_nonneg (by linarith [hr.1])]
    linarith [hr.2]
  · simpa using (show r ∈ Ioo (3 : ℝ) 5 by constructor <;> linarith [hr.1, hr.2])

theorem endSphereCylinderMap_uniform_jet_bound
    {g : RiemannianMetric 3 StandardCapSpace} (e : StandardCylindricalEnd g) (m : ℕ) :
    ∃ C : ℝ, ∀ (q : UnitTwoSphere) r, r ∈ Icc (17 / 5 : ℝ) (23 / 5) →
      ‖iteratedFDeriv ℝ m (endSphereCylinderMap e q) (0, r)‖ ≤ C := by
  obtain ⟨C, hC⟩ := endStereographicChart_uniform_jet_bounds e m
  refine ⟨C * ‖cylinderCoordinateLinearMap‖ ^ m, ?_⟩
  intro q r hr
  have hx := cylinderCoordinateLinearMap_center_mem hr
  have hs : ContDiffAt ℝ ∞ (endStereographicChart e q)
      (cylinderCoordinateLinearMap (0, r)) :=
    contMDiffAt_iff_contDiffAt.mp (endStereographicChart_contMDiffAt e q
      (by have := hx.2.1; linarith))
  rw [endSphereCylinderMap_eq_comp]
  exact (cylinderCoordinateLinearMap.norm_iteratedFDeriv_comp_right_of_contDiffAt
    (hs.of_le (by exact_mod_cast le_top))).trans
      (mul_le_mul_of_nonneg_right (hC q _ hx) (pow_nonneg (norm_nonneg _) _))

end PoincareConjecture.M34
