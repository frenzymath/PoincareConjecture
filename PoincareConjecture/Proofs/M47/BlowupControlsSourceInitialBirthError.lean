import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialMetric

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal BigOperators

namespace PoincareConjecture.M47

private theorem initial_birth_component_lt {epsilon u : ℝ}
    {B : RoundCylinderTwoTensor} (h : RoundCylinderClose epsilon u B)
    (he : 0 < epsilon) (hlo : -2 ≤ u) (hu : u < 1)
    {z : RoundCylinderSpace} (hz : z.2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹)
    (a : Fin 2 → Fin 3) :
    |roundCylinderIteratedDerivative u (chartAt (EuclideanSpace ℝ (Fin 2)) z.1)
      B 0 (chartAt (EuclideanSpace ℝ (Fin 2)) z.1 z.1, z.2) a| < 6 * epsilon := by
  let T := roundCylinderIteratedDerivative u
    (chartAt (EuclideanSpace ℝ (Fin 2)) z.1) B 0
      (chartAt (EuclideanSpace ℝ (Fin 2)) z.1 z.1, z.2) a
  have hweight (i : Fin 3) :
      (1 / 6 : ℝ) ≤ ![(2 * (1 - u))⁻¹, (2 * (1 - u))⁻¹, 1] i := by
    have hinv : (1 / 6 : ℝ) ≤ (2 * (1 - u))⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le
        (a := 2 * (1 - u)) (b := 6) (by linarith) (by linarith)
    fin_cases i <;> first | exact hinv | norm_num
  have hw : (1 / 6 : ℝ) ^ 2 ≤
      ∏ i, ![(2 * (1 - u))⁻¹, (2 * (1 - u))⁻¹, 1] (a i) := by
    calc
      _ = ∏ _ : Fin 2, (1 / 6 : ℝ) := by simp
      _ ≤ _ := Finset.prod_le_prod (fun _ _ => by norm_num)
        (fun i _ => hweight (a i))
  have hb : (1 / 6 : ℝ) ^ 2 * T ^ 2 < epsilon ^ 2 :=
    (mul_le_mul_of_nonneg_right hw (sq_nonneg _)).trans_lt
      (h.component_sq_lt hu hz (Nat.zero_le _) a)
  change |T| < 6 * epsilon
  apply abs_lt_of_sq_lt_sq _ (by positivity)
  nlinarith

section CoordinateNorm

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem standard_initial_patch_pullback_error_le {epsilon u : ℝ} {x : StandardCapSpace}
    (N : StandardCylinderPatch epsilon⁻¹ x) (g : RiemannianMetric 3 StandardCapSpace)
    (he : 0 < epsilon) (hu : u ∈ Icc (-2) 0)
    (hclose : RoundCylinderClose epsilon u (roundCylinderPullback g N.coordinate))
    (q : UnitTwoSphere) (s : ℝ) (hs : s ∈ Ioo (-epsilon⁻¹) epsilon⁻¹)
    (v : EuclideanSpace ℝ (Fin 3)) :
    |g.pullbackCoefficients (N.coordinate ∘ M35.cylinderChart q)
        (M35.cylinderCoordinateEquiv.symm (0, s)) v v -
      M35.cylinderEuclideanCoefficients u (M35.cylinderCoordinateEquiv.symm (0, s)) v v| ≤
        18 * epsilon * ‖v‖ ^ 2 := by
  let p := M35.cylinderCoordinateEquiv.symm (0, s)
  let B := g.pullbackCoefficients (N.coordinate ∘ M35.cylinderChart q) p
  let C := M35.cylinderEuclideanCoefficients u p
  have hp : M35.cylinderCoordinateEquiv p = (0, s) :=
    M35.cylinderCoordinateEquiv.apply_symm_apply (0, s)
  have hdom : (M35.cylinderCoordinateEquiv p).2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹ := by
    simpa only [hp] using hs
  have huone : u < 1 := hu.2.trans_lt (by norm_num)
  have hB (i j : Fin 3) :
      |(B - C) (EuclideanSpace.basisFun (Fin 3) ℝ i)
        (EuclideanSpace.basisFun (Fin 3) ℝ j)| ≤ 6 * epsilon := by
    have hb := initial_birth_component_lt hclose he hu.1 huone (z := (q, s)) hs ![i, j]
    rw [M35.sphere_chart_center] at hb
    norm_num [roundCylinderIteratedDerivative] at hb
    have hC := M35.cylinderEuclideanMetric_basis u huone q p i j
    change C (EuclideanSpace.basisFun (Fin 3) ℝ i)
      (EuclideanSpace.basisFun (Fin 3) ℝ j) = _ at hC
    change |B (EuclideanSpace.basisFun (Fin 3) ℝ i)
      (EuclideanSpace.basisFun (Fin 3) ℝ j) -
      C (EuclideanSpace.basisFun (Fin 3) ℝ i)
        (EuclideanSpace.basisFun (Fin 3) ℝ j)| ≤ _
    rw [hC, N.euclideanChart_coefficient g q hdom, hp]
    exact hb.le
  have herr := M35.abs_bilinear_le_of_components (B - C) (by positivity) hB v
  change |B v v - C v v| ≤ 3 * (6 * epsilon) * ‖v‖ ^ 2 at herr
  simpa only [show (3 : ℝ) * (6 * epsilon) = 18 * epsilon by ring] using herr

theorem standard_initial_patch_pullback_lower_sharp {epsilon u : ℝ} {x : StandardCapSpace}
    (N : StandardCylinderPatch epsilon⁻¹ x) (g : RiemannianMetric 3 StandardCapSpace)
    (he : 0 < epsilon) (hsmall : epsilon ≤ 1 / 1200) (hu : u ∈ Icc (-2) 0)
    (hclose : RoundCylinderClose epsilon u (roundCylinderPullback g N.coordinate))
    (q : UnitTwoSphere) (s : ℝ) (hs : s ∈ Ioo (-epsilon⁻¹) epsilon⁻¹)
    (v : EuclideanSpace ℝ (Fin 3)) :
    (197 / 200 : ℝ) * ‖v‖ ^ 2 ≤
      g.pullbackCoefficients (N.coordinate ∘ M35.cylinderChart q)
        (M35.cylinderCoordinateEquiv.symm (0, s)) v v := by
  have herr := standard_initial_patch_pullback_error_le N g he hu hclose q s hs v
  have hmodel := M35.cylinderEuclideanCoefficients_lower hu.2 s v
  have hbudget : 18 * epsilon * ‖v‖ ^ 2 ≤ (3 / 200 : ℝ) * ‖v‖ ^ 2 :=
    mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
  have hlo := (abs_le.mp herr).1
  linarith

end CoordinateNorm

end PoincareConjecture.M47
