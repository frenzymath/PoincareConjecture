import PoincareConjecture.Proofs.M47.CanonicalNeckCalibratedAxial

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal BigOperators

namespace PoincareConjecture.M47

private theorem initial_zero_component_lt {epsilon u : ℝ}
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

theorem standard_initial_patch_pullback_lower {epsilon u : ℝ} {x : StandardCapSpace}
    (N : StandardCylinderPatch epsilon⁻¹ x) (g : RiemannianMetric 3 StandardCapSpace)
    (he : 0 < epsilon) (hsmall : epsilon ≤ 1 / 1200) (hu : u ∈ Icc (-2) 0)
    (hclose : RoundCylinderClose epsilon u (roundCylinderPullback g N.coordinate))
    (q : UnitTwoSphere) (s : ℝ) (hs : s ∈ Ioo (-epsilon⁻¹) epsilon⁻¹)
    (v : EuclideanSpace ℝ (Fin 3)) :
    (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤
      g.pullbackCoefficients (N.coordinate ∘ M35.cylinderChart q)
        (M35.cylinderCoordinateEquiv.symm (0, s)) v v := by
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
    have hb := initial_zero_component_lt hclose he hu.1 huone (z := (q, s)) hs ![i, j]
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
  have hmodel := M35.cylinderEuclideanCoefficients_lower hu.2 s v
  have herror : 3 * (6 * epsilon) * ‖v‖ ^ 2 ≤ (1 / 2 : ℝ) * ‖v‖ ^ 2 :=
    mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
  change (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ B v v
  have hlo := (abs_le.mp (herr.trans herror)).1
  change ‖v‖ ^ 2 ≤ C v v at hmodel
  linarith

theorem standard_initial_patch_axial_derivative {epsilon u : ℝ} {x : StandardCapSpace}
    (N : StandardCylinderPatch epsilon⁻¹ x) (g : RiemannianMetric 3 StandardCapSpace)
    (he : 0 < epsilon) (hsmall : epsilon ≤ 1 / 1200) (hu : u ∈ Icc (-2) 0)
    (hclose : RoundCylinderClose epsilon u (roundCylinderPullback g N.coordinate))
    {y : StandardCapSpace} (hy : y ∈ N.carrier) (w : TangentSpace (𝓡 3) y) :
    |mvfderiv (𝓡 3) (fun z => (N.inverse z).2) y w| ≤
      2 * g.tangentNorm y w := by
  obtain ⟨⟨q, s⟩, hs, rfl⟩ := N.coordinate_image.symm ▸ hy
  let p := M35.cylinderCoordinateEquiv.symm (0, s)
  have hp : M35.cylinderCoordinateEquiv p = (0, s) :=
    M35.cylinderCoordinateEquiv.apply_symm_apply (0, s)
  have hdom : (M35.cylinderCoordinateEquiv p).2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹ := by
    simpa only [hp] using hs.2
  have hchart : M35.cylinderChart q p = (q, s) := by
    change ((chartAt (EuclideanSpace ℝ (Fin 2)) q).symm
      (M35.cylinderCoordinateEquiv p).1, (M35.cylinderCoordinateEquiv p).2) = _
    rw [hp]
    apply Prod.ext
    · have h := (chartAt (EuclideanSpace ℝ (Fin 2)) q).left_inv
        (mem_chart_source (EuclideanSpace ℝ (Fin 2)) q)
      simpa only [M35.sphere_chart_center] using h
    · rfl
  let f := N.coordinate ∘ M35.cylinderChart q
  let A := mfderiv (𝓡 3) (𝓡 3) f p
  obtain ⟨e, heA⟩ := N.euclideanChart_mfderiv_invertible q hdom
  let v : EuclideanSpace ℝ (Fin 3) := e.symm w
  have hv : A v = w := by
    change mfderiv (𝓡 3) (𝓡 3) f p (e.symm w) = w
    rw [← heA]
    exact e.apply_symm_apply w
  have hmetric := standard_initial_patch_pullback_lower N g he hsmall hu hclose q s hs.2 v
  change (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ g.inner (f p) (A v) (A v) at hmetric
  have hroot : (g.tangentNorm (f p) (A v)) ^ 2 = g.inner (f p) (A v) (A v) :=
    Real.sq_sqrt ((by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ) * ‖v‖ ^ 2).trans hmetric)
  have hnorm : ‖v‖ ≤ 2 * g.tangentNorm (f p) (A v) := by
    have hnonneg : 0 ≤ g.tangentNorm (f p) (A v) := Real.sqrt_nonneg _
    nlinarith [norm_nonneg v]
  have haxis : |(M35.cylinderCoordinateEquiv v).2| ≤ ‖v‖ :=
    PiLp.norm_apply_le v (2 : Fin 3)
  have hdiff : mvfderiv (𝓡 3) (fun z => (N.inverse z).2) (f p) (A v) =
      (M35.cylinderCoordinateEquiv v).2 := N.axial_mfderiv_chart q hdom v
  have hbound := (congrArg abs hdiff).trans_le (haxis.trans hnorm)
  rw [hv] at hbound
  change |mvfderiv (𝓡 3) (fun z => (N.inverse z).2)
    (N.coordinate (M35.cylinderChart q p)) w| ≤
      2 * g.tangentNorm (N.coordinate (M35.cylinderChart q p)) w at hbound
  rwa [hchart] at hbound

end CoordinateNorm

end PoincareConjecture.M47
