import PoincareConjecture.Proofs.M35.Thm12_28.NeckPathLength

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal NNReal

namespace PoincareConjecture.Proofs.M47

section CoordinateNorm

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem standardNeck_pullback_lower_calibrated {epsilon u : ℝ} {x : StandardCapSpace}
    (N : StandardCylinderPatch epsilon⁻¹ x) (g : RiemannianMetric 3 StandardCapSpace)
    (he : 0 < epsilon) (hsmall : epsilon ≤ 1 / 1200) (hu : u ∈ Icc (-1) 0)
    (hclose : RoundCylinderClose epsilon u (roundCylinderPullback g N.coordinate))
    (q : UnitTwoSphere) (s : ℝ) (hs : s ∈ Ioo (-epsilon⁻¹) epsilon⁻¹)
    (v : EuclideanSpace ℝ (Fin 3)) :
    (97 / 100 : ℝ) * ‖v‖ ^ 2 ≤
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
        (EuclideanSpace.basisFun (Fin 3) ℝ j)| ≤ 4 * epsilon := by
    have hb := hclose.component_abs_lt he hu.1 huone (z := (q, s)) hs (Nat.zero_le _) ![i, j]
    dsimp only at hb
    rw [M35.sphere_chart_center] at hb
    norm_num [roundCylinderIteratedDerivative] at hb
    have hC := M35.cylinderEuclideanMetric_basis u huone q p i j
    change C (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ j) = _ at hC
    change |B (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ j) -
      C (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ j)| ≤ _
    rw [hC, N.euclideanChart_coefficient g q hdom, hp]
    exact hb.le
  have herr := M35.abs_bilinear_le_of_components (B - C) (by positivity) hB v
  change |B v v - C v v| ≤ 3 * (4 * epsilon) * ‖v‖ ^ 2 at herr
  have hmodel := M35.cylinderEuclideanCoefficients_lower hu.2 s v
  have herror : 3 * (4 * epsilon) * ‖v‖ ^ 2 ≤ (3 / 100 : ℝ) * ‖v‖ ^ 2 :=
    mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
  change (97 / 100 : ℝ) * ‖v‖ ^ 2 ≤ B v v
  have hlo := (abs_le.mp (herr.trans herror)).1
  change ‖v‖ ^ 2 ≤ C v v at hmodel
  linarith

theorem standardNeck_axial_derivative_calibrated {epsilon u : ℝ} {x : StandardCapSpace}
    (N : StandardCylinderPatch epsilon⁻¹ x) (g : RiemannianMetric 3 StandardCapSpace)
    (he : 0 < epsilon) (hsmall : epsilon ≤ 1 / 1200) (hu : u ∈ Icc (-1) 0)
    (hclose : RoundCylinderClose epsilon u (roundCylinderPullback g N.coordinate))
    {y : StandardCapSpace} (hy : y ∈ N.carrier) (w : TangentSpace (𝓡 3) y) :
    |mvfderiv (𝓡 3) (fun z => (N.inverse z).2) y w| ≤
      (21 / 20 : ℝ) * g.tangentNorm y w := by
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
  have hmetric := standardNeck_pullback_lower_calibrated N g he hsmall hu hclose q s hs.2 v
  change (97 / 100 : ℝ) * ‖v‖ ^ 2 ≤ g.inner (f p) (A v) (A v) at hmetric
  have hroot : (g.tangentNorm (f p) (A v)) ^ 2 = g.inner (f p) (A v) (A v) :=
    Real.sq_sqrt ((by positivity : (0 : ℝ) ≤ (97 / 100 : ℝ) * ‖v‖ ^ 2).trans hmetric)
  have hnorm : ‖v‖ ≤ (21 / 20 : ℝ) * g.tangentNorm (f p) (A v) := by
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
      (21 / 20 : ℝ) * g.tangentNorm (N.coordinate (M35.cylinderChart q p)) w at hbound
  rw [hchart] at hbound
  exact hbound

end CoordinateNorm

theorem standardNeck_axial_edist_le_pathELength_calibrated
    {epsilon u : ℝ} {x : StandardCapSpace}
    (N : StandardCylinderPatch epsilon⁻¹ x) (g : RiemannianMetric 3 StandardCapSpace)
    (he : 0 < epsilon) (hsmall : epsilon ≤ 1 / 1200) (hu : u ∈ Icc (-1) 0)
    (hclose : RoundCylinderClose epsilon u (roundCylinderPullback g N.coordinate))
    (gamma : ℝ → StandardCapSpace)
    (hgamma : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 gamma (Icc 0 1))
    (himage : MapsTo gamma (Icc (0 : ℝ) 1) N.carrier) :
    edist (N.inverse (gamma 0)).2 (N.inverse (gamma 1)).2 ≤
      ENNReal.ofReal (21 / 20 : ℝ) * g.pathELength gamma 0 1 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : StandardCapSpace → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hnorm (z : StandardCapSpace) (v : TangentSpace (𝓡 3) z) :
      ‖v‖ = g.tangentNorm z v := by
    rw [norm_eq_sqrt_real_inner]
    rfl
  have hbound (z : StandardCapSpace) (hz : z ∈ N.carrier) :
      ‖mvfderiv (𝓡 3) (fun y => (N.inverse y).2) z‖ₑ ≤ ENNReal.ofReal (21 / 20 : ℝ) := by
    apply ContinuousLinearMap.opENorm_le_bound
    intro v
    have hb := ENNReal.ofReal_le_ofReal
      (standardNeck_axial_derivative_calibrated N g he hsmall hu hclose hz v)
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 21 / 20)] at hb
    simpa only [← ofReal_norm, hnorm, Real.norm_eq_abs] using hb
  exact Poincare.edist_le_mul_pathELength_of_mfderiv_le
    (M := StandardCapSpace) (E := EuclideanSpace ℝ (Fin 3)) (F := ℝ)
    (I := 𝓡 3) (f := fun y => (N.inverse y).2) (s := N.carrier)
    (K := Real.toNNReal (21 / 20 : ℝ))
    (fun z hz => (N.axial_contMDiffAt hz).of_le (by simp))
    (fun z hz => by exact hbound z hz) hgamma himage

end PoincareConjecture.Proofs.M47
