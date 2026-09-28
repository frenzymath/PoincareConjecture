import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialBirthMetric
import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialSpeed










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal

namespace PoincareConjecture.M47

variable {g0 : StandardInitialMetric} {G : MaximalStandardCapFlow g0}
  {atlas : StandardCylinderAtlas} {v gamma : ℝ} {z : StandardCapSpace}
  (N : StandardEvolvingNeck atlas G v gamma z
    (Icc (-v * (G.connection v).scalarCurvature z) 0))
  (hsmall : gamma ≤ 1 / 1200)
  (hdisjoint : Disjoint N.patch.carrier
    {y | g0.metric.edist 0 y ≤ ENNReal.ofReal (g0.cylindrical_end.radius + 4)})
  (hshort : v * (G.connection v).scalarCurvature z < 1 + gamma)

include hsmall hdisjoint hshort

section CoordinateNorm

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace



theorem standard_initial_neck_axial_derivative_sharp
    {y : StandardCapSpace} (hy : y ∈ N.patch.carrier)
    (w : TangentSpace (𝓡 3) y) :
    |mvfderiv (𝓡 3) (fun x => (N.patch.inverse x).2) y w| ≤
      (29 / 20 : ℝ) * g0.metric.tangentNorm y w := by
  obtain ⟨⟨q, s⟩, hs, rfl⟩ := N.patch.coordinate_image.symm ▸ hy
  let p := M35.cylinderCoordinateEquiv.symm (0, s)
  have hp : M35.cylinderCoordinateEquiv p = (0, s) :=
    M35.cylinderCoordinateEquiv.apply_symm_apply (0, s)
  have hdom : (M35.cylinderCoordinateEquiv p).2 ∈ Ioo (-gamma⁻¹) gamma⁻¹ := by
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
  let f := N.patch.coordinate ∘ M35.cylinderChart q
  let A := mfderiv (𝓡 3) (𝓡 3) f p
  obtain ⟨e, heA⟩ := N.patch.euclideanChart_mfderiv_invertible q hdom
  let v : EuclideanSpace ℝ (Fin 3) := e.symm w
  have hv : A v = w := by
    change mfderiv (𝓡 3) (𝓡 3) f p (e.symm w) = w
    rw [← heA]
    exact e.apply_symm_apply w
  have hmetric := (standard_initial_neck_birth_pullback_bounds N hsmall hdisjoint hshort
    q s hs.2 v).1
  change (20 / 29 : ℝ) ^ 2 * ‖v‖ ^ 2 ≤ g0.metric.inner (f p) (A v) (A v) at hmetric
  have hroot : (g0.metric.tangentNorm (f p) (A v)) ^ 2 =
      g0.metric.inner (f p) (A v) (A v) :=
    Real.sq_sqrt ((by positivity : (0 : ℝ) ≤ (20 / 29 : ℝ) ^ 2 * ‖v‖ ^ 2).trans hmetric)
  have hnorm : ‖v‖ ≤ (29 / 20 : ℝ) * g0.metric.tangentNorm (f p) (A v) := by
    have hnonneg : 0 ≤ g0.metric.tangentNorm (f p) (A v) := Real.sqrt_nonneg _
    nlinarith [norm_nonneg v]
  have haxis : |(M35.cylinderCoordinateEquiv v).2| ≤ ‖v‖ :=
    PiLp.norm_apply_le v (2 : Fin 3)
  have hdiff : mvfderiv (𝓡 3) (fun x => (N.patch.inverse x).2) (f p) (A v) =
      (M35.cylinderCoordinateEquiv v).2 := N.patch.axial_mfderiv_chart q hdom v
  have hbound := (congrArg abs hdiff).trans_le (haxis.trans hnorm)
  rw [hv] at hbound
  change |mvfderiv (𝓡 3) (fun x => (N.patch.inverse x).2)
    (N.patch.coordinate (M35.cylinderChart q p)) w| ≤
      (29 / 20 : ℝ) * g0.metric.tangentNorm
        (N.patch.coordinate (M35.cylinderChart q p)) w at hbound
  rwa [hchart] at hbound

end CoordinateNorm



theorem standard_initial_neck_axial_path_length_sharp
    (p : ℝ → StandardCapSpace)
    (hp : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 p (Icc 0 1))
    (himage : MapsTo p (Icc (0 : ℝ) 1) N.patch.carrier) :
    edist (N.patch.inverse (p 0)).2 (N.patch.inverse (p 1)).2 ≤
      ENNReal.ofReal (29 / 20 : ℝ) * g0.metric.pathELength p 0 1 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : StandardCapSpace → Type _) :=
    ⟨g0.metric.toRiemannianMetric⟩
  have hnorm (x : StandardCapSpace) (w : TangentSpace (𝓡 3) x) :
      ‖w‖ = g0.metric.tangentNorm x w := by
    rw [norm_eq_sqrt_real_inner]
    rfl
  have hbound (x : StandardCapSpace) (hx : x ∈ N.patch.carrier) :
      ‖mvfderiv (𝓡 3) (fun y => (N.patch.inverse y).2) x‖ₑ ≤
        ENNReal.ofReal (29 / 20 : ℝ) := by
    apply ContinuousLinearMap.opENorm_le_bound
    intro w
    have hb := ENNReal.ofReal_le_ofReal
      (standard_initial_neck_axial_derivative_sharp N hsmall hdisjoint hshort hx w)
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 29 / 20)] at hb
    simpa only [← ofReal_norm, hnorm, Real.norm_eq_abs] using hb
  exact Poincare.edist_le_mul_pathELength_of_mfderiv_le
    (M := StandardCapSpace) (E := EuclideanSpace ℝ (Fin 3)) (F := ℝ)
    (I := 𝓡 3) (f := fun y => (N.patch.inverse y).2) (s := N.patch.carrier)
    (K := Real.toNNReal (29 / 20 : ℝ))
    (fun x hx => (N.patch.axial_contMDiffAt hx).of_le (by simp))
    (fun x hx => by exact hbound x hx) hp himage

end PoincareConjecture.M47
