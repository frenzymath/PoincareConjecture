import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialMetric
import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialScalar
import PoincareConjecture.Proofs.M13.Metric










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



theorem standard_initial_neck_axial_derivative
    {y : StandardCapSpace} (hy : y ∈ N.patch.carrier)
    (w : TangentSpace (𝓡 3) y) :
    |mvfderiv (𝓡 3) (fun x => (N.patch.inverse x).2) y w| ≤
      4 * g0.metric.tangentNorm y w := by
  let q := (G.connection v).scalarCurvature z
  have hq : 0 < q := N.scalar_pos
  have hqfour : q < 4 :=
    (standard_initial_neck_birth_scale_lt_four N (by linarith) hdisjoint hshort).2
  have hv : 0 ≤ v := N.time_mem.1
  have hu : -v * q ∈ Icc (-2 : ℝ) 0 := by
    constructor
    · change -2 ≤ -v * (G.connection v).scalarCurvature z
      nlinarith only [hshort, hsmall]
    · exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hv) hq.le
  have hbirth : -v * q ∈ Icc (-v * q) 0 := ⟨le_rfl, hu.2⟩
  have htime : v + (-v * q) / q = 0 := by
    field_simp [hq.ne']
    ring
  have hinitial : G.metric 0 = g0.metric := G.base.initial_metric
  let gq : RiemannianMetric 3 StandardCapSpace := M13.scaleSmoothMetric g0.metric q hq
  have hclose : RoundCylinderClose gamma (-v * q)
      (roundCylinderPullback gq N.patch.coordinate) := by
    obtain ⟨hsmooth, B, hB, hjets⟩ := N.close
    have h : RoundCylinderClose gamma (-v * q)
        (fun p a b => q * roundCylinderPullback (G.metric (v + (-v * q) / q))
          N.patch.coordinate p a b) :=
      ⟨hsmooth (-v * q) hbirth, B, hB, hjets (-v * q) hbirth⟩
    change RoundCylinderClose gamma (-v * q)
      (fun p a b => q * roundCylinderPullback g0.metric N.patch.coordinate p a b)
    simpa only [htime, hinitial] using h
  have hb := standard_initial_patch_axial_derivative N.patch gq N.epsilon_pos
    hsmall hu hclose hy w
  change |mvfderiv (𝓡 3) (fun x => (N.patch.inverse x).2) y w| ≤
    2 * RiemannianMetric.tangentNorm (M13.scaleSmoothMetric g0.metric q hq) y w at hb
  rw [M13.scaleSmoothMetric_tangentNorm] at hb
  have hsqrt : Real.sqrt q ≤ 2 := (Real.sqrt_le_iff).mpr ⟨by norm_num, by linarith⟩
  refine hb.trans ?_
  have hnorm : 0 ≤ g0.metric.tangentNorm y w := Real.sqrt_nonneg _
  nlinarith [mul_le_mul_of_nonneg_right hsqrt hnorm]



theorem standard_initial_neck_axial_edist_le_pathELength
    (p : ℝ → StandardCapSpace)
    (hp : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 p (Icc 0 1))
    (himage : MapsTo p (Icc (0 : ℝ) 1) N.patch.carrier) :
    edist (N.patch.inverse (p 0)).2 (N.patch.inverse (p 1)).2 ≤
      4 * g0.metric.pathELength p 0 1 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : StandardCapSpace → Type _) :=
    ⟨g0.metric.toRiemannianMetric⟩
  have hnorm (x : StandardCapSpace) (w : TangentSpace (𝓡 3) x) :
      ‖w‖ = g0.metric.tangentNorm x w := by
    rw [norm_eq_sqrt_real_inner]
    rfl
  have hbound (x : StandardCapSpace) (hx : x ∈ N.patch.carrier) :
      ‖mvfderiv (𝓡 3) (fun y => (N.patch.inverse y).2) x‖ₑ ≤ (4 : ℝ≥0∞) := by
    apply ContinuousLinearMap.opENorm_le_bound
    intro w
    have hb := ENNReal.ofReal_le_ofReal
      (standard_initial_neck_axial_derivative N hsmall hdisjoint hshort hx w)
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)] at hb
    simpa only [← ofReal_norm, hnorm, Real.norm_eq_abs, ENNReal.ofReal_ofNat] using hb
  exact Poincare.edist_le_mul_pathELength_of_mfderiv_le
    (M := StandardCapSpace) (E := EuclideanSpace ℝ (Fin 3)) (F := ℝ)
    (I := 𝓡 3) (f := fun y => (N.patch.inverse y).2) (s := N.patch.carrier)
    (K := 4)
    (fun x hx => (N.patch.axial_contMDiffAt hx).of_le (by simp)) hbound hp himage

end PoincareConjecture.M47
