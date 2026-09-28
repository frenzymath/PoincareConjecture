import PoincareConjecture.Proofs.M64.Sec19_6_Comparison.PolarMap
import PoincareConjecture.Proofs.M60.Def18_17_FillingArea.AnnularLengthMap












set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal NNReal Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {c0 c1 : ℝ → M}



noncomputable def m64PolarCoordinate (theta : LoopPlane → ℝ)
    (z : LoopPlane) : AnnulusCoordinates :=
  annulusPoint (theta z) (2 * ‖z‖ - 1)



theorem m64AnnulusPolarMap_local_edist_of_angle
    (A : M64Annulus g c0 c1) {z : LoopPlane} (hz : z ≠ 0)
    {theta : LoopPlane → ℝ} (htheta : ContDiffAt ℝ 1 theta z)
    (hpolar : ∀ w : LoopPlane,
      ‖w‖ • Proofs.M58.angularPoint (theta w) = w)
    (htheta0 : 0 < theta z) (hthetaP : theta z < curvePeriod) :
    ∃ (K : ℝ≥0) (U : Set LoopPlane), U ∈ 𝓝 z ∧
      ∀ w : LoopPlane, w ∈ U → ∀ v : LoopPlane, v ∈ U →
        (1 / 2 : ℝ) ≤ ‖w‖ → ‖w‖ ≤ (1 : ℝ) →
        (1 / 2 : ℝ) ≤ ‖v‖ → ‖v‖ ≤ (1 : ℝ) →
        g.edist (m64AnnulusPolarMap A w) (m64AnnulusPolarMap A v) ≤
          (ENNReal.ofReal A.lipschitz_constant * (K : ℝ≥0∞)) *
            ENNReal.ofReal ‖w - v‖ := by
  let p : LoopPlane → AnnulusCoordinates := m64PolarCoordinate theta
  have hnorm : ContDiffAt ℝ 1 (norm : LoopPlane → ℝ) z := contDiffAt_norm ℝ hz
  have hscalar : ContDiffAt ℝ 1 (fun q : LoopPlane => 2 * ‖q‖ - 1) z := by
    simpa only [one_mul] using ((contDiffAt_const.mul hnorm).sub contDiffAt_const)
  have hp : ContDiffAt ℝ 1 p z := by
    apply contDiffAt_euclidean.mpr
    intro i
    fin_cases i
    · simpa [p, m64PolarCoordinate, annulusPoint] using htheta
    · simpa [p, m64PolarCoordinate, annulusPoint] using hscalar
  obtain ⟨K, V, hV, hKV⟩ := hp.exists_lipschitzOnWith
  have hangle : theta ⁻¹' Ioo (0 : ℝ) curvePeriod ∈ 𝓝 z := by
    exact htheta.continuousAt (Ioo_mem_nhds htheta0 hthetaP)
  refine ⟨K, V ∩ theta ⁻¹' Ioo (0 : ℝ) curvePeriod,
    inter_mem hV hangle, ?_⟩
  intro w hw v hv hwlo hwhi hvlo hvhi
  have hwtheta : theta w ∈ Ioo (0 : ℝ) curvePeriod := hw.2
  have hvtheta : theta v ∈ Ioo (0 : ℝ) curvePeriod := hv.2
  have hpdom (q : LoopPlane) (hq : theta q ∈ Ioo (0 : ℝ) curvePeriod)
      (hlo : 1 / 2 ≤ ‖q‖) (hhi : ‖q‖ ≤ 1) :
      m64PolarCoordinate theta q ∈ m64AnnulusDomain := by
    change 0 ≤ theta q ∧ theta q ≤ curvePeriod ∧
      0 ≤ 2 * ‖q‖ - 1 ∧ 2 * ‖q‖ - 1 ≤ 1
    exact ⟨le_of_lt hq.1, le_of_lt hq.2,
      by linarith, by linarith⟩
  have hpw : p w ∈ m64AnnulusDomain := hpdom w hwtheta hwlo hwhi
  have hpv : p v ∈ m64AnnulusDomain := hpdom v hvtheta hvlo hvhi
  have hA := A.lipschitz_on_domain ⟨p w, hpw⟩ ⟨p v, hpv⟩
  have hcoord := hKV hw.1 hv.1
  have hwne : w ≠ 0 := by
    intro hw0
    subst w
    norm_num at hwlo
  have hvne : v ≠ 0 := by
    intro hv0
    subst v
    norm_num at hvlo
  have hmw : m64AnnulusPolarMap A w = A.map (p w) := by
    exact m64AnnulusPolarMap_eq_polar A hwne (hpolar w)
  have hmv : m64AnnulusPolarMap A v = A.map (p v) := by
    exact m64AnnulusPolarMap_eq_polar A hvne (hpolar v)
  rw [hmw, hmv]
  calc
    g.edist (A.map (p w)) (A.map (p v)) ≤
        ENNReal.ofReal A.lipschitz_constant * ENNReal.ofReal ‖p w - p v‖ := hA
    _ ≤ ENNReal.ofReal A.lipschitz_constant *
        ((K : ℝ≥0∞) * ENNReal.ofReal ‖w - v‖) := by
      have hcoord' : ENNReal.ofReal ‖p w - p v‖ ≤
          (K : ℝ≥0∞) * ENNReal.ofReal ‖w - v‖ := by
        simpa only [edist_dist, dist_eq_norm] using hcoord
      exact mul_le_mul_of_nonneg_left hcoord' (by positivity)
    _ = (ENNReal.ofReal A.lipschitz_constant * (K : ℝ≥0∞)) *
        ENNReal.ofReal ‖w - v‖ := by rw [mul_assoc]

end PoincareConjecture
