import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerCompactnessBounds
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.AlphaCriticalInterface
import PoincareConjecture.Proofs.M60.Mathlib.CovariantIntegrationByParts



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff

noncomputable section

universe u

namespace PoincareConjecture.M60

open CoordinateExponential ConnectionVariation ConjugateVariation
  Poincare.Riemannian.RadialTransport

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "e" => EuclideanSpace.basisFun (Fin 2) ℝ

local instance suCompactVariationBilinearNormedGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance suCompactVariationBilinearNormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance suCompactVariationTrilinearNormedGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance suCompactVariationTrilinearNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace



def suWeightedChartVariation (g : RiemannianMetric n M) (b : M)
    (u : LoopPlane → E) (w : LoopPlane → ℝ) (phi : LoopPlane → E)
    (z : LoopPlane) : ℝ :=
  let G := g.pullbackCoefficients (extChartAt (𝓡 n) b).symm
  let V := fun i : Fin 2 => fderiv ℝ u z (e i)
  w z * ((∑ i : Fin 2, fderiv ℝ G (u z) (phi z) (V i) (V i)) +
    2 * ∑ i : Fin 2, G (u z) (V i) (fderiv ℝ phi z (e i)))

set_option maxHeartbeats 1600000 in




theorem suWeightedEuler_variation
    (g : RiemannianMetric n M) (b : M)
    {u phi : LoopPlane → E} {w : LoopPlane → ℝ} {O : Set LoopPlane}
    (hO : IsOpen O) (hu : ContDiffOn ℝ ∞ u O) (hw : ContDiffOn ℝ ∞ w O)
    (hrange : MapsTo u O (extChartAt (𝓡 n) b).target)
    (hphi : ContDiff ℝ ∞ phi) (hphic : HasCompactSupport phi)
    (hphis : tsupport phi ⊆ O)
    (heq : ∀ z ∈ O,
      let Gamma := christoffelBilinear
        (g.pullbackCoefficients (extChartAt (𝓡 n) b).symm)
      ∑ i : Fin 2, covDerivAlong Gamma u
        (fun y => w y • fderiv ℝ u y (e i)) (e i) z = 0) :
    Integrable (suWeightedChartVariation g b u w phi) ∧
      (∫ z, suWeightedChartVariation g b u w phi z) = 0 := by
  let G := g.pullbackCoefficients (extChartAt (𝓡 n) b).symm
  let Gamma := christoffelBilinear G
  let A := mapConnectionCoefficients Gamma u
  let B := fun z => G (u z)
  let V := fun i z => fderiv ℝ u z (e i)
  let W := fun i z => w z • V i z
  let P := fun z => ∑ i : Fin 2,
    B z (covariantDerivative A phi z (e i)) (W i z)
  have hG (z : LoopPlane) (hz : z ∈ O) : ContDiffAt ℝ ∞ G (u z) :=
    (g.contDiffOn_chartCoefficients b).contDiffAt
      ((isOpen_extChartAt_target b).mem_nhds (hrange hz))
  have hGamma (z : LoopPlane) (hz : z ∈ O) : ContDiffAt ℝ ∞ Gamma (u z) :=
    contDiffAt_christoffelBilinear (hG z hz)
      (g.isInvertible_chartCoefficients b (hrange hz))
  have hcompat (z : LoopPlane) (hz : z ∈ O) : IsMetricCompatibleAt G Gamma (u z) :=
    isMetricCompatibleAt_chartCoefficients g b (hrange hz)
  have hA : ContDiffOn ℝ ∞ A O := by
    intro z hz
    exact (contDiffAt_mapConnectionCoefficients (hGamma z hz)
      (hu.contDiffAt (hO.mem_nhds hz))).contDiffWithinAt
  have hB : ContDiffOn ℝ ∞ B O := by
    intro z hz
    exact ((hG z hz).comp z (hu.contDiffAt (hO.mem_nhds hz))).contDiffWithinAt
  have hW (i : Fin 2) : ContDiffOn ℝ ∞ (W i) O :=
    hw.smul ((hu.fderiv_of_isOpen hO (by simp)).clm_apply contDiffOn_const)
  have hcompat' (z : LoopPlane) (hz : z ∈ O) (d : LoopPlane) (a c : E) :
      fderiv ℝ (fun y => B y a c) z d = B z (A z d a) c + B z a (A z d c) := by
    simpa [covDerivAlong_def, B, A, mapConnectionCoefficients] using
      fderiv_metricAlong (hcompat z hz) ((hG z hz).differentiableAt (by simp))
        ((hu.contDiffAt (hO.mem_nhds hz)).differentiableAt (by simp))
        (differentiableAt_const a) (differentiableAt_const c) d
  have hi (i : Fin 2) := integrable_covariant_pairings (μ := volume)
    hO hA hB hphi.contDiffOn (hW i) hphic hphis (e i)
  have hip : Integrable P := integrable_finsetSum _ (fun i _ => (hi i).1)
  have hPi : (∫ z, P z) = 0 := by
    have hij (i : Fin 2) := integral_covariant_pairing_eq_neg (μ := volume)
      hO hA hB hphi.contDiffOn (hW i) hphic hphis hcompat' (e i)
    have hz (z : LoopPlane) :
        ∑ i : Fin 2, B z (phi z) (covariantDerivative A (W i) z (e i)) = 0 := by
      rw [← map_sum]
      by_cases hz : z ∈ O
      · have hh := heq z hz
        change (∑ i : Fin 2, covariantDerivative A (W i) z (e i)) = 0 at hh
        rw [hh, map_zero]
      · rw [image_eq_zero_of_notMem_tsupport (fun h => hz (hphis h)), map_zero, zero_apply]
    change (∫ z, ∑ i : Fin 2,
      B z (covariantDerivative A phi z (e i)) (W i z)) = 0
    rw [integral_finsetSum _ (fun i _ => (hi i).1)]
    simp_rw [hij]
    rw [Finset.sum_neg_distrib, ← integral_finsetSum _ (fun i _ => (hi i).2)]
    simp only [hz, integral_zero, neg_zero]
  have hpoint (z : LoopPlane) : suWeightedChartVariation g b u w phi z = 2 * P z := by
    by_cases hz : z ∈ O
    · have hterm (i : Fin 2) :
          fderiv ℝ G (u z) (phi z) (V i z) (V i z) +
            2 * G (u z) (V i z) (fderiv ℝ phi z (e i)) =
          2 * G (u z) (covDerivAlong Gamma u phi (e i) z) (V i z) := by
        rw [hcompat z hz (phi z) (V i z) (V i z)]
        have hsym (a c : E) : G (u z) a c = G (u z) c a := g.symm _ _ _
        have hGs := christoffelBilinear_chart_symm g b (u z) (phi z) (V i z)
        dsimp only [covDerivAlong_def]
        rw [hGs, hsym (V i z) (Gamma (u z) (V i z) (phi z)),
          hsym (V i z) (fderiv ℝ phi z (e i))]
        simp only [map_add, add_apply]
        dsimp only [Gamma, G, V]
        ring
      have h0 := hterm 0
      have h1 := hterm 1
      change w z * ((∑ i : Fin 2, fderiv ℝ G (u z) (phi z) (V i z) (V i z)) +
        2 * ∑ i : Fin 2, G (u z) (V i z) (fderiv ℝ phi z (e i))) = 2 * P z
      have hs :
          (fderiv ℝ G (u z) (phi z) (V 0 z) (V 0 z) +
            fderiv ℝ G (u z) (phi z) (V 1 z) (V 1 z)) +
          2 * (G (u z) (V 0 z) (fderiv ℝ phi z (e 0)) +
            G (u z) (V 1 z) (fderiv ℝ phi z (e 1))) =
          2 * (G (u z) (covDerivAlong Gamma u phi (e 0) z) (V 0 z) +
            G (u z) (covDerivAlong Gamma u phi (e 1) z) (V 1 z)) := by
        linarith only [h0, h1]
      rw [Fin.sum_univ_two, Fin.sum_univ_two, hs]
      simp only [P, B, W, Fin.sum_univ_two, map_smul, smul_eq_mul]
      change _ = 2 * (w z * G (u z) (covDerivAlong Gamma u phi (e 0) z) (V 0 z) +
        w z * G (u z) (covDerivAlong Gamma u phi (e 1) z) (V 1 z))
      ring
    · have hpz := image_eq_zero_of_notMem_tsupport (fun h => hz (hphis h))
      have hpd := fderiv_of_notMem_tsupport (𝕜 := ℝ) (fun h => hz (hphis h))
      simp only [suWeightedChartVariation, hpz, hpd, zero_apply, map_zero, mul_zero,
        P, covariantDerivative, add_zero, Finset.sum_const_zero]
  constructor
  · exact (hip.const_mul 2).congr (Filter.Eventually.of_forall fun z => (hpoint z).symm)
  · simp_rw [hpoint]
    rw [integral_const_mul, hPi, mul_zero]

end PoincareConjecture.M60
