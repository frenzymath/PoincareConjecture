import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.SUAlphaStrongConvergence
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.AlphaCriticalInterface
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.LocalExtr.Basic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology ENNReal

noncomputable section

universe u

namespace PoincareConjecture.M60

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local instance : NormedAddCommGroup
    (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance : NormedSpace ℝ
    (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

local instance : NormedAddCommGroup
    (EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance : NormedSpace ℝ
    (EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

def suAlphaLocalDensity (g : RiemannianMetric n M) (b : M) (alpha : ℝ)
    (z : LoopPlane) (w : EuclideanSpace ℝ (Fin n) ×
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))) : ℝ :=
  let lambda := 16 / (‖z‖ ^ 2 + 4) ^ 2
  lambda ^ (1 - alpha) * suRegularizedQuadratic
    (suAlphaPairMetric (g.pullbackCoefficients (extChartAt (𝓡 n) b).symm w.1))
      lambda alpha w.2

private theorem coefficient_nonneg (g : RiemannianMetric n M) (b : M)
    (y v : EuclideanSpace ℝ (Fin n)) :
    0 ≤ g.pullbackCoefficients (extChartAt (𝓡 n) b).symm y v v := by
  change 0 ≤ g.inner ((extChartAt (𝓡 n) b).symm y)
    (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) b).symm y v)
    (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) b).symm y v)
  by_cases h : mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) b).symm y v = 0
  · rw [h]
    simp
  · exact (g.pos _ _ h).le

private theorem localDensity_eq (g : RiemannianMetric n M) (b : M) (alpha : ℝ)
    (z : LoopPlane) (y v0 v1 : EuclideanSpace ℝ (Fin n)) :
    suAlphaLocalDensity g b alpha z (y, (v0, v1)) =
      suAlphaRoundFactor z * (1 +
        (g.pullbackCoefficients (chartAt (EuclideanSpace ℝ (Fin n)) b).symm y v0 v0 +
          g.pullbackCoefficients (chartAt (EuclideanSpace ℝ (Fin n)) b).symm y v1 v1) /
            suAlphaRoundFactor z) ^ alpha := by
  let lambda := suAlphaRoundFactor z
  let q := g.pullbackCoefficients (extChartAt (𝓡 n) b).symm y v0 v0 +
    g.pullbackCoefficients (extChartAt (𝓡 n) b).symm y v1 v1
  have hl : 0 < lambda := by dsimp [lambda, suAlphaRoundFactor]; positivity
  have hq : 0 ≤ q := add_nonneg (coefficient_nonneg g b y v0) (coefficient_nonneg g b y v1)
  change lambda ^ (1 - alpha) * (lambda + q) ^ alpha =
    lambda * (1 + q / lambda) ^ alpha
  rw [one_add_div hl.ne', Real.div_rpow (add_nonneg hl.le hq) hl.le,
    Real.rpow_sub hl, Real.rpow_one]
  ring

theorem suAlphaLocalDensity_hasDerivAt (g : RiemannianMetric n M) (b : M)
    {alpha : ℝ} (ha : 1 ≤ alpha)
    (u phi : LoopPlane → EuclideanSpace ℝ (Fin n))
    (V : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin n)) (z : LoopPlane) (s : ℝ)
    (hs : u z + s • phi z ∈ (extChartAt (𝓡 n) b).target) :
    HasDerivAt
      (fun t : ℝ => suAlphaLocalDensity g b alpha z
        ((u z, (V 0 z, V 1 z)) + t • (phi z, suAlphaDerivativePair phi z)))
      (suAlphaChartVariation g b alpha (fun y => u y + s • phi y)
        (fun i y => V i y + s • fderiv ℝ phi y (EuclideanSpace.single i 1)) phi z) s := by
  let G := g.pullbackCoefficients (extChartAt (𝓡 n) b).symm
  let d := fun i : Fin 2 => fderiv ℝ phi z (EuclideanSpace.single i 1)
  let v := fun i : Fin 2 => V i z + s • d i
  let Q := fun t : ℝ => ∑ i : Fin 2,
    G (u z + t • phi z) (V i z + t • d i) (V i z + t • d i)
  let Q' := (∑ i : Fin 2, fderiv ℝ G (u z + s • phi z) (phi z) (v i) (v i)) +
    2 * ∑ i : Fin 2, G (u z + s • phi z) (v i) (d i)
  have hu : HasDerivAt (fun t : ℝ => u z + t • phi z) (phi z) s := by
    simpa using ((hasDerivAt_id s).smul_const (phi z)).const_add (u z)
  have hv (i : Fin 2) : HasDerivAt (fun t : ℝ => V i z + t • d i) (d i) s := by
    simpa using ((hasDerivAt_id s).smul_const (d i)).const_add (V i z)
  have hG : DifferentiableAt ℝ G (u z + s • phi z) :=
    ((g.contDiffOn_chartCoefficients b).contDiffAt
      ((isOpen_extChartAt_target b).mem_nhds hs)).differentiableAt (by simp)
  have hc := hG.hasFDerivAt.comp_hasDerivAt (l := G)
    (f := fun t : ℝ => u z + t • phi z) s hu
  have hsymm (i : Fin 2) : G (u z + s • phi z) (d i) (v i) =
      G (u z + s • phi z) (v i) (d i) := g.symm _ _ _
  have hQ : HasDerivAt Q Q' s := by
    have h := HasDerivAt.sum (u := Finset.univ)
      (fun i _ => (hc.clm_apply (hv i)).clm_apply (hv i))
    convert! h using 1
    simp only [Q', Fin.sum_univ_two, Function.comp_apply, add_apply]
    change _ = ((fderiv ℝ G (u z + s • phi z) (phi z) (v 0) +
      G (u z + s • phi z) (d 0)) (v 0) + G (u z + s • phi z) (v 0) (d 0)) +
      ((fderiv ℝ G (u z + s • phi z) (phi z) (v 1) +
      G (u z + s • phi z) (d 1)) (v 1) + G (u z + s • phi z) (v 1) (d 1))
    simp only [add_apply, hsymm]
    ring
  have hl : 0 < suAlphaRoundFactor z := by unfold suAlphaRoundFactor; positivity
  have h := (((hQ.div_const (suAlphaRoundFactor z)).const_add 1).rpow_const
    (Or.inr ha)).const_mul (suAlphaRoundFactor z)
  convert! h using 1
  · funext t
    simpa [suAlphaDerivativePair, Q, G, d] using
        localDensity_eq g b alpha z (u z + t • phi z)
          (V 0 z + t • d 0) (V 1 z + t • d 1)
  · change alpha * (1 + Q s / suAlphaRoundFactor z) ^ (alpha - 1) * Q' = _
    field_simp

theorem suAlphaChartVariation_bound (g : RiemannianMetric n M) (b : M)
    {alpha C P L : ℝ} (ha : 1 ≤ alpha) (hC : 0 ≤ C) (hP : 0 ≤ P) (hL : 0 ≤ L)
    (u phi : LoopPlane → EuclideanSpace ℝ (Fin n))
    (V : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin n)) (z : LoopPlane)
    (hB : ‖g.pullbackCoefficients (extChartAt (𝓡 n) b).symm (u z)‖ ≤ C)
    (hD : ‖fderiv ℝ (g.pullbackCoefficients (extChartAt (𝓡 n) b).symm) (u z)‖ ≤ C)
    (hphi : ‖phi z‖ ≤ P)
    (hd : ∀ i : Fin 2, ‖fderiv ℝ phi z (EuclideanSpace.single i 1)‖ ≤ P)
    (hl : (suAlphaRoundFactor z)⁻¹ ≤ L) :
    ‖suAlphaChartVariation g b alpha u V phi z‖ ≤
      (6 * alpha * C * P * (1 + 2 * C * L) ^ (alpha - 1)) *
        (1 + ‖(V 0 z, V 1 z)‖) ^ (2 * alpha) := by
  let G := g.pullbackCoefficients (extChartAt (𝓡 n) b).symm
  let A := 1 + ‖(V 0 z, V 1 z)‖
  let d := fun i : Fin 2 => fderiv ℝ phi z (EuclideanSpace.single i 1)
  let Q := ∑ i : Fin 2, G (u z) (V i z) (V i z)
  let T := (∑ i : Fin 2, fderiv ℝ G (u z) (phi z) (V i z) (V i z)) +
    2 * ∑ i : Fin 2, G (u z) (V i z) (d i)
  have hA : 1 ≤ A := le_add_of_nonneg_right (norm_nonneg _)
  have hA0 : 0 < A := by linarith
  have hv (i : Fin 2) : ‖V i z‖ ≤ A := by
    have hi : ‖V i z‖ ≤ ‖(V 0 z, V 1 z)‖ := by
      fin_cases i
      · exact norm_fst_le (V 0 z, V 1 z)
      · exact norm_snd_le (V 0 z, V 1 z)
    exact hi.trans (le_add_of_nonneg_left zero_le_one)
  have hquad (i : Fin 2) : ‖G (u z) (V i z) (V i z)‖ ≤ C * A ^ 2 := by
    calc
      _ ≤ ‖G (u z)‖ * ‖V i z‖ * ‖V i z‖ := (G (u z)).le_opNorm₂ _ _
      _ ≤ C * A * A := by gcongr <;> first | exact hB | exact hv i
      _ = _ := by ring
  have hmetric (i : Fin 2) :
      ‖fderiv ℝ G (u z) (phi z) (V i z) (V i z)‖ ≤ C * P * A ^ 2 := by
    calc
      _ ≤ ‖fderiv ℝ G (u z) (phi z)‖ * ‖V i z‖ * ‖V i z‖ :=
        (fderiv ℝ G (u z) (phi z)).le_opNorm₂ _ _
      _ ≤ ‖fderiv ℝ G (u z)‖ * ‖phi z‖ * ‖V i z‖ * ‖V i z‖ := by
        gcongr
        exact (fderiv ℝ G (u z)).le_opNorm _
      _ ≤ C * P * A * A := by gcongr <;> first | exact hD | exact hphi | exact hv i
      _ = _ := by ring
  have hlinear (i : Fin 2) : ‖G (u z) (V i z) (d i)‖ ≤ C * A * P := by
    calc
      _ ≤ ‖G (u z)‖ * ‖V i z‖ * ‖d i‖ := (G (u z)).le_opNorm₂ _ _
      _ ≤ C * A * P := by gcongr <;> first | exact hB | exact hv i | exact hd i
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg (fun i _ => coefficient_nonneg g b _ _)
  have hQ : Q ≤ 2 * C * A ^ 2 := by
    dsimp only [Q]
    rw [Fin.sum_univ_two]
    have h0 := (le_abs_self _).trans (hquad 0)
    have h1 := (le_abs_self _).trans (hquad 1)
    linarith
  have hT : ‖T‖ ≤ 6 * C * P * A ^ 2 := by
    have hsum := norm_add_le
      (fderiv ℝ G (u z) (phi z) (V 0 z) (V 0 z) +
        fderiv ℝ G (u z) (phi z) (V 1 z) (V 1 z))
      (2 * (G (u z) (V 0 z) (d 0) + G (u z) (V 1 z) (d 1)))
    rw [norm_mul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at hsum
    have hs0 := norm_add_le (fderiv ℝ G (u z) (phi z) (V 0 z) (V 0 z))
      (fderiv ℝ G (u z) (phi z) (V 1 z) (V 1 z))
    have hs1 := norm_add_le (G (u z) (V 0 z) (d 0)) (G (u z) (V 1 z) (d 1))
    have hp := mul_le_mul_of_nonneg_left (show A ≤ A ^ 2 by nlinarith)
      (show 0 ≤ 4 * C * P by positivity)
    dsimp only [T]
    rw [Fin.sum_univ_two, Fin.sum_univ_two]
    nlinarith [hmetric 0, hmetric 1, hlinear 0, hlinear 1]
  have hlam : 0 < suAlphaRoundFactor z := by unfold suAlphaRoundFactor; positivity
  have hbase : 1 + Q / suAlphaRoundFactor z ≤ (1 + 2 * C * L) * A ^ 2 := by
    have hdiv : Q / suAlphaRoundFactor z ≤ (2 * C * A ^ 2) * L := by
      rw [div_eq_mul_inv]
      exact mul_le_mul hQ hl (inv_nonneg.mpr hlam.le) (by positivity)
    nlinarith [sq_nonneg A]
  have hpower : (1 + Q / suAlphaRoundFactor z) ^ (alpha - 1) ≤
      (1 + 2 * C * L) ^ (alpha - 1) * A ^ (2 * (alpha - 1)) := by
    calc
      _ ≤ ((1 + 2 * C * L) * A ^ 2) ^ (alpha - 1) :=
        Real.rpow_le_rpow (by positivity) hbase (by linarith)
      _ = _ := by
        rw [Real.mul_rpow (by positivity) (sq_nonneg A), ← Real.rpow_natCast,
          ← Real.rpow_mul hA0.le]
        norm_num
  change ‖alpha * (1 + Q / suAlphaRoundFactor z) ^ (alpha - 1) * T‖ ≤ _
  rw [norm_mul, norm_mul, Real.norm_of_nonneg (by linarith : 0 ≤ alpha),
    Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  calc
    _ ≤ (alpha * ((1 + 2 * C * L) ^ (alpha - 1) * A ^ (2 * (alpha - 1)))) *
        (6 * C * P * A ^ 2) := by gcongr
    _ = (6 * alpha * C * P * (1 + 2 * C * L) ^ (alpha - 1)) * A ^ (2 * alpha) := by
      rw [show A ^ (2 : ℕ) = A ^ (2 : ℝ) by rw [Real.rpow_two]]
      rw [show A ^ (2 * alpha) = A ^ (2 * (alpha - 1)) * A ^ (2 : ℝ) by
        rw [← Real.rpow_add hA0]; congr 1; ring]
      ring

private theorem ae_clm_apply {X E F : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {m0 : MeasurableSpace X} {mu : Measure[m0] X}
    {A : X → E →L[ℝ] F} {v : X → E}
    (hA : AEStronglyMeasurable A mu) (hv : AEStronglyMeasurable v mu) :
    AEStronglyMeasurable (fun z => A z (v z)) mu :=
  (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable (hA.prodMk hv)

set_option maxHeartbeats 1000000 in

theorem suAlpha_integral_firstVariation (g : RiemannianMetric n M) (b : M)
    {alpha : ℝ} (ha : 1 ≤ alpha)
    (u phi : LoopPlane → EuclideanSpace ℝ (Fin n)) (hu : Continuous u)
    (hphi : ContDiff ℝ ∞ phi) (V : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin n))
    (x : LoopPlane) (R : ℝ)
    (hV : ∀ i, MemLp (V i) (ENNReal.ofReal (2 * alpha))
      (volume.restrict (Metric.ball x R)))
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K)
    (hKt : K ⊆ (extChartAt (𝓡 n) b).target) {delta : ℝ} (hdelta : 0 < delta)
    (hrange : ∀ t : ℝ, |t| < delta → ∀ z ∈ Metric.closedBall x R,
      u z + t • phi z ∈ K)
    (hint : IntegrableOn (fun z => suAlphaLocalDensity g b alpha z
      (u z, (V 0 z, V 1 z))) (Metric.ball x R)) :
    IntegrableOn (suAlphaChartVariation g b alpha u V phi) (Metric.ball x R) ∧
      HasDerivAt
        (fun t : ℝ => ∫ z in Metric.ball x R, suAlphaLocalDensity g b alpha z
          ((u z, (V 0 z, V 1 z)) + t • (phi z, suAlphaDerivativePair phi z)))
        (∫ z in Metric.ball x R, suAlphaChartVariation g b alpha u V phi z) 0 := by
  let mu := volume.restrict (Metric.ball x R)
  let S := Metric.closedBall x R
  let G := g.pullbackCoefficients (extChartAt (𝓡 n) b).symm
  let U := fun (t : ℝ) (z : LoopPlane) => u z + t • phi z
  let W := fun (t : ℝ) (i : Fin 2) (z : LoopPlane) =>
    V i z + t • fderiv ℝ phi z (EuclideanSpace.single i 1)
  let F := fun (t : ℝ) (z : LoopPlane) => suAlphaLocalDensity g b alpha z
    ((u z, (V 0 z, V 1 z)) + t • (phi z, suAlphaDerivativePair phi z))
  let F' := fun t => suAlphaChartVariation g b alpha (U t) (W t) phi
  let A := fun z => 1 + ‖V 0 z‖ + ‖V 1 z‖
  let : IsFiniteMeasure mu := isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have hGB : ContinuousOn G K := (g.contDiffOn_chartCoefficients b).continuousOn.mono hKt
  have hGD : ContinuousOn (fderiv ℝ G) K :=
    ((g.contDiffOn_chartCoefficients b).continuousOn_fderiv_of_isOpen
      (isOpen_extChartAt_target b) (by simp)).mono hKt
  obtain ⟨C0, hC0⟩ := hK.bddAbove_image
    ((continuous_norm.comp_continuousOn hGB).add (continuous_norm.comp_continuousOn hGD))
  let C := max C0 1
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hcoeff (y) (hy : y ∈ K) : ‖G y‖ ≤ C ∧ ‖fderiv ℝ G y‖ ≤ C := by
    have hh := (hC0 (mem_image_of_mem _ hy)).trans (le_max_left C0 1)
    exact ⟨le_trans (le_add_of_nonneg_right (norm_nonneg _)) hh,
      le_trans (le_add_of_nonneg_left (norm_nonneg _)) hh⟩
  have hdcont := hphi.continuous_fderiv (by simp)
  obtain ⟨P0, hP0⟩ := (isCompact_closedBall x R).bddAbove_image
    ((hphi.continuous.norm.add hdcont.norm).continuousOn)
  let P := max P0 1
  have hP : 0 < P := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have htest (z) (hz : z ∈ S) : ‖phi z‖ ≤ P ∧
      ∀ i : Fin 2, ‖fderiv ℝ phi z (EuclideanSpace.single i 1)‖ ≤ P := by
    have hh := (hP0 (mem_image_of_mem _ hz)).trans (le_max_left P0 1)
    refine ⟨le_trans (le_add_of_nonneg_right (norm_nonneg _)) hh, fun i => ?_⟩
    have hd := (fderiv ℝ phi z).le_opNorm (EuclideanSpace.single i 1)
    simp only [EuclideanSpace.single, PiLp.norm_single, norm_one, mul_one] at hd
    exact hd.trans (le_trans (le_add_of_nonneg_left (norm_nonneg _)) hh)
  have hlam : Continuous suAlphaRoundFactor := continuous_const.div₀
    (((continuous_norm.pow 2).add continuous_const).pow 2) (fun _ => by positivity)
  have hlam0 (z) : 0 < suAlphaRoundFactor z := by unfold suAlphaRoundFactor; positivity
  have hinv := hlam.inv₀ (fun z => (hlam0 z).ne')
  obtain ⟨L0, hL0⟩ := (isCompact_closedBall x R).bddAbove_image hinv.continuousOn
  let L := max L0 1
  have hL : 0 < L := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  let D := 6 * alpha * C * P * (1 + 2 * C * L) ^ (alpha - 1)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hA : MemLp A (ENNReal.ofReal (2 * alpha)) mu :=
    ((memLp_const (1 : ℝ)).add (hV 0).norm).add (hV 1).norm
  have hpower : Integrable (fun z => A z ^ (2 * alpha)) mu := by
    have hp := hA.integrable_norm_rpow
      (by simp; linarith : ENNReal.ofReal (2 * alpha) ≠ 0) ENNReal.ofReal_ne_top
    have hn (z) : ‖A z‖ = A z := Real.norm_of_nonneg (by dsimp [A]; positivity)
    simpa only [ENNReal.toReal_ofReal (by linarith : 0 ≤ 2 * alpha), hn] using hp
  let bound := fun z => (D * (1 + P) ^ (2 * alpha)) * A z ^ (2 * alpha)
  have hboundInt : Integrable bound mu := hpower.const_mul _
  have hU (t) : Continuous (U t) := hu.add (hphi.continuous.const_smul t)
  have hW (t i) : AEStronglyMeasurable (W t i) mu :=
    (hV i).1.add (((hdcont.clm_apply continuous_const).const_smul t).aestronglyMeasurable)
  have hGmeas (t) (ht : |t| < delta) :
      AEStronglyMeasurable (fun z => G (U t z)) mu ∧
        AEStronglyMeasurable (fun z => fderiv ℝ G (U t z)) mu := by
    have hmap : MapsTo (U t) (Metric.ball x R) K := fun z hz =>
      hrange t ht z (Metric.ball_subset_closedBall hz)
    exact ⟨(hGB.comp (hU t).continuousOn hmap).aestronglyMeasurable measurableSet_ball,
      (hGD.comp (hU t).continuousOn hmap).aestronglyMeasurable measurableSet_ball⟩
  have hQmeas (t) (ht : |t| < delta) : AEStronglyMeasurable
      (fun z => ∑ i : Fin 2, G (U t z) (W t i z) (W t i z)) mu := by
    convert!
      (ae_clm_apply (ae_clm_apply (hGmeas t ht).1 (hW t 0)) (hW t 0)).add
        (ae_clm_apply (ae_clm_apply (hGmeas t ht).1 (hW t 1)) (hW t 1)) using 1
    simp only [Fin.sum_univ_two, Pi.add_def]
  have hFmeas (t) (ht : |t| < delta) : AEStronglyMeasurable (F t) mu := by
    have hh := hlam.aestronglyMeasurable.mul
      ((Real.continuous_rpow_const (by linarith : 0 ≤ alpha)).comp_aestronglyMeasurable
        ((aestronglyMeasurable_const (b := (1 : ℝ))).add
          ((hQmeas t ht).div₀ hlam.aestronglyMeasurable)))
    convert! hh using 1
    funext z
    simpa [F, U, W, Fin.sum_univ_two, G, suAlphaDerivativePair] using
      localDensity_eq g b alpha z (U t z) (W t 0 z) (W t 1 z)
  have hF'meas : AEStronglyMeasurable (F' 0) mu := by
    have hzero : |(0 : ℝ)| < delta := by simpa using hdelta
    have hmetric (i : Fin 2) : AEStronglyMeasurable
        (fun z => fderiv ℝ G (U 0 z) (phi z) (W 0 i z) (W 0 i z)) mu :=
      ae_clm_apply (ae_clm_apply (ae_clm_apply (hGmeas 0 hzero).2
        hphi.continuous.aestronglyMeasurable) (hW 0 i)) (hW 0 i)
    have hflux (i : Fin 2) : AEStronglyMeasurable
        (fun z => G (U 0 z) (W 0 i z) (fderiv ℝ phi z (EuclideanSpace.single i 1))) mu :=
      ae_clm_apply (ae_clm_apply (hGmeas 0 hzero).1 (hW 0 i))
        (hdcont.clm_apply continuous_const).aestronglyMeasurable
    have hp := (Real.continuous_rpow_const (by linarith : 0 ≤ alpha - 1)).comp_aestronglyMeasurable
      ((aestronglyMeasurable_const (b := (1 : ℝ))).add
        ((hQmeas 0 hzero).div₀ hlam.aestronglyMeasurable))
    have hh := ((aestronglyMeasurable_const (b := alpha)).mul hp).mul
      ((hmetric 0).add (hmetric 1) |>.add
        ((aestronglyMeasurable_const (b := (2 : ℝ))).mul ((hflux 0).add (hflux 1))))
    convert! hh using 1
    funext z
    simp only [F', suAlphaChartVariation, Fin.sum_univ_two, Pi.mul_apply, Pi.add_apply,
      Pi.div_apply]
    simp [G]
  have hdiff : ∀ᵐ z ∂mu, ∀ t ∈ Metric.ball (0 : ℝ) (min delta 1),
      HasDerivAt (fun s => F s z) (F' t z) t := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz t ht
    have ht' : |t| < delta := lt_of_lt_of_le
      (by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using ht) (min_le_left _ _)
    exact suAlphaLocalDensity_hasDerivAt g b ha u phi V z t
      (hKt (hrange t ht' z (Metric.ball_subset_closedBall hz)))
  have hbound : ∀ᵐ z ∂mu, ∀ t ∈ Metric.ball (0 : ℝ) (min delta 1),
      ‖F' t z‖ ≤ bound z := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz t ht
    have ht0 : |t| < min delta 1 := by
      simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using ht
    have ht' := lt_of_lt_of_le ht0 (min_le_left _ _)
    have ht1 : |t| ≤ 1 := (lt_of_lt_of_le ht0 (min_le_right _ _)).le
    have hzS := Metric.ball_subset_closedBall hz
    have hc := hcoeff (U t z) (hrange t ht' z hzS)
    have htestz := htest z hzS
    have hvl (i : Fin 2) : ‖W t i z‖ ≤ ‖V i z‖ + P := by
      calc
        _ ≤ ‖V i z‖ + ‖t • fderiv ℝ phi z (EuclideanSpace.single i 1)‖ := norm_add_le _ _
        _ ≤ ‖V i z‖ + P := by
          rw [norm_smul, Real.norm_eq_abs]
          simpa only [one_mul] using add_le_add_right
            (mul_le_mul ht1 (htestz.2 i) (norm_nonneg _) zero_le_one) ‖V i z‖
    have hnorm : 1 + ‖(W t 0 z, W t 1 z)‖ ≤ (1 + P) * A z := by
      rw [Prod.norm_def, add_max]
      apply max_le
      · dsimp only [A]
        nlinarith [hvl 0, norm_nonneg (V 0 z), norm_nonneg (V 1 z)]
      · dsimp only [A]
        nlinarith [hvl 1, norm_nonneg (V 0 z), norm_nonneg (V 1 z)]
    have hh := suAlphaChartVariation_bound g b ha hC.le hP.le hL.le (U t) phi (W t) z
      hc.1 hc.2 htestz.1 htestz.2
        ((hL0 (mem_image_of_mem _ hzS)).trans (le_max_left L0 1))
    refine hh.trans ?_
    change D * (1 + ‖(W t 0 z, W t 1 z)‖) ^ (2 * alpha) ≤
      (D * (1 + P) ^ (2 * alpha)) * A z ^ (2 * alpha)
    calc
      _ ≤ D * ((1 + P) * A z) ^ (2 * alpha) := by gcongr
      _ = _ := by rw [Real.mul_rpow (by positivity) (by dsimp [A]; positivity)]; ring
  have hh := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds (0 : ℝ) (lt_min hdelta zero_lt_one))
    (Filter.mem_of_superset (Metric.ball_mem_nhds (0 : ℝ) hdelta)
      (fun t ht => hFmeas t (by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using ht)))
    (show Integrable (F 0) mu by simpa only [F, zero_smul, add_zero, IntegrableOn, mu] using hint)
    hF'meas hbound hboundInt hdiff
  simpa only [F', F, U, W, zero_smul, add_zero, IntegrableOn, mu] using hh

end PoincareConjecture.M60
