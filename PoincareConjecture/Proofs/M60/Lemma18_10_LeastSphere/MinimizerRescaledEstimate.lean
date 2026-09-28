import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerRescaling

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff

noncomputable section

universe u

namespace PoincareConjecture

open M60

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem m60AlphaMap_rescaled_small_energy [CompactSpace M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g) :
    ∃ epsilon C : ℝ, 0 < epsilon ∧ 0 < C ∧
      ∀ (a : LoopPlane) (s rho alpha R : ℝ),
        0 < s → 0 < rho → 1 ≤ alpha → alpha ≤ 33 / 32 → 0 < R → R ≤ 1 →
      ∀ f : LoopPlane → M, ContMDiff (𝓡 2) (𝓡 n) ∞ f →
      ∀ lambda : LoopPlane → ℝ, ContDiff ℝ ∞ lambda → (∀ x, 0 < lambda x) →
      let A := fun z : LoopPlane => a + s • z
      let l := lambda ∘ A
      let q := fun x => 2 * m60EnergyDensity g f x / lambda x
      (∀ z ∈ Metric.closedBall 0 R, 1 / 4 ≤ l z ∧ l z ≤ 4 ∧
        (fderiv ℝ l z (EuclideanSpace.basisFun (Fin 2) ℝ 0)) ^ 2 +
          (fderiv ℝ l z (EuclideanSpace.basisFun (Fin 2) ℝ 1)) ^ 2 ≤ 256 ∧
        (∑ i : Fin 2, fderiv ℝ (fun w => fderiv ℝ l w
          (EuclideanSpace.basisFun (Fin 2) ℝ i)) z
            (EuclideanSpace.basisFun (Fin 2) ℝ i)) ≤ 64) →
      (∀ b : M, ∀ x ∈ A '' Metric.ball 0 R, f x ∈ (extChartAt (𝓡 n) b).source →
        let u := extChartAt (𝓡 n) b ∘ f
        let Gamma := CoordinateExponential.christoffelBilinear
          (g.pullbackCoefficients (extChartAt (𝓡 n) b).symm)
        ∑ i : Fin 2, ConnectionVariation.covDerivAlong Gamma u
          (fun y => (rho ^ 2 + q y) ^ (alpha - 1) •
            fderiv ℝ u y (EuclideanSpace.basisFun (Fin 2) ℝ i))
              (EuclideanSpace.basisFun (Fin 2) ℝ i) x = 0) →
      (∫ x in A '' Metric.closedBall 0 R, m60EnergyDensity g f x) ≤ epsilon →
      (s * R) ^ 2 * q a ≤ C *
        (∫ x in A '' Metric.closedBall 0 R, m60EnergyDensity g f x) := by
  obtain ⟨epsilon, C, hepsilon, hC, hestimate⟩ := m60AlphaMap_small_energy D
  refine ⟨epsilon / 8, 8 * C, by positivity, by positivity, ?_⟩
  intro a s rho alpha R hs hrho ha ha' hR hR' f hf lambda hl hlpos
  let A := fun z : LoopPlane => a + s • z
  let l := lambda ∘ A
  let q := fun x => 2 * m60EnergyDensity g f x / lambda x
  change (∀ z ∈ Metric.closedBall 0 R, _) → _
  intro hlbound heq hsmall
  let v := f ∘ A
  let qv := fun z => 2 * m60EnergyDensity g v z / l z
  have hA : ContDiff ℝ ∞ A := contDiff_const.add (contDiff_id.const_smul s)
  have hv : ContMDiff (𝓡 2) (𝓡 n) ∞ v := hf.comp hA.contMDiff
  have hl' : ContDiff ℝ ∞ l := hl.comp hA
  have hlpos' (z : LoopPlane) : 0 < l z := hlpos _
  have hq (z : LoopPlane) : 0 ≤ q z :=
    div_nonneg (mul_nonneg (by norm_num) (m60EnergyDensity_nonneg g f z)) (hlpos z).le
  have hqv (z : LoopPlane) : qv z = s ^ 2 * q (A z) := by
    dsimp only [qv, v, l, q, A, Function.comp_def]
    rw [suRescale_energyDensity g f (hf.mdifferentiable (by simp))]
    ring
  have heqv : ∀ b : M, ∀ z ∈ Metric.ball 0 R,
      v z ∈ (extChartAt (𝓡 n) b).source →
      let u := extChartAt (𝓡 n) b ∘ v
      let Gamma := CoordinateExponential.christoffelBilinear
        (g.pullbackCoefficients (extChartAt (𝓡 n) b).symm)
      ∑ i : Fin 2, ConnectionVariation.covDerivAlong Gamma u
        (fun y => ((s * rho) ^ 2 + qv y) ^ (alpha - 1) •
          fderiv ℝ u y (EuclideanSpace.basisFun (Fin 2) ℝ i))
            (EuclideanSpace.basisFun (Fin 2) ℝ i) z = 0 := by
    intro b z hz hb
    let u := extChartAt (𝓡 n) b ∘ f
    let Gamma := CoordinateExponential.christoffelBilinear
      (g.pullbackCoefficients (extChartAt (𝓡 n) b).symm)
    have hbase := heq b (A z) ⟨z, hz, rfl⟩ hb
    have h := suRescale_weightedEuler Gamma u q hq a s rho alpha z
    change _ = (s ^ 2 * (s ^ 2) ^ (alpha - 1)) •
      (∑ i : Fin 2, ConnectionVariation.covDerivAlong Gamma u
        (fun y => (rho ^ 2 + q y) ^ (alpha - 1) •
          fderiv ℝ u y (EuclideanSpace.basisFun (Fin 2) ℝ i))
            (EuclideanSpace.basisFun (Fin 2) ℝ i) (A z)) at h
    rw [hbase, smul_zero] at h
    simpa only [hqv, u, Gamma, v, A, Function.comp_def] using h
  have heint : IntegrableOn (m60EnergyDensity g v) (Metric.closedBall 0 R) :=
    (m60EnergyDensity_continuous g (hv.of_le (by simp))).continuousOn.integrableOn_compact
      (isCompact_closedBall _ _)
  have hqint : IntegrableOn qv (Metric.closedBall 0 R) :=
    ((continuous_const.mul (m60EnergyDensity_continuous g (hv.of_le (by simp)))).div₀
      hl'.continuous (fun z => (hlpos' z).ne')).continuousOn.integrableOn_compact
        (isCompact_closedBall _ _)
  have hqle : (∫ z in Metric.closedBall 0 R, qv z) ≤
      8 * ∫ z in Metric.closedBall 0 R, m60EnergyDensity g v z := by
    rw [← integral_const_mul]
    apply setIntegral_mono_on hqint (heint.const_mul 8) measurableSet_closedBall
    intro z hz
    change 2 * m60EnergyDensity g v z / l z ≤ 8 * m60EnergyDensity g v z
    apply (div_le_iff₀ (hlpos' z)).mpr
    have he := m60EnergyDensity_nonneg g v z
    have hlz := (hlbound z hz).1
    nlinarith
  have henergy : (∫ z in Metric.closedBall 0 R, m60EnergyDensity g v z) =
      ∫ z in A '' Metric.closedBall 0 R, m60EnergyDensity g f z :=
    suRescale_energyIntegral g f (hf.mdifferentiable (by simp)) a hs _
  rw [henergy] at hqle
  have hqsmall : (∫ z in Metric.closedBall 0 R, qv z) ≤ epsilon := by linarith
  have h := hestimate (s * rho) alpha R (mul_pos hs hrho) ha ha' hR hR' v hv l hl' hlpos'
    (fun z hz => hlbound z (Metric.ball_subset_closedBall hz)) heqv hqsmall
  change R ^ 2 * qv 0 ≤ C * _ at h
  rw [hqv] at h
  simp only [A, smul_zero, add_zero] at h
  have hmul := mul_le_mul_of_nonneg_left hqle hC.le
  calc
    (s * R) ^ 2 * q a = R ^ 2 * (s ^ 2 * q a) := by ring
    _ ≤ C * (∫ z in Metric.closedBall 0 R, qv z) := h
    _ ≤ C * (8 * ∫ z in A '' Metric.closedBall 0 R, m60EnergyDensity g f z) := hmul
    _ = _ := by ring

end PoincareConjecture

end
