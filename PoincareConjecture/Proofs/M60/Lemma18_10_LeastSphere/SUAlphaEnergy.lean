import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.IntrinsicEnergy
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.NonNullSphere
import Mathlib.Topology.Order.IsLUB
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import PoincareConjecture.Proofs.M40.Mathlib.LipschitzSmoothingRiemannian
import Mathlib.Topology.Semicontinuity.Basic
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.Sobolev.Embedding.MorreySmoothInequality
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Analysis.InnerProductSpace.Dual
import PoincareConjecture.Proofs.M60.Mathlib.SUConvexIntegral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import PoincareConjecture.Proofs.M60.Mathlib.SURegularizedQuadratic
import PoincareConjecture.Proofs.M60.Mathlib.SUMovingQuadratic
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Topology.ContinuousMap.Compact
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.CompactEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology Bundle BoundedContinuousFunction

noncomputable section

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

def m60SphereAlphaEnergy (g : RiemannianMetric n M) (alpha : ℝ)
    (f : UnitTwoSphere → M) : ℝ :=
  ∫ p, (1 + 2 * m60SphereIntrinsicEnergy g f p) ^ alpha
    ∂m60RoundSphereMetric.volumeMeasure

theorem m60SphereIntrinsicEnergy_nonneg (g : RiemannianMetric n M)
    (f : UnitTwoSphere → M) (p : UnitTwoSphere) :
    0 ≤ m60SphereIntrinsicEnergy g f p := by
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro i _
  by_cases h : mfderiv (𝓡 2) (𝓡 n) f p
      (m60RoundSphereMetric.orthonormalBasis p i) = 0
  · simp [h]
  · exact (g.pos _ _ h).le

theorem m60SphereAlphaEnergy_integrable (g : RiemannianMetric n M)
    (alpha : ℝ) (f : UnitTwoSphere → M) (hf : ContMDiff (𝓡 2) (𝓡 n) ∞ f) :
    Integrable (fun p => (1 + 2 * m60SphereIntrinsicEnergy g f p) ^ alpha)
      m60RoundSphereMetric.volumeMeasure := by
  have hbase : Continuous (fun p => 1 + 2 * m60SphereIntrinsicEnergy g f p) :=
    continuous_const.add (continuous_const.mul
      (m60SphereIntrinsicEnergy_contMDiff g f hf).continuous)
  have hcont : Continuous (fun p => (1 + 2 * m60SphereIntrinsicEnergy g f p) ^ alpha) :=
    hbase.rpow_const fun p => Or.inl (by
      have := m60SphereIntrinsicEnergy_nonneg g f p
      positivity)
  exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem m60SphereAlphaEnergy_nonneg (g : RiemannianMetric n M)
    (alpha : ℝ) (f : UnitTwoSphere → M) : 0 ≤ m60SphereAlphaEnergy g alpha f := by
  apply integral_nonneg
  intro p
  exact Real.rpow_nonneg (by
    have := m60SphereIntrinsicEnergy_nonneg g f p
    positivity) _

theorem m60SphereAlphaEnergy_one (g : RiemannianMetric n M)
    (f : UnitTwoSphere → M) (hf : ContMDiff (𝓡 2) (𝓡 n) ∞ f) :
    m60SphereAlphaEnergy g 1 f = 4 * Real.pi + 2 * m60SphereEnergy g f := by
  have hi : Integrable (m60SphereIntrinsicEnergy g f)
      m60RoundSphereMetric.volumeMeasure :=
    (m60SphereIntrinsicEnergy_contMDiff g f hf).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  simp only [m60SphereAlphaEnergy, Real.rpow_one]
  rw [integral_add (integrable_const _) (hi.const_mul _), integral_const,
    integral_const_mul, m60RoundSphereMetric_volume_univ,
    m60SphereEnergy_eq_intrinsic_integral g f hf]
  simp

theorem m60SphereEnergy_le_alphaEnergy (g : RiemannianMetric n M)
    {alpha : ℝ} (halpha : 1 ≤ alpha)
    (f : UnitTwoSphere → M) (hf : ContMDiff (𝓡 2) (𝓡 n) ∞ f) :
    4 * Real.pi + 2 * m60SphereEnergy g f ≤ m60SphereAlphaEnergy g alpha f := by
  rw [← m60SphereAlphaEnergy_one g f hf]
  apply integral_mono (m60SphereAlphaEnergy_integrable g 1 f hf)
    (m60SphereAlphaEnergy_integrable g alpha f hf)
  intro p
  exact Real.rpow_le_rpow_of_exponent_le (by
    have := m60SphereIntrinsicEnergy_nonneg g f p
    linarith) halpha

theorem m60SphereAlphaEnergy_uniform_competitor_bound (g : RiemannianMetric n M)
    (f : UnitTwoSphere → M) (hf : ContMDiff (𝓡 2) (𝓡 n) ∞ f) :
    ∃ C : ℝ, 0 < C ∧ ∀ alpha : ℝ, 1 ≤ alpha → alpha ≤ 2 →
      m60SphereAlphaEnergy g alpha f < C := by
  refine ⟨m60SphereAlphaEnergy g 2 f + 1,
    by have := m60SphereAlphaEnergy_nonneg g 2 f; linarith, fun alpha _ htwo => ?_⟩
  apply lt_of_le_of_lt (b := m60SphereAlphaEnergy g 2 f) ?_ (by linarith)
  apply integral_mono (m60SphereAlphaEnergy_integrable g alpha f hf)
    (m60SphereAlphaEnergy_integrable g 2 f hf)
  intro p
  exact Real.rpow_le_rpow_of_exponent_le
    (by have := m60SphereIntrinsicEnergy_nonneg g f p; linarith) htwo

namespace M60

theorem suAlpha_coordinate_metric_bounds
    (g : RiemannianMetric n M) (b : M) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsCompact K) (hKt : K ⊆ (extChartAt (𝓡 n) b).target) :
    let B := g.pullbackCoefficients (extChartAt (𝓡 n) b).symm
    ∃ a C : ℝ, 0 < a ∧ 0 ≤ C ∧ UniformContinuousOn B K ∧
      (∀ y ∈ K, ‖B y‖ ≤ C) ∧ ∀ y ∈ K, ∀ v, a * ‖v‖ ^ 2 ≤ B y v v := by
  let B := g.pullbackCoefficients (extChartAt (𝓡 n) b).symm
  have hB : ContinuousOn B K := (g.contDiffOn_chartCoefficients b).continuousOn.mono hKt
  obtain ⟨a, ha, hab⟩ := exists_uniform_bilinear_lower_bound hK hB (by
    intro y hy v hv
    have hAv : mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) b).symm y v ≠ 0 := by
      intro hzero
      obtain ⟨e, he⟩ := g.isInvertible_chartCoefficients b (hKt hy)
      apply hv
      apply e.injective
      change (e : EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) v = e 0
      rw [map_zero, he]
      ext w
      change g.inner ((extChartAt (𝓡 n) b).symm y)
        (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) b).symm y v)
        (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) b).symm y w) = 0
      rw [hzero]
      simp +instances only [map_zero, zero_apply]
    exact g.pos _ _ hAv)
  have hnorm : ContinuousOn (fun y => ‖B y‖) K :=
    (continuous_norm (E := EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)).comp_continuousOn hB
  obtain ⟨C, hC⟩ := hK.bddAbove_image hnorm
  exact ⟨a, max C 0, ha, le_max_right _ _, hK.uniformContinuousOn_of_continuous hB,
    fun y hy => (hC ⟨y, hy, rfl⟩).trans (le_max_left _ _), hab⟩

theorem plane_opNorm_sq_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : LoopPlane →L[ℝ] F) : ‖L‖ ^ 2 ≤
      2 * (‖L (EuclideanSpace.basisFun (Fin 2) ℝ 0)‖ ^ 2 +
        ‖L (EuclideanSpace.basisFun (Fin 2) ℝ 1)‖ ^ 2) := by
  let b := EuclideanSpace.basisFun (Fin 2) ℝ
  have hb : ‖L‖ ≤ ∑ i, ‖L (b i)‖ := by
    apply L.opNorm_le_bound (Finset.sum_nonneg fun i _ => norm_nonneg _) (fun x => ?_)
    have hx := congrArg L (b.sum_repr x)
    simp only [map_sum, map_smul] at hx
    calc
      ‖L x‖ = ‖∑ i, b.repr x i • L (b i)‖ := congrArg norm hx.symm
      _ ≤ ∑ i, ‖b.repr x i • L (b i)‖ := norm_sum_le _ _
      _ ≤ ∑ i, ‖x‖ * ‖L (b i)‖ := by
        apply Finset.sum_le_sum
        intro i _
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_right
          ((PiLp.norm_apply_le (b.repr x) i).trans_eq (b.repr.norm_map x)) (norm_nonneg _)
      _ = (∑ i, ‖L (b i)‖) * ‖x‖ := by rw [← Finset.mul_sum]; ring
  rw [Fin.sum_univ_two] at hb
  have hs := sq_le_sq₀ (norm_nonneg L) (add_nonneg (norm_nonneg _) (norm_nonneg _)) |>.mpr hb
  dsimp only [b] at hs
  nlinarith [sq_nonneg (‖L (EuclideanSpace.basisFun (Fin 2) ℝ 0)‖ -
    ‖L (EuclideanSpace.basisFun (Fin 2) ℝ 1)‖)]

theorem exists_uniform_mfderiv_bound [CompactSpace M]
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (g : RiemannianMetric n M) (e : M → F)
    (he : ContMDiff (𝓡 n) 𝓘(ℝ, F) 1 e) :
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x, ‖mfderiv (𝓡 n) 𝓘(ℝ, F) e x‖ ≤ B := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let : IsContinuousRiemannianBundle F (TangentSpace 𝓘(ℝ, F) : F → Type _) :=
    ⟨⟨(riemannianMetricVectorSpace F).inner,
      (riemannianMetricVectorSpace F).contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  have hupper : UpperSemicontinuous (fun x => ‖mfderiv (𝓡 n) 𝓘(ℝ, F) e x‖) := by
    intro x B hB
    exact M40.eventually_norm_mfderiv_lt (he x) hB
  obtain ⟨B, hB⟩ := (hupper.upperSemicontinuousOn univ).bddAbove_of_isCompact isCompact_univ
  refine ⟨max B 0, le_max_right _ _, fun x => ?_⟩
  exact (hB ⟨x, mem_univ _, rfl⟩).trans (le_max_left _ _)

theorem exists_observed_derivative_energy_bound [CompactSpace M]
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (g : RiemannianMetric n M) (e : M → F)
    (he : ContMDiff (𝓡 n) 𝓘(ℝ, F) 1 e) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (f : LoopPlane → M), ContMDiff (𝓡 2) (𝓡 n) 1 f →
      ∀ z (i : Fin 2),
        ‖fderiv ℝ (e ∘ f) z (EuclideanSpace.basisFun (Fin 2) ℝ i)‖ ^ 2 ≤
          B * m60EnergyDensity g f z := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  obtain ⟨B, hB, hbound⟩ := exists_uniform_mfderiv_bound g e he
  refine ⟨2 * B ^ 2, by positivity, fun f hf z i => ?_⟩
  let v := mfderiv (𝓡 2) (𝓡 n) f z (EuclideanSpace.basisFun (Fin 2) ℝ i)
  have hnorm : ‖(show F from mfderiv (𝓡 n) 𝓘(ℝ, F) e (f z) v)‖ ≤ B * ‖v‖ := by
    rw [← norm_tangentSpace_vectorSpace (x := e (f z))]
    exact ((mfderiv (𝓡 n) 𝓘(ℝ, F) e (f z)).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (hbound _) (norm_nonneg _))
  have hder : fderiv ℝ (e ∘ f) z (EuclideanSpace.basisFun (Fin 2) ℝ i) =
      mfderiv (𝓡 n) 𝓘(ℝ, F) e (f z) v := by
    rw [← mfderiv_eq_fderiv, mfderiv_comp z (he.mdifferentiable (by simp) _)
      (hf.mdifferentiable (by simp) _)]
    rfl
  have hv : ‖v‖ ^ 2 = m60AreaGram g f z i i := (real_inner_self_eq_norm_sq v).symm
  have hcolumn : ‖v‖ ^ 2 ≤ 2 * m60EnergyDensity g f z := by
    rw [hv, m60EnergyDensity, Matrix.trace_fin_two]
    have h0 := m60AreaGram_diagonal_nonneg g f z 0
    have h1 := m60AreaGram_diagonal_nonneg g f z 1
    fin_cases i
    · change m60AreaGram g f z 0 0 ≤ 2 * (1 / 2 *
        (m60AreaGram g f z 0 0 + m60AreaGram g f z 1 1))
      linarith
    · change m60AreaGram g f z 1 1 ≤ 2 * (1 / 2 *
        (m60AreaGram g f z 0 0 + m60AreaGram g f z 1 1))
      linarith
  rw [hder]
  have hsquare := mul_self_le_mul_self (norm_nonneg _) hnorm
  nlinarith [mul_le_mul_of_nonneg_left hcolumn (sq_nonneg B)]

theorem suAlpha_coercivity_rpow {r B a E alpha : ℝ}
    (hr : 0 ≤ r) (hB : 0 ≤ B) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hE : 0 ≤ E) (halpha : 1 ≤ alpha) (hder : r ^ 2 ≤ B * (E * a)) :
    r ^ (2 * alpha) ≤ B ^ alpha * (1 + 2 * E) ^ alpha * a := by
  have hlarge : r ^ 2 ≤ B * (1 + 2 * E) * a := hder.trans (by
    nlinarith [mul_nonneg (mul_nonneg hB ha0) hE, mul_nonneg hB ha0])
  calc
    _ = (r ^ 2) ^ alpha := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hr]
      norm_num
    _ ≤ (B * (1 + 2 * E) * a) ^ alpha :=
      Real.rpow_le_rpow (sq_nonneg _) hlarge (by linarith)
    _ = B ^ alpha * (1 + 2 * E) ^ alpha * a ^ alpha := by
      rw [Real.mul_rpow (mul_nonneg hB (by positivity)) ha0,
        Real.mul_rpow hB (by positivity)]
    _ ≤ B ^ alpha * (1 + 2 * E) ^ alpha * a :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_self_of_le_one ha0 ha1 halpha) (by positivity)

end M60

def m60NonNullAlphaEnergyValues (g : RiemannianMetric n M) (alpha : ℝ) : Set ℝ :=
  {r | ∃ f : UnitTwoSphere → M, ContMDiff (𝓡 2) (𝓡 n) ∞ f ∧
    ¬ IsNullHomotopicSphere f ∧ m60SphereAlphaEnergy g alpha f = r}

theorem m60NonNullAlphaEnergyValues_bddBelow (g : RiemannianMetric n M) (alpha : ℝ) :
    BddBelow (m60NonNullAlphaEnergyValues g alpha) := by
  refine ⟨0, ?_⟩
  rintro r ⟨f, _, _, rfl⟩
  exact m60SphereAlphaEnergy_nonneg g alpha f

end PoincareConjecture
