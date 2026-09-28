import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.SphereTangent
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.StereographicConformal
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Topology.Instances.Matrix

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Bundle
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem m60AreaGram_continuous (g : RiemannianMetric n M)
    {F : LoopPlane → M} (hF : ContMDiff (𝓡 2) (𝓡 n) 1 F) :
    Continuous (m60AreaGram g F) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  have hcolumn (i : Fin 2) : Continuous (fun z : LoopPlane =>
      (⟨F z, mfderiv (𝓡 2) (𝓡 n) F z (EuclideanSpace.basisFun (Fin 2) ℝ i)⟩ :
        TangentBundle (𝓡 n) M)) :=
    (hF.continuous_tangentMap le_rfl).comp
      ((tangentBundleModelSpaceHomeomorph (𝓡 2)).symm.continuous.comp
        (continuous_id.prodMk continuous_const))
  exact continuous_pi fun i => continuous_pi fun j =>
    (hcolumn i).inner_bundle (hcolumn j)

theorem m60AreaDensity_continuous (g : RiemannianMetric n M)
    {F : LoopPlane → M} (hF : ContMDiff (𝓡 2) (𝓡 n) 1 F) :
    Continuous (m60AreaDensity g F) :=
  (continuous_const.max (m60AreaGram_continuous g hF).matrix_det).sqrt

theorem m60EnergyDensity_continuous (g : RiemannianMetric n M)
    {F : LoopPlane → M} (hF : ContMDiff (𝓡 2) (𝓡 n) 1 F) :
    Continuous (m60EnergyDensity g F) := by
  unfold m60EnergyDensity
  simp only [Matrix.trace_fin_two]
  have hG := m60AreaGram_continuous g hF
  have hentry (i j : Fin 2) : Continuous (fun z => m60AreaGram g F z i j) :=
    (continuous_apply j).comp ((continuous_apply i).comp hG)
  exact continuous_const.mul ((hentry 0 0).add (hentry 1 1))

theorem m60SphereEnergyDensity_bound (g : RiemannianMetric n M)
    (f : UnitTwoSphere → M) (hf : ContMDiff (𝓡 2) (𝓡 n) 1 f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : LoopPlane,
      m60SphereEnergyDensity g f z ≤ C * (16 / (‖z‖ ^ 2 + 4) ^ 2) := by
  obtain ⟨C, hC, hbound⟩ := m60SphereDifferential_bound g f hf
  refine ⟨C, hC, ?_⟩
  intro z
  have hcolumn (i : Fin 2) : m60AreaGram g (f ∘ m60SphereParameter) z i i ≤
      C * (16 / (‖z‖ ^ 2 + 4) ^ 2) := by
    have h := hbound (m60SphereParameter z)
      (mfderiv (𝓡 2) (𝓡 2) m60SphereParameter z (EuclideanSpace.basisFun (Fin 2) ℝ i))
    rw [m60SphereParameter_inner] at h
    simp only [real_inner_self_eq_norm_sq, (EuclideanSpace.basisFun (Fin 2) ℝ).norm_eq_one,
      one_pow, mul_one] at h
    unfold m60AreaGram
    rw [mfderiv_comp z (hf.mdifferentiable (by simp) _)
      (m60SphereParameter_contMDiff.mdifferentiable (by simp) _)]
    exact h
  unfold m60SphereEnergyDensity m60EnergyDensity
  rw [Matrix.trace_fin_two]
  linarith [hcolumn 0, hcolumn 1]

theorem m60SphereParameter_factor_integrable :
    Integrable (fun z : LoopPlane => 16 / (‖z‖ ^ 2 + 4) ^ 2) volume := by
  have hbase : Integrable (fun z : LoopPlane => ((1 : ℝ) + ‖z‖ ^ 2)⁻¹ ^ 2) volume := by
    have h := integrable_rpow_neg_one_add_norm_sq (E := LoopPlane) (μ := volume)
      (r := 4) (by norm_num [LoopPlane])
    convert h using 1
    funext z
    norm_num [Real.rpow_neg, Real.rpow_natCast, inv_pow]
  refine (hbase.const_mul 16).mono' ?_ (Filter.Eventually.of_forall fun z => ?_)
  · have hc : Continuous (fun z : LoopPlane => 16 / (‖z‖ ^ 2 + 4) ^ 2) := by
      exact continuous_const.div₀ (((continuous_norm.pow 2).add continuous_const).pow 2)
        (fun _ => ne_of_gt (by positivity))
    exact hc.aestronglyMeasurable
  · rw [Real.norm_of_nonneg (by positivity), div_eq_mul_inv, inv_pow]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    have hinv : (‖z‖ ^ 2 + 4)⁻¹ ≤ (1 + ‖z‖ ^ 2)⁻¹ :=
      inv_anti₀ (by positivity) (by linarith)
    simpa only [inv_pow] using pow_le_pow_left₀ (by positivity) hinv 2

theorem m60SphereEnergyDensity_integrable (g : RiemannianMetric n M)
    (f : UnitTwoSphere → M) (hf : ContMDiff (𝓡 2) (𝓡 n) 1 f) :
    Integrable (m60SphereEnergyDensity g f) volume := by
  obtain ⟨C, -, hbound⟩ := m60SphereEnergyDensity_bound g f hf
  have hF := hf.comp (m60SphereParameter_contMDiff.of_le (by simp))
  apply (m60SphereParameter_factor_integrable.const_mul C).mono'
    (m60EnergyDensity_continuous g hF).aestronglyMeasurable
  filter_upwards [] with z
  rw [Real.norm_of_nonneg (m60EnergyDensity_nonneg g (f ∘ m60SphereParameter) z)]
  exact hbound z

theorem m60SphereAreaDensity_integrable (g : RiemannianMetric n M)
    (f : UnitTwoSphere → M) (hf : ContMDiff (𝓡 2) (𝓡 n) 1 f) :
    Integrable (m60SphereAreaDensity g f) volume := by
  have hF := hf.comp (m60SphereParameter_contMDiff.of_le (by simp))
  apply (m60SphereEnergyDensity_integrable g f hf).mono'
    (m60AreaDensity_continuous g hF).aestronglyMeasurable
  filter_upwards [] with z
  rw [Real.norm_of_nonneg (m60AreaDensity_nonneg g (f ∘ m60SphereParameter) z)]
  exact m60AreaDensity_le_energyDensity g (f ∘ m60SphereParameter) z

end PoincareConjecture
