import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.AreaToEnergyMajorant
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.AreaToEnergyComparison










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Filter
open scoped Manifold ContDiff Topology

universe u

noncomputable section

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "T" => TangentSpace (𝓡 2) (M := UnitTwoSphere)

local instance c1ConversionTangentNormedAddCommGroup (p : UnitTwoSphere) :
    NormedAddCommGroup (T p) := inferInstanceAs (NormedAddCommGroup LoopPlane)

local instance c1ConversionTangentNormedSpace (p : UnitTwoSphere) :
    NormedSpace ℝ (T p) := inferInstanceAs (NormedSpace ℝ LoopPlane)

private theorem gram_eq_pullback (g : RiemannianMetric n M)
    (f : UnitTwoSphere → M) (hf : ContMDiff (𝓡 2) (𝓡 n) 1 f)
    (z : LoopPlane) (i j : Fin 2) :
    m60AreaGram g (f ∘ m60SphereParameter) z i j =
      M60.metricPullbackForm (n := 2) g f (m60SphereParameter z)
        (mfderiv (𝓡 2) (𝓡 2) m60SphereParameter z (EuclideanSpace.basisFun (Fin 2) ℝ i))
        (mfderiv (𝓡 2) (𝓡 2) m60SphereParameter z (EuclideanSpace.basisFun (Fin 2) ℝ j)) := by
  unfold m60AreaGram
  rw [mfderiv_comp z (hf.mdifferentiable (by simp) _)
    (m60SphereParameter_contMDiff.mdifferentiable (by simp) _)]
  rfl



theorem m60SphereMajorant_area_tendsto (g : RiemannianMetric n M)
    (f : UnitTwoSphere → M) (hf : ContMDiff (𝓡 2) (𝓡 n) 1 f)
    (q : ℕ → RiemannianMetric 2 UnitTwoSphere)
    (hbound : ∀ k (p : UnitTwoSphere) (v : T p),
      M60.metricPullbackForm (n := 2) g f p v v ≤ (q k).inner p v v ∧
      (q k).inner p v v ≤ M60.metricPullbackForm (n := 2) g f p v v +
        (2 * ((k : ℝ) + 1)⁻¹) * m60RoundSphereMetric.inner p v v) :
    Tendsto (fun k => m60SphereArea (q k) id) atTop (𝓝 (m60SphereArea g f)) := by
  have hd : Tendsto (fun k : ℕ => 2 * ((k : ℝ) + 1)⁻¹) atTop (𝓝 (0 : ℝ)) := by
    have hd₀ : Tendsto (fun k : ℕ => ((k : ℝ) + 1)⁻¹) atTop (𝓝 (0 : ℝ)) :=
      tendsto_inv_atTop_zero.comp
        (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
    simpa only [mul_zero] using hd₀.const_mul 2
  have hcoef (z : LoopPlane) (i j : Fin 2) :
      Tendsto (fun k => m60AreaGram (q k) m60SphereParameter z i j) atTop
        (𝓝 (m60AreaGram g (f ∘ m60SphereParameter) z i j)) := by
    rw [gram_eq_pullback g f hf z i j]
    exact M60.tendsto_bilinear_of_quadratic_bounds
      (E := T (m60SphereParameter z))
      (M60.metricPullbackForm (n := 2) g f (m60SphereParameter z))
      (m60RoundSphereMetric.inner (m60SphereParameter z))
      (fun k => (q k).inner (m60SphereParameter z))
      (fun v w => g.symm _ _ _) (fun k => (q k).symm _) hd
      (fun k => hbound k (m60SphereParameter z)) _ _
  have hpoint (z : LoopPlane) :
      Tendsto (fun k => m60SphereAreaDensity (q k) id z) atTop
        (𝓝 (m60SphereAreaDensity g f z)) := by
    have hdet := ((hcoef z 0 0).mul (hcoef z 1 1)).sub
      ((hcoef z 0 1).mul (hcoef z 1 0))
    simpa only [m60SphereAreaDensity, m60AreaDensity, Function.id_comp,
      Matrix.det_fin_two] using
      ((show Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0) from
        tendsto_const_nhds).max hdet).sqrt
  have hdom (k : ℕ) (z : LoopPlane) :
      m60SphereAreaDensity (q k) id z ≤
        m60SphereEnergyDensity g f z + 2 * (16 / (‖z‖ ^ 2 + 4) ^ 2) := by
    have hdiag (i : Fin 2) : m60AreaGram (q k) m60SphereParameter z i i ≤
        m60AreaGram g (f ∘ m60SphereParameter) z i i +
          (2 * ((k : ℝ) + 1)⁻¹) * (16 / (‖z‖ ^ 2 + 4) ^ 2) := by
      have h := (hbound k (m60SphereParameter z)
        (mfderiv (𝓡 2) (𝓡 2) m60SphereParameter z
          (EuclideanSpace.basisFun (Fin 2) ℝ i))).2
      rw [m60RoundSphereMetric_inner, m60SphereParameter_inner,
        real_inner_self_eq_norm_sq, (EuclideanSpace.basisFun (Fin 2) ℝ).norm_eq_one,
        one_pow, mul_one, ← gram_eq_pullback g f hf z i i] at h
      exact h
    have henergy : m60SphereEnergyDensity (q k) id z ≤
        m60SphereEnergyDensity g f z +
          (2 * ((k : ℝ) + 1)⁻¹) * (16 / (‖z‖ ^ 2 + 4) ^ 2) := by
      simp only [m60SphereEnergyDensity, Function.id_comp, m60EnergyDensity,
        Matrix.trace_fin_two]
      linarith [hdiag 0, hdiag 1]
    have hk : ((k : ℝ) + 1)⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ (by have h := Nat.cast_nonneg (α := ℝ) k; linarith)
    calc
      _ ≤ m60SphereEnergyDensity (q k) id z := m60AreaDensity_le_energyDensity _ _ _
      _ ≤ _ := henergy.trans (by
        apply add_le_add_right
        exact mul_le_mul_of_nonneg_right
          (by linarith : 2 * ((k : ℝ) + 1)⁻¹ ≤ 2) (by positivity))
  change Tendsto (fun k => ∫ z : LoopPlane, m60SphereAreaDensity (q k) id z) atTop
    (𝓝 (∫ z : LoopPlane, m60SphereAreaDensity g f z))
  refine tendsto_integral_of_dominated_convergence
    (fun z => m60SphereEnergyDensity g f z + 2 * (16 / (‖z‖ ^ 2 + 4) ^ 2)) ?_ ?_ ?_ ?_
  · intro k
    exact (m60SphereAreaDensity_integrable (q k) id contMDiff_id).aestronglyMeasurable
  · exact (m60SphereEnergyDensity_integrable g f hf).add
      (m60SphereParameter_factor_integrable.const_mul 2)
  · intro k
    filter_upwards [] with z
    rw [Real.norm_of_nonneg (show 0 ≤ m60SphereAreaDensity (q k) id z from
      m60AreaDensity_nonneg (q k) (id ∘ m60SphereParameter) z)]
    exact hdom k z
  · exact Filter.Eventually.of_forall hpoint



theorem m60Sphere_exists_metric_majorant_area_lt (g : RiemannianMetric n M)
    (f : UnitTwoSphere → M) (hf : ContMDiff (𝓡 2) (𝓡 n) 1 f)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ q : RiemannianMetric 2 UnitTwoSphere,
      (∀ (p : UnitTwoSphere) (v : T p),
        g.inner (f p) (mfderiv (𝓡 2) (𝓡 n) f p v) (mfderiv (𝓡 2) (𝓡 n) f p v) ≤
          q.inner p v v) ∧ m60SphereArea q id < m60SphereArea g f + eta := by
  choose q hq using fun k : ℕ => m60Sphere_exists_smooth_metric_majorant g f hf
    ((k : ℝ) + 1)⁻¹ (by positivity)
  have hbound (k : ℕ) (p : UnitTwoSphere) (v : T p) :
      M60.metricPullbackForm (n := 2) g f p v v ≤ (q k).inner p v v ∧
      (q k).inner p v v ≤ M60.metricPullbackForm (n := 2) g f p v v +
        (2 * ((k : ℝ) + 1)⁻¹) * m60RoundSphereMetric.inner p v v := by
    refine ⟨?_, (hq k p v).2⟩
    have hr : 0 ≤ m60RoundSphereMetric.inner p v v := by
      by_cases hv : v = 0
      · simp [hv]
      · exact (m60RoundSphereMetric.pos p v hv).le
    exact (le_add_of_nonneg_right (mul_nonneg (by positivity) hr)).trans (hq k p v).1
  have hevent := (m60SphereMajorant_area_tendsto g f hf q hbound).eventually
    (gt_mem_nhds (show m60SphereArea g f < m60SphereArea g f + eta by linarith))
  obtain ⟨k, hk⟩ := hevent.exists
  exact ⟨q k, fun p v => (hbound k p v).1, hk⟩




theorem m60SphereAreaToEnergy_of_uniformization
    (huniform : ∀ q : RiemannianMetric 2 UnitTwoSphere,
      ∃ phi : UnitTwoSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ UnitTwoSphere, M60WeaklyConformal q phi)
    (g : RiemannianMetric n M) (f : UnitTwoSphere → M)
    (hf : ContMDiff (𝓡 2) (𝓡 n) 1 f) (eta : ℝ) (heta : 0 < eta) :
    ∃ h : UnitTwoSphere → M, ContMDiff (𝓡 2) (𝓡 n) 1 h ∧
      m60SphereEnergy g h < m60SphereArea g f + eta ∧
      (IsNullHomotopicSphere h → IsNullHomotopicSphere f) := by
  obtain ⟨q, hbound, harea⟩ := m60Sphere_exists_metric_majorant_area_lt g f hf eta heta
  obtain ⟨phi, hphi⟩ := huniform q
  refine ⟨f ∘ phi, hf.comp (phi.contMDiff.of_le (by simp)), ?_, ?_⟩
  · calc
      _ ≤ m60SphereEnergy q phi := m60SphereEnergy_comp_le_of_differential_le g f hf q phi
        (phi.contMDiff.of_le (by simp)) hbound
      _ = m60SphereArea q phi :=
        (m60SphereArea_eq_energy_of_weaklyConformal q phi
          (phi.contMDiff.of_le (by simp)) hphi).symm
      _ = m60SphereArea q id := m60SphereMetric_area_diffeomorph_eq q phi
      _ < _ := harea
  · exact (m60IsNullHomotopicSphere_comp_homeomorph f phi.toHomeomorph).mp

end PoincareConjecture

end
