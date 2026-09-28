import PoincareConjecture.Proofs.M08.PathLengthReparameterization
import PoincareConjecture.Proofs.M08.PathEnergy
import Mathlib.Topology.MetricSpace.ProperSpace

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped Manifold ContDiff Bundle intervalIntegral ENNReal

universe u

namespace PoincareConjecture.M08

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [ConnectedSpace M] [T3Space M]

theorem exists_reference_lipschitz_path (g : RiemannianMetric n M) (x y : M)
    (R : ℝ) (hR : 0 ≤ R) :
    letI : MetricSpace M := referenceMetricSpace g
    dist x y ≤ R → ∃ β : Icc (0 : ℝ) 1 → M,
      β ⟨0, le_rfl, zero_le_one⟩ = x ∧ β ⟨1, zero_le_one, le_rfl⟩ = y ∧
      ∀ s t, dist (β s) (β t) ≤ (R + 2) * dist s t := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  letI : MetricSpace M := EMetricSpace.toMetricSpace (finiteEdistMetric g)
  intro hxy
  have hed : Manifold.riemannianEDist (𝓡 n) x y < ENNReal.ofReal (R + 1) := by
    change edist x y < ENNReal.ofReal (R + 1)
    rw [edist_dist, ENNReal.ofReal_lt_ofReal_iff (by linarith : 0 < R + 1)]
    linarith
  obtain ⟨α, hα0, hα1, hα, hlen, _, _⟩ :=
    Manifold.exists_lt_locally_constant_of_riemannianEDist_lt hed
      (zero_lt_one : (0 : ℝ) < 1)
  let v := fun r ↦ Real.sqrt (referenceSpeedSq g α r)
  have hv : Continuous v := Real.continuous_sqrt.comp
    (continuousOn_univ.mp (referenceSpeedSq_continuousOn g isOpen_univ hα.contMDiffOn))
  have hn (r : ℝ) : 0 ≤ v r := Real.sqrt_nonneg _
  have hlength (s t : ℝ) (hst : s ≤ t) :
      Manifold.pathELength (𝓡 n) α s t = ENNReal.ofReal (∫ r in s..t, v r) := by
    rw [Manifold.pathELength_eq_lintegral_mfderiv_Icc,
      intervalIntegral.integral_of_le hst, ← integral_Icc_eq_integral_Ioc,
      ofReal_integral_eq_lintegral_ofReal hv.continuousOn.integrableOn_Icc
        (ae_of_all _ hn)]
    apply lintegral_congr
    intro r
    rw [← ofReal_norm, norm_eq_sqrt_real_inner]
    rfl
  have hinc (s : ℝ) (_hs : s ∈ Icc 0 1) (t : ℝ) (_ht : t ∈ Icc 0 1) (hst : s ≤ t) :
      dist (α s) (α t) ≤ ∫ r in s..t, v r := by
    apply (edist_le_ofReal (intervalIntegral.integral_nonneg_of_forall hst hn)).mp
    change Manifold.riemannianEDist (𝓡 n) (α s) (α t) ≤ _
    rw [← hlength s t hst]
    exact Manifold.riemannianEDist_le_pathELength hα.contMDiffOn rfl rfl hst
  have hL : (∫ r in (0 : ℝ)..1, v r) < R + 1 := by
    rw [hlength 0 1 zero_le_one,
      ENNReal.ofReal_lt_ofReal_iff (by linarith : 0 < R + 1)] at hlen
    exact hlen
  obtain ⟨β, hβ0, hβ1, hβ⟩ := exists_lipschitz_length_reparameterization α v
    hv.continuousOn (fun r _ ↦ hn r) hinc
  refine ⟨β, hβ0.trans hα0, hβ1.trans hα1, ?_⟩
  intro s t
  exact (hβ s t).trans (mul_le_mul_of_nonneg_right (by linarith) dist_nonneg)

theorem referenceMetricSpace_proper (g : RiemannianMetric n M) (hg : MetricComplete g) :
    letI : MetricSpace M := referenceMetricSpace g
    ProperSpace M := by
  letI : MetricSpace M := referenceMetricSpace g
  letI : CompleteSpace M := referenceMetricSpace_complete g hg
  letI : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional (M := M) (𝓡 n)
  refine ⟨fun x R ↦ ?_⟩
  by_cases hR : 0 ≤ R
  · have hpaths (y : Metric.closedBall x R) : ∃ β : Icc (0 : ℝ) 1 → M,
        β ⟨0, le_rfl, zero_le_one⟩ = x ∧ β ⟨1, zero_le_one, le_rfl⟩ = y ∧
        ∀ s t, dist (β s) (β t) ≤ (R + 2) * dist s t :=
      exists_reference_lipschitz_path g x y R hR (by
        simpa only [Metric.mem_closedBall, dist_comm] using y.2)
    choose f hleft hright hbound using hpaths
    have hf : Equicontinuous f := by
      apply UniformEquicontinuous.equicontinuous
      apply Metric.uniformEquicontinuous_of_continuity_modulus (fun r ↦ (R + 2) * r)
        _ f (fun s t y ↦ hbound y s t)
      simpa only [mul_zero, id_eq] using (tendsto_const_nhds.mul (tendsto_id : Tendsto (fun r : ℝ ↦ r) (𝓝 0) (𝓝 0)))
    letI : PreconnectedSpace (Icc (0 : ℝ) 1) :=
      isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
    obtain ⟨K, hK, hKf⟩ := exists_compact_range_of_anchored f hf
      ⟨0, le_rfl, zero_le_one⟩ x hleft
    apply hK.of_isClosed_subset Metric.isClosed_closedBall
    intro y hy
    have h := hKf ⟨y, hy⟩ ⟨1, zero_le_one, le_rfl⟩
    rwa [hright] at h
  · rw [Metric.closedBall_of_neg (lt_of_not_ge hR)]
    exact isCompact_empty

theorem isCompact_closure_referenceBall (g : RiemannianMetric n M) (hg : MetricComplete g)
    (x : M) {r : ℝ} (hr : 0 < r) : IsCompact (closure (g.ball x r)) := by
  letI : MetricSpace M := referenceMetricSpace g
  letI : ProperSpace M := referenceMetricSpace_proper g hg
  apply (isCompact_closedBall x r).of_isClosed_subset isClosed_closure
  apply closure_minimal _ Metric.isClosed_closedBall
  intro y hy
  change g.edist x y < ENNReal.ofReal r at hy
  change edist x y < ENNReal.ofReal r at hy
  rw [edist_dist, ENNReal.ofReal_lt_ofReal_iff hr] at hy
  exact Metric.mem_closedBall.mpr (by simpa only [dist_comm] using hy.le)

end PoincareConjecture.M08
