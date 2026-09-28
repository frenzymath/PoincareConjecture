import PoincareConjecture.Proofs.M60.Mathlib.LipschitzDerivative
import PoincareConjecture.Proofs.M60.Def18_17_FillingArea.AreaMeasurability
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.AreaEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped Manifold ContDiff Topology Bundle NNReal ENNReal

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M] [T2Space M]

theorem m60AreaDensity_le_of_metric_lipschitzOn (g : RiemannianMetric n M)
    {f : LoopPlane → M} {S : Set LoopPlane} (hS : IsOpen S)
    {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ x ∈ S, ∀ y ∈ S,
      g.edist (f x) (f y) ≤ ENNReal.ofReal L * ENNReal.ofReal ‖x - y‖)
    {z : LoopPlane} (hz : z ∈ S) : m60AreaDensity g f z ≤ (2 * L) ^ 2 := by
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  let : IsRiemannianManifold (𝓡 n) M := ⟨fun _ _ => rfl⟩
  have hLip : LipschitzOnWith (NNReal.mk L hL) f S := by
    intro x hx y hy
    change g.edist (f x) (f y) ≤ _
    simpa only [edist_dist, dist_eq_norm, ENNReal.ofReal_eq_coe_nnreal hL] using hf x hx y hy
  have hcol (i : Fin 2) : m60AreaGram g f z i i ≤ (2 * L) ^ 2 := by
    have hb := M60.norm_mfderiv_apply_le_of_lipschitzOn
      (F := EuclideanSpace ℝ (Fin n)) hS hLip hz
      (EuclideanSpace.basisFun (Fin 2) ℝ i)
    rw [(EuclideanSpace.basisFun (Fin 2) ℝ).norm_eq_one, mul_one] at hb
    change inner ℝ (mfderiv (𝓡 2) (𝓡 n) f z (EuclideanSpace.basisFun (Fin 2) ℝ i))
      (mfderiv (𝓡 2) (𝓡 n) f z (EuclideanSpace.basisFun (Fin 2) ℝ i)) ≤ _
    rw [real_inner_self_eq_norm_sq]
    exact pow_le_pow_left₀ (norm_nonneg _) hb 2
  apply (m60AreaDensity_le_energyDensity g f z).trans
  unfold m60EnergyDensity
  rw [Matrix.trace_fin_two]
  linarith [hcol 0, hcol 1]

theorem m60AreaIntegral_bound_of_metric_lipschitzOn (g : RiemannianMetric n M)
    {f : LoopPlane → M} {S : Set LoopPlane} (hS : IsOpen S)
    (hfinite : volume S ≠ ⊤) {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ x ∈ S, ∀ y ∈ S,
      g.edist (f x) (f y) ≤ ENNReal.ofReal L * ENNReal.ofReal ‖x - y‖) :
    IntegrableOn (m60AreaDensity g f) S volume ∧
      (∫ z in S, m60AreaDensity g f z) ≤ (2 * L) ^ 2 * volume.real S := by
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  have hLip : LipschitzOnWith (NNReal.mk L hL) f S := by
    intro x hx y hy
    change g.edist (f x) (f y) ≤ _
    simpa only [edist_dist, dist_eq_norm, ENNReal.ofReal_eq_coe_nnreal hL] using hf x hx y hy
  have hm := m60AreaDensity_aestronglyMeasurableOn g hS hLip.continuousOn
  have hbound : ∀ᵐ z ∂volume.restrict S, m60AreaDensity g f z ≤ (2 * L) ^ 2 := by
    filter_upwards [ae_restrict_mem hS.measurableSet] with z hz
    exact m60AreaDensity_le_of_metric_lipschitzOn g hS hL hf hz
  have hc : IntegrableOn (fun _ : LoopPlane => (2 * L) ^ 2) S volume :=
    integrableOn_const hfinite
  have hint : IntegrableOn (m60AreaDensity g f) S volume := hc.mono' hm (by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (m60AreaDensity_nonneg g f _)] using hbound)
  refine ⟨hint, ?_⟩
  calc
    (∫ z in S, m60AreaDensity g f z) ≤ ∫ _ : LoopPlane in S, (2 * L) ^ 2 :=
      integral_mono_ae hint hc hbound
    _ = (2 * L) ^ 2 * volume.real S := by simp [mul_comm]

end PoincareConjecture
