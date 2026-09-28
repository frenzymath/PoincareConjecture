import PoincareConjecture.Proofs.M47.CanonicalMetricFamilyPullback
import Mathlib.Topology.Order.Compact

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M47

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {J : Set ℝ} {epsilon : ℝ}

theorem continuousOn_round_metricJetError (F : RicciFlow 3 M J) (t : J)
    (N : SingularRoundComponent (F.metric t.val) epsilon) :
    ContinuousOn (fun p : ℝ × N.model.carrier ↦
      singularMetricJetErrorSquared N.model_metric N.model_connection
        (fun y v ↦ N.scale * singularMetricPullback (F.metric p.1) N.forward y v)
        ⌊epsilon⁻¹⌋₊ p.2) (J ×ˢ univ) := by
  let T : ℝ → CovariantTensorEvaluation 3 N.model.carrier 2 := fun s y v ↦
    N.scale * singularMetricPullback (F.metric s) N.forward y v -
      N.model_metric.inner y (v 0) (v 1)
  have hT (s : ℝ) : IsSmoothCovariantTensor (T s) :=
    ((M44.isSmoothCovariantTensor_metric_pullback (F.metric s) N.forward_smooth).const_mul
      N.scale).sub (M44.isSmoothCovariantTensor_metric N.model_metric)
  have hTime (U : Set N.model.carrier) (hU : IsOpen U)
      (Y : Fin 2 → (y : N.model.carrier) → TangentSpace (𝓡 3) y)
      (hY : ∀ i, ContMDiffOn (𝓡 3) ((𝓡 3).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))
        ∞ (T% (Y i)) U) :
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × N.model.carrier ↦ T p.1 p.2 (fun i ↦ Y i p.2)) (J ×ˢ U) := by
    have hflow := (contMDiffOn_const (c := N.scale)).mul
      (contMDiffOn_flow_metricPullback_onFields F N.forward_smooth hU Y hY)
    have hmodel : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × N.model.carrier ↦ N.model_metric.inner p.2 (Y 0 p.2) (Y 1 p.2))
        (J ×ˢ U) :=
      ((M44.isSmoothCovariantTensor_metric N.model_metric).2 U hU Y hY).comp
        contMDiffOn_snd (fun _ hp ↦ hp.2)
    exact hflow.sub hmodel
  exact continuousOn_fixed_tensorJetEnergy N.model_metric N.model_connection T hT hTime
    ⌊epsilon⁻¹⌋₊

theorem eventually_same_round_component (F : RicciFlow 3 M J) (t : J)
    (N : SingularRoundComponent (F.metric t.val) epsilon) :
    ∀ᶠ s : J in 𝓝 t, ∃ P : SingularRoundComponent (F.metric s.val) epsilon,
      P.carrier = N.carrier ∧ P.basepoint = N.basepoint ∧
        P.model = N.model ∧ P.scale = N.scale := by
  let error : J × N.model.carrier → ℝ := fun p ↦
    singularMetricJetErrorSquared N.model_metric N.model_connection
      (fun y v ↦ N.scale * singularMetricPullback (F.metric p.1.val) N.forward y v)
      ⌊epsilon⁻¹⌋₊ p.2
  have herror : Continuous error := by
    have hmap : Continuous (fun p : J × N.model.carrier ↦ (p.1.val, p.2)) :=
      (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
    have h := (continuousOn_round_metricJetError F t N).comp_continuous hmap
      (fun p ↦ ⟨p.1.property, mem_univ p.2⟩)
    exact h
  obtain ⟨b, hb, hbound⟩ := N.metric_comparison
  let b' := (b + epsilon ^ 2) / 2
  have hbb' : b < b' := by dsimp only [b']; linarith
  have hb' : b' < epsilon ^ 2 := by dsimp only [b']; linarith
  have hnear : ∀ᶠ s : J in 𝓝 t, ∀ x ∈ (univ : Set N.model.carrier), error (s, x) < b' := by
    apply N.model_compact.eventually_forall_of_forall_eventually
    intro x _
    have hold : error (t, x) ≤ b := hbound x
    exact (herror.continuousAt (x := (t, x))).eventually
      (Iio_mem_nhds (hold.trans_lt hbb'))
  filter_upwards [hnear] with s hs
  refine ⟨{
    epsilon_pos := N.epsilon_pos
    basepoint := N.basepoint
    carrier := N.carrier
    component_eq := N.component_eq
    compact := N.compact
    model := N.model
    model_compact := N.model_compact
    model_connected := N.model_connected
    model_metric := N.model_metric
    model_connection := N.model_connection
    model_curvature_one := N.model_curvature_one
    forward := N.forward
    inverse := N.inverse
    forward_image := N.forward_image
    forward_openEmbedding := N.forward_openEmbedding
    forward_smooth := N.forward_smooth
    inverse_smooth := N.inverse_smooth
    left_inverse := N.left_inverse
    right_inverse := N.right_inverse
    scale := N.scale
    scale_pos := N.scale_pos
    metric_comparison := ⟨b', hb', fun x ↦ (hs x (mem_univ x)).le⟩
  }, rfl, rfl, rfl, rfl⟩

end PoincareConjecture.Proofs.M47
