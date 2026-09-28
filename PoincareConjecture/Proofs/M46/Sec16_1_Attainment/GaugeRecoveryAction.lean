import PoincareConjecture.Proofs.M46.Sec16_1_Attainment.GaugeRecovery
import PoincareConjecture.Proofs.M46.Sec16_1_Attainment.GaugeActionLimit










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology intervalIntegral

universe u

namespace PoincareConjecture.Proofs.M46

variable {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport 3 X time I}



noncomputable def gaugeCylinderAction (j : G.gaugeCover.index) {a b : ℝ}
    (theta : ℝ → (G.timeIntervals.interval (G.gaugeCover.interval j)).Point)
    (alpha : ℝ → G.gaugeCover.spatial j)
    (v : M08.ChartL2 (EuclideanSpace ℝ (Fin 3)) a b) : ℝ :=
  (∫ s in a..b, (1 / 2 : ℝ) *
    ((G.gaugeCover.metric j).metric (theta s).val).inner (alpha s) (v s) (v s)) +
  ∫ s in a..b, 2 * s ^ 2 * horizontalScalarCurvature G.leafwise
    ((G.gaugeCover.cylinder j).toSpacetime (theta s, alpha s))



theorem gaugeCylinderAction_eq (e : AttainmentGauge G) {a b : ℝ}
    (gamma : ℝ → G.Point) (hsrc : MapsTo gamma (Icc a b) e.source) (hab : a ≤ b)
    (w : M08.ChartL2 (EuclideanSpace ℝ (Fin 3)) a b) :
    gaugeCylinderAction e.index (fun s => (e.lift (gamma s)).1)
      (fun s => (e.lift (gamma s)).2) w = gaugePieceAction e gamma w := by
  unfold gaugeCylinderAction gaugePieceAction
  congr 1
  · apply intervalIntegral.integral_congr
    intro s _
    exact congrArg (fun z : ℝ => (1 / 2 : ℝ) * z)
      (gaugeLiftMetric_apply e.index e.lift e.center (gamma s) (w s) (w s)).symm
  · apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hab] at hs
    change 2 * s ^ 2 * horizontalScalarCurvature G.leafwise
      ((G.gaugeCover.cylinder e.index).toSpacetime (e.lift (gamma s))) = _
    rw [e.right_inv (gamma s) (hsrc hs)]

set_option synthInstance.maxHeartbeats 200000 in




theorem gauge_cylinder_action_tendsto (hM12 : GeneralizedRicciGaugeTheory.{u} 3)
    (j : G.gaugeCover.index) (x0 : G.gaugeCover.spatial j) {a b : ℝ} (hab : a ≤ b)
    (theta : ℝ → (G.timeIntervals.interval (G.gaugeCover.interval j)).Point)
    (htheta : ContinuousOn theta (Icc a b))
    {K : Set (G.gaugeCover.spatial j)} (hK : IsCompact K)
    (alpha : ℕ → ℝ → G.gaugeCover.spatial j) (gamma : ℝ → G.gaugeCover.spatial j)
    (halpha : ∀ k, ContinuousOn (alpha k) (Icc a b))
    (hgamma : ContinuousOn gamma (Icc a b))
    (halphaK : ∀ k, MapsTo (alpha k) (Icc a b) K) (hgammaK : MapsTo gamma (Icc a b) K)
    (hlim : TendstoUniformlyOn alpha gamma atTop (Icc a b))
    (v : ℕ → M08.ChartL2 (EuclideanSpace ℝ (Fin 3)) a b)
    (w : M08.ChartL2 (EuclideanSpace ℝ (Fin 3)) a b) (hv : Tendsto v atTop (𝓝 w)) :
    Tendsto (fun k => gaugeCylinderAction j theta (alpha k) (v k)) atTop
      (𝓝 (gaugeCylinderAction j theta gamma w)) := by
  let A : ℝ × G.gaugeCover.spatial j →
      EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ := fun z =>
    (1 / 2 : ℝ) • Proofs.M11.ordinaryChartMetric (G.gaugeCover.metric j).metric x0
      ((theta z.1).val, z.2.val)
  have hA : ContinuousOn A (Icc a b ×ˢ K) := by
    apply (continuousOn_const : ContinuousOn
      (fun _ : ℝ × G.gaugeCover.spatial j => (1 / 2 : ℝ)) (Icc a b ×ˢ K)).smul
    apply (Proofs.M11.ordinaryChartMetric_smooth (G.gaugeCover.metric j).metric
      (G.gaugeCover.interval j).domain (G.gaugeCover.metric j).smooth x0).continuousOn.comp
    · exact (continuous_subtype_val.comp_continuousOn
        (htheta.comp continuousOn_fst (fun _ hz => hz.1))).prodMk
        (continuous_subtype_val.comp_continuousOn continuousOn_snd)
    · intro z _
      refine ⟨(theta z.1).property, ?_⟩
      change z.2.val ∈ (chartAt (EuclideanSpace ℝ (Fin 3)) x0).target
      rw [(G.gaugeCover.spatial j).chartAt_target_eq]
      exact z.2.property
  let B k s := A (s, alpha k s)
  let D s := A (s, gamma s)
  have hB (k : ℕ) : MemLp (B k) (⊤ : ENNReal) (volume.restrict (Icc a b)) :=
    M08.continuousOn_memLp_top_Icc (f := B k) (a := a) (b := b)
      (hA.comp (continuousOn_id.prodMk (halpha k)) (fun _ hs => ⟨hs, halphaK k hs⟩))
  have hD : MemLp D (⊤ : ENNReal) (volume.restrict (Icc a b)) :=
    M08.continuousOn_memLp_top_Icc (f := D) (a := a) (b := b)
      (hA.comp (continuousOn_id.prodMk hgamma) (fun _ hs => ⟨hs, hgammaK hs⟩))
  let Qk k := M08.integratedFormMap _ ((hB k).toLp (B k))
  let Q := M08.integratedFormMap _ (hD.toLp D)
  have hQ : Tendsto Qk atTop (𝓝 Q) := by
    apply (tendsto_iff_norm_sub_tendsto_zero (f := Qk) (b := Q)).mpr
    apply M08.integratedForm_tendsto_of_uniform B D hB hD
    exact M08.uniform_composition_on_compact_core hK A hA alpha gamma
      (Eventually.of_forall halphaK) hgammaK hlim
  have hQeq (z : M08.ChartL2 (EuclideanSpace ℝ (Fin 3)) a b) :
      Q z z = ∫ s in a..b, D s (z s) (z s) := by
    rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc,
      M08.integratedFormMap_apply]
    apply integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp
      (E := EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ)
      hD] with s hs
    rw [hs]
  have hQkeq (k : ℕ) : Qk k (v k) (v k) = ∫ s in a..b, B k s (v k s) (v k s) := by
    rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc,
      M08.integratedFormMap_apply]
    apply integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp
      (E := EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ)
      (hB k)] with s hs
    rw [hs]
  have hkin := M08.quadratic_form_tendsto Qk Q v w hQ hv
  let V : ℝ × G.gaugeCover.spatial j → ℝ := fun z =>
    2 * z.1 ^ 2 * horizontalScalarCurvature G.leafwise
      ((G.gaugeCover.cylinder j).toSpacetime (theta z.1, z.2))
  have H := (hM12.leafwise_calculus X time I G.spacetime G.slices
    G.timeIntervals G.gaugeCover).2 G.leafwise
  have hscalar := H.scalar_smooth.continuous.comp
    (G.gaugeCover.cylinder j).smooth.continuous
  have hV : ContinuousOn V (Icc a b ×ˢ K) :=
    (continuousOn_const.mul (continuousOn_fst.pow 2)).mul
      (hscalar.comp_continuousOn
        ((htheta.comp continuousOn_fst (fun _ hz => hz.1)).prodMk
          continuousOn_snd))
  have hpot : Tendsto (fun k => ∫ s in a..b, V (s, alpha k s)) atTop
      (𝓝 (∫ s in a..b, V (s, gamma s))) := by
    apply TendstoUniformlyOn.tendsto_intervalIntegral_of_continuousOn
    · apply Eventually.of_forall
      intro k
      rw [uIcc_of_le hab]
      exact hV.comp (continuousOn_id.prodMk (halpha k)) (fun _ hs => ⟨hs, halphaK k hs⟩)
    · rw [uIcc_of_le hab]
      exact M08.uniform_composition_on_compact_core hK V hV alpha gamma
        (Eventually.of_forall halphaK) hgammaK hlim
  simpa only [hQeq, hQkeq, B, D, A, V, gaugeCylinderAction,
    smul_apply, smul_eq_mul, M14.ordinaryChartMetric_openSubset_apply]
    using hkin.add hpot

end PoincareConjecture.Proofs.M46
