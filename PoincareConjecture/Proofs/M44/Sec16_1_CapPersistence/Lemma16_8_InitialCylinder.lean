import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma16_8_StoppedCylinder
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma16_8_InitialScalarBound
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma16_8_InitialChartBounds
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma16_8_InitialTwoJet
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma16_8_OpenMetricBuffer
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_CylinderBirthMetric
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_NormalizedBirthBalls
import PoincareConjecture.Proofs.M44.Mathlib.RestrictChart

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.M44

open SpacetimeBounds

local notation "E" => StandardCapSpace

noncomputable local instance initialCylinderCoefficientNorm :
    NormedAddCommGroup (MetricCoefficient 3) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance initialCylinderCoefficientSpace :
    NormedSpace ℝ (MetricCoefficient 3) := ContinuousLinearMap.toNormedSpace

noncomputable local instance initialCylinderTwoJetNorm :
    NormedAddCommGroup (MetricTwoJet 3) := Prod.normedAddCommGroup

noncomputable local instance initialCylinderTwoJetSpace :
    NormedSpace ℝ (MetricTwoJet 3) := Prod.normedSpace

theorem exists_initial_cylinder_bound (P : M44CapPersistencePredecessors.{u})
    (g0 : StandardInitialMetric) (estimate : StandardCapEstimate g0)
    (C : ℝ) (x u v : E)
    (hcollar : metricTwoJet g0.metric.euclideanCoefficients x ∈ collarJetRegion C u v)
    {R0 : ℝ} (hR0 : 2 < R0) (hx : x ∈ g0.metric.ball 0 (R0 - 2)) :
    ∃ delta tau M : ℝ, 0 < delta ∧ 0 < tau ∧ 1 ≤ M ∧
      ∀ (F : SurgeryFlowData.{u}), F.standard_initial = g0 →
      ∀ (a : ℝ) (ha : a ∈ F.surgery_times) [Nonempty (F.slice a).carrier],
      ∀ (i : Fin (F.event a ha).cap_count) {R eta B q : ℝ}, R0 ≤ R → R < eta⁻¹ →
      0 < B → F.parameters.h a ^ 2 ≤ 1 → F.parameters.h a ^ 2 * q ≤ 1 →
      ∀ Q : SurgeryCapClose F.standard_initial
        ((F.event a ha).local_result i).output ((F.event a ha).local_result i).metric
        ((F.event a ha).local_result i).tip (((F.event a ha).necks i).neck.scale) eta,
      eta ≤ delta →
      (∀ r : ℝ, 0 < r → r ≤ eta⁻¹ → Q.map '' F.standard_initial.metric.ball 0 r =
        ((F.event a ha).local_result i).metric.ball ((F.event a ha).local_result i).tip
          (((F.event a ha).necks i).neck.scale * r)) →
      ∀ e : SurgeryFlowCylinder F (F.slice a) a ((F.parameters.h a)⁻¹ ^ 2) (Ico 0 B)
        ((F.metric a).ball ((F.event a ha).caps i).tip (F.parameters.h a * R)),
      (∀ h y, y ∈ (F.metric a).ball ((F.event a ha).caps i).tip (F.parameters.h a * R) →
        HEq (e.forward 0 h y) y) →
      (∀ s (_hs : s ∈ Ico (0 : ℝ) B),
        ∀ y : (F.slice (a + s / ((F.parameters.h a)⁻¹ ^ 2))).carrier,
        q ≤ (F.connection (a + s / ((F.parameters.h a)⁻¹ ^ 2))).scalarCurvature y →
        SurgeryCanonicalControl F (a + s / ((F.parameters.h a)⁻¹ ^ 2)) y
          F.parameters.epsilon C) → SurgeryFlowPinched F →
      ∃ f : PartialDiffeomorph (𝓡 3) (𝓡 3) E (F.slice a).carrier ∞,
        f.source = F.standard_initial.metric.ball 0 R ∧
        f.target = (F.metric a).ball ((F.event a ha).caps i).tip (F.parameters.h a * R) ∧
        (∀ y, f y = (F.event a ha).local_embed i (Q.map y)) ∧
        ∃ G : CylinderRicciFlow e f,
        ∃ p : (⟨f.target, f.open_target⟩ : Opens (F.slice a).carrier),
        ∀ T : ℝ, 0 < T → T < B → T ≤ tau →
          (∀ s ∈ Icc (0 : ℝ) T,
            metricTwoJet ((G.flow.metric s).pullbackCoefficients (targetChart f p)) x ∈
              collarJetRegion C u v) ∧
          (∀ s ∈ Icc (0 : ℝ) T, ∀ y,
            (G.flow.connection s).scalarCurvature y ≤ 2 * M ∧
            (G.flow.connection s).curvatureTensorNorm y ≤ 13 * max (2 * M) (Real.exp 4)) := by
  let K := {y : E | g0.metric.edist 0 y ≤ ENNReal.ofReal R0}
  have hK : IsCompact K := M36.standard_closed_ball_compact g0 (by linarith)
  obtain ⟨dB, alpha, Z, K0, hdB, halpha, hZ, hK0, hbounds⟩ :=
    exists_initial_chart_bounds.{u, u} g0 hK 2
  obtain ⟨M, hM, hscalar⟩ := exists_global_initial_chart_scalar_bound.{u, u} estimate
  let J := metricTwoJet g0.metric.euclideanCoefficients x
  obtain ⟨dJ, tau, hdJ, htau, hstop⟩ :=
    exists_stopped_cylinder_bound P C u v (model := {J}) isCompact_singleton
      (by intro z hz; obtain rfl : z = J := hz; exact hcollar)
      (zero_lt_one.trans_le hM) (zero_lt_one.trans_le hK0)
      (H := 1) (r := 1) zero_lt_one zero_lt_one halpha (zero_le_one.trans hZ) hZ
  obtain ⟨d2, hd2, hnear⟩ := exists_initial_twoJet_cutoff.{u} g0 hK hdJ
  refine ⟨min dB (min d2 (1 / 4)), min 1 tau, M,
    lt_min hdB (lt_min hd2 (by norm_num)), lt_min zero_lt_one htau, hM, ?_⟩
  intro F hg0 a ha _ i R eta B q hR hReta hB hsmall hq Q heta hballs e hinitial
    hcanonical hpinch
  subst g0
  have hRpos : 0 < R := by linarith
  have hh := F.parameters.h_pos a (F.time_domain_nonnegative (F.surgery_times_subset ha))
  have hscale : 0 < (F.parameters.h a)⁻¹ ^ 2 := sq_pos_of_pos (inv_pos.mpr hh)
  let g := m01RescaledMetric (F.metric a) ((F.parameters.h a)⁻¹ ^ 2) hscale
  have hg (y) (w z) : g.inner y w z = (F.parameters.h a)⁻¹ ^ 2 *
      (F.metric a).inner y w z := rfl
  obtain ⟨f, hfsource, hfmap, hftarget, hfconnected⟩ :=
    exists_physical_birth_chart F a ha i hRpos hReta Q (hballs R hRpos hReta.le)
  have hU : IsOpen ((F.metric a).ball ((F.event a ha).caps i).tip (F.parameters.h a * R)) :=
    hftarget ▸ f.open_target
  have hfU : f.target ⊆ (F.metric a).ball ((F.event a ha).caps i).tip
      (F.parameters.h a * R) := le_of_eq hftarget
  obtain ⟨G⟩ := exists_cylinderRicciFlow P hpinch e hU hB f hfU
  let W := F.standard_initial.metric.ball 0 R0
  let V := F.standard_initial.metric.ball 0 (R0 - 2)
  have hW : IsOpen W := by
    dsimp [W]
    rw [M36.standard_ball_eq_euclidean F.standard_initial (by linarith : 0 < R0)]
    exact Metric.isOpen_ball
  have hV : IsOpen V := by
    dsimp [V]
    rw [M36.standard_ball_eq_euclidean F.standard_initial (by linarith : 0 < R0 - 2)]
    exact Metric.isOpen_ball
  have hVW : V ⊆ W := fun _ hy => hy.trans_le (ENNReal.ofReal_le_ofReal (by linarith))
  have hWf : W ⊆ f.source := by
    rw [hfsource]
    exact fun _ hy => hy.trans_le (ENNReal.ofReal_le_ofReal hR)
  let p : (⟨f.target, f.open_target⟩ : Opens (F.slice a).carrier) :=
    ⟨f x, f.map_source (hWf (hVW hx))⟩
  let c := restrictChart (targetPartialDiffeomorph f p) hW hWf
  have hfQ : f.source ⊆ F.standard_initial.metric.ball 0 eta⁻¹ := by
    rw [hfsource]
    exact fun _ hy => hy.trans_le (ENNReal.ofReal_le_ofReal hReta.le)
  have hlink : EqOn ((G.flow.metric 0).pullbackCoefficients (targetChart f p))
      Q.normalizedCoefficients f.source := by
    intro y hy
    exact (G.initial_pullback_eq ⟨le_rfl, hB⟩ hfU hinitial g hg p hy).trans
      (physical_birth_pullback_eq F a ha i Q g hg f.open_source hfQ
        (fun z _ => hfmap z) hy)
  let N : GeneralizedSliceCarrier.{u} :=
    ⟨(⟨f.target, f.open_target⟩ : Opens (F.slice a).carrier), inferInstance,
      inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, inferInstance⟩
  have hWK : W ⊆ K := by
    intro y hy
    change F.standard_initial.metric.edist 0 y ≤ ENNReal.ofReal R0
    exact hy.le
  obtain ⟨hjets, hcurv, _⟩ := hbounds _ _ _ _ _ Q (heta.trans (min_le_left _ _))
    N (G.flow.metric 0) (G.flow.connection 0) c hWK (fun y hy => hlink (hWf hy))
  have hscalar0 (y : (⟨f.target, f.open_target⟩ : Opens (F.slice a).carrier)) :
      (G.flow.connection 0).scalarCurvature y ≤ M :=
    hscalar _ _ _ _ _ Q (heta.trans ((min_le_right _ _).trans (min_le_right _ _)))
      (G.flow.metric 0) (G.flow.connection 0) (targetPartialDiffeomorph f p)
      hfQ hlink y (mem_univ y)
  have himage (r : ℝ) (hr : 0 < r) (hrR : r ≤ R) :
      f '' F.standard_initial.metric.ball 0 r = g.ball ((F.event a ha).caps i).tip r :=
    physical_birth_chart_image_ball F a ha i hr (hrR.trans_lt hReta) Q
      (hballs r hr (hrR.trans hReta.le)) g hg f (fun y _ => hfmap y)
  have hcTarget : c.target = Subtype.val ⁻¹' (f '' W) :=
    targetChart_image_eq_preimage f p hWf
  have hmetric (y : (⟨f.target, f.open_target⟩ : Opens (F.slice a).carrier)) (w) :
      g.inner y.1 (mfderiv (𝓡 3) (𝓡 3) Subtype.val y w)
        (mfderiv (𝓡 3) (𝓡 3) Subtype.val y w) ≤ (G.flow.metric 0).inner y w w := by
    rw [G.initial_metric_link ⟨le_rfl, hB⟩ hfU hinitial, hg]
  have hbuffer (y : E) (hy : y ∈ V) :
      IsCompact (closure ((G.flow.metric 0).ball (c y) 1)) ∧
        closure ((G.flow.metric 0).ball (c y) 1) ⊆ c.target := by
    have hval : (c y).1 = f y := targetChart_val f p (hWf (hVW hy))
    have hinner : f y ∈ g.ball ((F.event a ha).caps i).tip (R0 - 2) := by
      rw [← himage (R0 - 2) (by linarith) (by linarith)]
      exact mem_image_of_mem f hy
    have hinside : closure (g.ball (c y).1 1) ⊆ f '' W := by
      rw [hval, himage R0 (by linarith) hR]
      exact g.closure_ball_subset_ball_of_margin (by linarith) zero_le_one (by linarith) hinner
    have hcompact : IsCompact (closure (g.ball (c y).1 1)) :=
      (F.slices_compact a (F.surgery_times_subset ha)).of_isClosed_subset
        isClosed_closure (subset_univ _)
    refine ⟨isCompact_closure_ball_of_open_metric _ g (G.flow.metric 0) hmetric (c y) 1
      hcompact (hinside.trans (by rintro _ ⟨z, hz, rfl⟩; exact f.map_source (hWf hz))), ?_⟩
    rw [hcTarget]
    exact (closure_ball_subset_preimage_of_open_metric _ g (G.flow.metric 0) hmetric
      (c y) 1).trans (preimage_mono hinside)
  have hcoeff : (G.flow.metric 0).pullbackCoefficients (targetChart f p) =ᶠ[𝓝 x]
      Q.normalizedCoefficients :=
    eventually_of_mem (f.open_source.mem_nhds (hWf (hVW hx))) hlink
  have htwo : metricTwoJet ((G.flow.metric 0).pullbackCoefficients (targetChart f p)) x =
      metricTwoJet Q.normalizedCoefficients x := by
    simp only [metricTwoJet, hcoeff.eq_of_nhds, hcoeff.fderiv_eq,
      (hcoeff.fderiv (𝕜 := ℝ)).fderiv_eq]
  have hJnear := (hnear _ _ _ _ _ Q
    (heta.trans ((min_le_right _ _).trans (min_le_left _ _)))).2 x (hWK (hVW hx))
  refine ⟨f, hfsource, hftarget, hfmap, G, p, ?_⟩
  intro T hT hTB hTtau
  apply hstop F (F.slice a) e hU (by simpa only [inv_pow, inv_inv] using hsmall)
    f hfU hfconnected G hT hTB (hTtau.trans (min_le_left _ _))
    (hTtau.trans (min_le_right _ _)) (hq.trans hM) _ hscalar0 hpinch c
    (fun j hj y hy => hcurv y hy j hj) hV hVW
    (fun y hy => (hbuffer y hy).1) (fun y hy => (hbuffer y hy).2)
    (fun y hy => (hjets y (hVW hy)).1)
    (fun y hy => (hjets y (hVW hy)).2.1)
    (fun y hy j hj => (hjets y (hVW hy)).2.2 j (by omega)) x hx J (mem_singleton J)
    (by change ‖metricTwoJet ((G.flow.metric 0).pullbackCoefficients
          (targetChart f p)) x - J‖ ≤ dJ; rw [htwo]; exact hJnear)
  intro s hs y hhigh hsI
  apply hcanonical s hsI (cylinderTargetTransport e f s hsI y)
  rw [G.scalar_eq hU hfU s hsI y] at hhigh
  apply (div_le_div_iff_of_pos_right hscale).mp
  simpa only [div_eq_mul_inv, inv_pow, inv_inv, mul_comm] using hhigh

end PoincareConjecture.M44
