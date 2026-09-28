import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma16_8_InitialCylinder











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.M44

open SpacetimeBounds

local notation "E" => StandardCapSpace

noncomputable local instance cylinderEstimateCoefficientNorm : NormedAddCommGroup
    (MetricCoefficient 3) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance cylinderEstimateCoefficientSpace : NormedSpace ℝ
    (MetricCoefficient 3) := ContinuousLinearMap.toNormedSpace





theorem exists_cylinder_coordinate_estimates (P : M44CapPersistencePredecessors.{u})
    (g0 : StandardInitialMetric) (m : ℕ) {R0 H K : ℝ}
    (hR0 : 2 < R0) (hH : 0 < H) (hK : 0 < K) :
    ∃ delta alpha Z L : ℝ, 0 < delta ∧ 0 < alpha ∧ 1 ≤ Z ∧ 0 ≤ L ∧
      ∀ (F : SurgeryFlowData.{u}), F.standard_initial = g0 →
      ∀ (a : ℝ) (ha : a ∈ F.surgery_times) [Nonempty (F.slice a).carrier],
      ∀ (i : Fin (F.event a ha).cap_count) {R eta B : ℝ}, R0 ≤ R → R < eta⁻¹ → 0 < B →
      ∀ Q : SurgeryCapClose F.standard_initial
        ((F.event a ha).local_result i).output ((F.event a ha).local_result i).metric
        ((F.event a ha).local_result i).tip (((F.event a ha).necks i).neck.scale) eta,
      eta ≤ delta →
      (∀ r : ℝ, 0 < r → r ≤ eta⁻¹ → Q.map '' F.standard_initial.metric.ball 0 r =
        ((F.event a ha).local_result i).metric.ball ((F.event a ha).local_result i).tip
          (((F.event a ha).necks i).neck.scale * r)) →
      ∀ f : PartialDiffeomorph (𝓡 3) (𝓡 3) E (F.slice a).carrier ∞,
      f.source = F.standard_initial.metric.ball 0 R →
      (∀ y, f y = (F.event a ha).local_embed i (Q.map y)) →
      ∀ {U : Set (F.slice a).carrier},
      ∀ e : SurgeryFlowCylinder F (F.slice a) a ((F.parameters.h a)⁻¹ ^ 2) (Ico 0 B) U,
      f.target ⊆ U → (∀ h y, y ∈ U → HEq (e.forward 0 h y) y) →
      ∀ G : CylinderRicciFlow e f,
      ∀ p : (⟨f.target, f.open_target⟩ : Opens (F.slice a).carrier),
      ∀ T : ℝ, 0 < T → T < B → T ≤ H →
      (∀ s ∈ Icc (0 : ℝ) T, ∀ y, (G.flow.connection s).curvatureTensorNorm y ≤ K) →
      ∀ x ∈ F.standard_initial.metric.ball 0 (R0 - 2),
        (∀ s ∈ Icc (0 : ℝ) T, ∀ w : E,
          alpha * ‖w‖ ^ 2 ≤ (G.flow.metric s).pullbackCoefficients (targetChart f p) x w w) ∧
        ∀ j ≤ m,
          (∀ s ∈ Icc (0 : ℝ) T,
            ‖iteratedFDeriv ℝ j ((G.flow.metric s).pullbackCoefficients
              (targetChart f p)) x‖ ≤ Z) ∧
          (∀ s ∈ Icc (0 : ℝ) T, ∀ t ∈ Icc (0 : ℝ) T,
            ‖iteratedFDeriv ℝ j ((G.flow.metric t).pullbackCoefficients (targetChart f p)) x -
              iteratedFDeriv ℝ j ((G.flow.metric s).pullbackCoefficients (targetChart f p)) x‖ ≤
                L * |t - s|) := by
  let C := {y : E | g0.metric.edist 0 y ≤ ENNReal.ofReal R0}
  have hC : IsCompact C := M36.standard_closed_ball_compact g0 (by linarith)
  obtain ⟨delta, alpha, Z0, K0, hdelta, halpha, hZ0, hK0, hbounds⟩ :=
    exists_initial_chart_bounds.{u, u} g0 hC m
  let K1 := max K K0
  have hKK : K ≤ K1 := le_max_left _ _
  have hK0K : K0 ≤ K1 := le_max_right _ _
  obtain ⟨Z, L, hZ, hL, hmod⟩ := exists_local_coordinate_modulus P m
    (hK.trans_le hKK) hH (r := 1) zero_lt_one halpha (zero_le_one.trans hZ0) hZ0
  refine ⟨delta, Real.exp (-6 * K * H) * alpha, Z, L, hdelta,
    mul_pos (Real.exp_pos _) halpha, hZ, hL, ?_⟩
  intro F hg0 a ha _ i R eta B hR hReta hB Q heta hballs f hfsource hfmap
    U e hfU hinitial G p T hT hTB hTH hcurv x hx
  subst g0
  have hh := F.parameters.h_pos a (F.time_domain_nonnegative (F.surgery_times_subset ha))
  have hscale : 0 < (F.parameters.h a)⁻¹ ^ 2 := sq_pos_of_pos (inv_pos.mpr hh)
  let g := m01RescaledMetric (F.metric a) ((F.parameters.h a)⁻¹ ^ 2) hscale
  have hg (y) (w z) : g.inner y w z = (F.parameters.h a)⁻¹ ^ 2 *
      (F.metric a).inner y w z := rfl
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
  have hWC : W ⊆ C := by
    intro y hy
    change F.standard_initial.metric.edist 0 y ≤ ENNReal.ofReal R0
    exact hy.le
  obtain ⟨hjets, hinitialCurv, _⟩ := hbounds _ _ _ _ _ Q heta
    N (G.flow.metric 0) (G.flow.connection 0) c hWC (fun y hy => hlink (hWf hy))
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
  constructor
  · intro s hs w
    have hcmp := (P.curvature.metric_comparison 3 _ (Ico 0 B) G.flow 0 s K
      ⟨le_rfl, hB⟩ ⟨hs.1, hs.2.trans_lt hTB⟩ hs.1 hK.le
      (fun t ht => hcurv t ⟨ht.1, ht.2.trans hs.2⟩)
      (targetChart f p x) (mfderiv (𝓡 3) (𝓡 3) (targetChart f p) x w)).1
    change Real.exp (-2 * (3 : ℝ) * K * (s - 0)) *
      (G.flow.metric 0).pullbackCoefficients (targetChart f p) x w w ≤ _ at hcmp
    have hbirth := (hjets x (hVW hx)).1 w
    change alpha * ‖w‖ ^ 2 ≤
      (G.flow.metric 0).pullbackCoefficients (targetChart f p) x w w at hbirth
    calc
      _ = Real.exp (-6 * K * H) * (alpha * ‖w‖ ^ 2) := by ring
      _ ≤ Real.exp (-2 * (3 : ℝ) * K * (s - 0)) * (alpha * ‖w‖ ^ 2) := by
        apply mul_le_mul_of_nonneg_right _ (mul_nonneg halpha.le (sq_nonneg _))
        apply Real.exp_le_exp.mpr
        nlinarith only [mul_le_mul_of_nonneg_left (hs.2.trans hTH) hK.le]
      _ ≤ Real.exp (-2 * (3 : ℝ) * K * (s - 0)) *
          (G.flow.metric 0).pullbackCoefficients (targetChart f p) x w w :=
        mul_le_mul_of_nonneg_left hbirth (Real.exp_pos _).le
      _ ≤ _ := hcmp
  · intro j hj
    let Gc := Poincare.Geometry.RicciFlow.Harnack.restrictFlow G.flow
      (show Icc (0 : ℝ) T ⊆ Ico 0 B from fun _ hs => ⟨hs.1, hs.2.trans_lt hTB⟩)
      ordConnected_Icc (Icc_infinite hT).nontrivial
    exact hmod _ hT hTH Gc c
      (fun s hs y _ => (hcurv s hs y).trans hKK)
      (fun l hl y hy => (hinitialCurv y hy l hl).trans hK0K)
      hV hVW (fun y hy => (hbuffer y hy).1) (fun y hy => (hbuffer y hy).2)
      (fun y hy => (hjets y (hVW hy)).1)
      (fun y hy => (hjets y (hVW hy)).2.1)
      (fun y hy l hl => (hjets y (hVW hy)).2.2 l (by omega)) j hj x hx

end PoincareConjecture.M44
