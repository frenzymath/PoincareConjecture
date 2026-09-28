import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_10_RemovalRestartSurvival

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.M44

open SpacetimeBounds

local notation "E" => StandardCapSpace

noncomputable local instance restartControlCoefficientNorm :
    NormedAddCommGroup (MetricCoefficient 3) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance restartControlCoefficientSpace :
    NormedSpace ℝ (MetricCoefficient 3) := ContinuousLinearMap.toNormedSpace

noncomputable local instance restartControlTwoJetNorm :
    NormedAddCommGroup (MetricTwoJet 3) := Prod.normedAddCommGroup

noncomputable local instance restartControlTwoJetSpace :
    NormedSpace ℝ (MetricTwoJet 3) := Prod.normedSpace

theorem exists_restarted_outer_control_cutoff
    (P : M44CapPersistencePredecessors.{u})
    {g0 : StandardInitialMetric} (standard : RepairedStandardCapExistenceData g0)
    {C r A H M Kpast : ℝ} (hC : 0 < C) (hA : 0 < A)
    (hH : 0 < H) (hH1 : H < 1) (hM : 0 < M) :
    ∃ R0 tau accuracy : ℝ, ∃ compact : Set E,
      A < R0 ∧ 2 < R0 ∧ 0 < tau ∧ 0 < accuracy ∧ IsCompact compact ∧
      compact ⊆ g0.metric.ball 0 (R0 - 2) ∧
      ∀ R : ℝ, R0 ≤ R → ∃ eta0 delta0 : ℝ, 0 < eta0 ∧ 0 < delta0 ∧
      ∀ (F : SurgeryFlowData.{u}) (O : SurgeryObservation F)
        {constants : MetricSurgeryConstants} (setup : SurgeryControlSetup constants)
        {start rNext deltaBar : ℝ},
      SurgeryFixedScalesOn setup F O start rNext deltaBar → deltaBar ≤ delta0 →
      ∀ (birth : ℝ) (hbirth : birth ∈ F.surgery_times)
        [Nonempty (F.slice birth).carrier] (i : Fin (F.event birth hbirth).cap_count)
        {B : ℝ}, B ≤ H →
      (∀ s ∈ Ico 0 B,
        birth + s / ((F.parameters.h birth)⁻¹ ^ 2) ∈ surgeryObservationInterval O ∩ Ici start) →
      ∀ D : MaximalCapSample g0 F birth hbirth i B,
      D.radius = R → D.eta ≤ eta0 → F.parameters.h birth ^ 2 ≤ 1 →
      F.parameters.h birth ^ 2 * (r⁻¹ ^ 2) ≤ M → F.parameters.C = C →
      SurgeryCanonicalOn F (surgeryObservationInterval O) r → SurgeryFlowPinched F →
      ∀ a : ℝ, 0 ≤ a → a < D.lifetime →
      (∀ y, (D.ordinary.flow.connection a).scalarCurvature y ≤ M) →
      (∀ s ∈ Icc (0 : ℝ) a, ∀ y,
        (D.ordinary.flow.connection s).curvatureTensorNorm y ≤ Kpast) →
      (∀ x ∈ compact,
        ‖metricTwoJet (fun y => D.toCylinderCompactnessSample.coefficients (a, y)) x -
          metricTwoJet (standard.flow.metric a).euclideanCoefficients x‖ ≤ accuracy) →
      ∀ {V : Set (F.slice birth).carrier}, V ⊆ D.region → V.Nonempty →
      ∀ {d : ℝ}, d ≤ B →
      ∀ inner : SurgeryFlowCylinder F (F.slice birth) birth ((F.parameters.h birth)⁻¹ ^ 2)
        (Ico 0 d) V,
      (∀ hs x, x ∈ V → HEq (inner.forward 0 hs x) x) →
        min d (a + tau) ≤ D.lifetime ∧
        ∀ s ∈ Ico (0 : ℝ) (min d (a + tau)), ∀ y,
          (D.ordinary.flow.connection s).curvatureTensorNorm y ≤
            max Kpast (13 * max (2 * M) (Real.exp 4)) := by
  obtain ⟨R1, tau1, accuracy1, compact1, hAR1, hR1, htau1, haccuracy1,
    hcompact1, _hinside1, hsurvival⟩ :=
    exists_restarted_outer_survival_cutoff P standard hC hA hH hH1 hM (r := r) (Kpast := Kpast)
  obtain ⟨x, u, v, hmodel, hcollar⟩ := exists_global_standard_collar standard hC hH.le hH1
  let model := (fun t => metricTwoJet (standard.flow.metric t).euclideanCoefficients x) ''
    Icc (0 : ℝ) H
  have hmargin : model ⊆ collarJetRegion C u v := by
    rintro _ ⟨t, ht, rfl⟩
    exact hcollar t ht
  let compact := compact1 ∪ {x}
  have hcompact : IsCompact compact := hcompact1.union isCompact_singleton
  obtain ⟨S, _hS, hR1S, hsub⟩ := exists_standard_ball_containing_compact g0 hcompact R1
  let R0 := S + 3
  have hR1R0 : R1 ≤ R0 := by dsimp [R0]; linarith
  have hR0 : 2 < R0 := hR1.trans_le hR1R0
  have hinside : compact ⊆ g0.metric.ball 0 (R0 - 2) := by
    intro y hy
    exact (hsub hy).trans_le (ENNReal.ofReal_le_ofReal (by dsimp [R0]; linarith))
  have hx : x ∈ g0.metric.ball 0 (R0 - 2) := hinside (Or.inr (mem_singleton x))
  obtain ⟨d2, tau2, hd2, htau2, hrestart⟩ :=
    exists_sample_restart_cutoff P g0 C x u v hmodel hmargin hR0 hx hM hH
      (Kpast := Kpast)
  refine ⟨R0, min tau1 tau2, min accuracy1 d2, compact, hAR1.trans_le hR1R0,
    hR0, lt_min htau1 htau2, lt_min haccuracy1 hd2, hcompact, hinside, ?_⟩
  intro R hR
  obtain ⟨eta1, delta1, heta1, hdelta1, hsurvive⟩ := hsurvival R (hR1R0.trans hR)
  refine ⟨min eta1 d2, delta1, lt_min heta1 hd2, hdelta1, ?_⟩
  intro F O constants setup start rNext deltaBar hscales hdelta birth hbirth _ i B hBH
    hclock D hDR heta hsmall hthreshold hconstant hcanonical hpinch a ha hac
    hscalar hpast hnear V hVU hV d hdB inner hinitialInner
  have hsurv1 := hsurvive F O setup hscales hdelta birth hbirth i hBH hclock D hDR
    (heta.trans (min_le_left _ _)) hsmall hthreshold hconstant hcanonical hpinch a ha hac
    hscalar hpast (fun y hy => (hnear y (Or.inl hy)).trans (min_le_left _ _))
    hVU hV hdB inner hinitialInner
  have hsurv : min d (a + min tau1 tau2) ≤ D.lifetime :=
    (min_le_min_left d (add_le_add le_rfl (min_le_left tau1 tau2))).trans hsurv1
  refine ⟨hsurv, ?_⟩
  intro s hs y
  by_cases hsa : s ≤ a
  · exact (hpast s ⟨hs.1, hsa⟩ y).trans (le_max_left _ _)
  · have has : a < s := lt_of_not_ge hsa
    have hsLife : s < D.lifetime := hs.2.trans_le hsurv
    have hsTau : s < a + tau2 := (hs.2.trans_le (min_le_right _ _)).trans_le
      (add_le_add le_rfl (min_le_right tau1 tau2))
    obtain ⟨T, hsT, hT⟩ := exists_between (lt_min hsLife hsTau)
    have hTLife : T < D.lifetime := hT.trans_le (min_le_left _ _)
    have hshort : T - a ≤ tau2 := by
      have hTa : T < a + tau2 := hT.trans_le (min_le_right _ _)
      linarith only [hTa]
    have hcanonical' (t : ℝ) (ht : t ∈ Ico (0 : ℝ) D.lifetime)
        (z : (F.slice (birth + t / ((F.parameters.h birth)⁻¹ ^ 2))).carrier)
        (hz : r⁻¹ ^ 2 ≤
          (F.connection (birth + t / ((F.parameters.h birth)⁻¹ ^ 2))).scalarCurvature z) :
        SurgeryCanonicalControl F (birth + t / ((F.parameters.h birth)⁻¹ ^ 2)) z
          F.parameters.epsilon C := by
      rw [← hconstant]
      exact hcanonical _ (hclock t ⟨ht.1, ht.2.trans_le D.lifetime_le⟩).1
        (D.cylinder.time_subset (mem_image_of_mem _ ht)) z hz
    have haH : a ∈ Icc (0 : ℝ) H :=
      ⟨ha, hac.le.trans (D.lifetime_le.trans hBH)⟩
    have hR' : R0 ≤ D.radius := by rwa [hDR]
    have h := hrestart F birth hbirth i D.toCylinderCompactnessSample hR'
      (heta.trans (min_le_right _ _)) D.region_open hsmall (r⁻¹ ^ 2) hthreshold
      hcanonical' hpinch a T ha (has.trans hsT) hTLife
      (hTLife.le.trans (D.lifetime_le.trans hBH)) hshort hscalar hpast
      _ (mem_image_of_mem _ haH)
      ((hnear x (Or.inr (mem_singleton x))).trans (min_le_right _ _))
    exact ((h.2 s ⟨has.le, hsT.le⟩ y).2).trans (le_max_right _ _)

end PoincareConjecture.M44
