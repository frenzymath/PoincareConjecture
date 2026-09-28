import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma16_8_StoppedSurgerySlab
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma16_8_InitialChartBounds
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma16_8_InitialTwoJet
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_NormalizedBirthBalls










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.M44

open SpacetimeBounds

local notation "E" => StandardCapSpace

noncomputable local instance initialSlabCoefficientNormedGroup :
    NormedAddCommGroup (MetricCoefficient 3) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance initialSlabCoefficientNormedSpace :
    NormedSpace ℝ (MetricCoefficient 3) := ContinuousLinearMap.toNormedSpace

noncomputable local instance initialSlabTwoJetNormedGroup :
    NormedAddCommGroup (MetricTwoJet 3) := Prod.normedAddCommGroup

noncomputable local instance initialSlabTwoJetNormedSpace :
    NormedSpace ℝ (MetricTwoJet 3) := Prod.normedSpace





theorem exists_initial_slab_bound (P : M44CapPersistencePredecessors.{u})
    (g0 : StandardInitialMetric) (C : ℝ) (x u v : E)
    (hcollar : metricTwoJet g0.metric.euclideanCoefficients x ∈ collarJetRegion C u v)
    {R : ℝ} (hR : 2 < R) (hx : x ∈ g0.metric.ball 0 (R - 2)) :
    ∃ delta tau M : ℝ, 0 < delta ∧ 0 < tau ∧ 1 ≤ M ∧
      ∀ (F : SurgeryFlowData.{u}), F.standard_initial = g0 →
      ∀ (a : ℝ) (ha : a ∈ F.surgery_times) [Nonempty (F.slice a).carrier],
      ∀ (i : Fin (F.event a ha).cap_count) {T eta q : ℝ},
      0 < T → T ≤ 1 → T ≤ tau → F.parameters.h a ^ 2 ≤ 1 →
      F.parameters.h a ^ 2 * q ≤ 1 →
      ∀ (S : SurgeryRegularSlab F.slice F.metric a (a + T * F.parameters.h a ^ 2))
        (G : RicciFlow 3 (F.slice a).carrier (Icc 0 T)),
      (∀ s ∈ Icc (0 : ℝ) T, ∀ y w z,
        (S.flow.metric (a + s * F.parameters.h a ^ 2)).inner y w z =
          F.parameters.h a ^ 2 * (G.metric s).inner y w z) →
      (∀ y w z, (G.metric 0).inner y w z =
        (F.parameters.h a)⁻¹ ^ 2 * (F.metric a).inner y w z) →
      ∀ Q : SurgeryCapClose F.standard_initial
        ((F.event a ha).local_result i).output ((F.event a ha).local_result i).metric
        ((F.event a ha).local_result i).tip (((F.event a ha).necks i).neck.scale) eta,
      eta ≤ delta →
      (∀ r : ℝ, 0 < r → r ≤ eta⁻¹ → Q.map '' F.standard_initial.metric.ball 0 r =
        ((F.event a ha).local_result i).metric.ball ((F.event a ha).local_result i).tip
          (((F.event a ha).necks i).neck.scale * r)) →
      (∀ t ∈ Ico a (a + T * F.parameters.h a ^ 2), ∀ y,
        q ≤ (F.connection t).scalarCurvature y →
        SurgeryCanonicalControl F t y F.parameters.epsilon C) →
      SurgeryFlowPinched F → Icc a (a + T * F.parameters.h a ^ 2) ⊆ F.time_domain →
      ∃ e : PartialDiffeomorph (𝓡 3) (𝓡 3) E (F.slice a).carrier ∞,
        e.source = F.standard_initial.metric.ball 0 R ∧
        e.target = (G.metric 0).ball ((F.event a ha).caps i).tip R ∧
        (∀ y, e y = (F.event a ha).local_embed i (Q.map y)) ∧
        (∀ s ∈ Icc (0 : ℝ) T,
          metricTwoJet ((G.metric s).pullbackCoefficients e) x ∈ collarJetRegion C u v) ∧
        (∀ s ∈ Icc (0 : ℝ) T, ∀ y ∈ e.target,
          (G.connection s).scalarCurvature y ≤ 2 * M ∧
          (G.connection s).curvatureTensorNorm y ≤ 13 * max (2 * M) (Real.exp 4)) := by
  let K := {y : E | g0.metric.edist 0 y ≤ ENNReal.ofReal R}
  have hR0 : 0 < R := by linarith
  have hK : IsCompact K := M36.standard_closed_ball_compact g0 hR0.le
  obtain ⟨dB, alpha, Z, K0, hdB, halpha, hZ, hK0, hbounds⟩ :=
    exists_initial_chart_bounds.{u, u} g0 hK 2
  let M := 9 * K0
  have hM : 1 ≤ M := by dsimp [M]; linarith only [hK0]
  let J := metricTwoJet g0.metric.euclideanCoefficients x
  obtain ⟨dJ, tau, hdJ, htau, hstop⟩ :=
    exists_stopped_surgery_slab_bound P C u v (model := {J}) isCompact_singleton
      (by intro z hz; obtain rfl : z = J := hz; exact hcollar)
      (zero_lt_one.trans_le hM) (zero_lt_one.trans_le hK0)
      (H := 1) (r := 1) zero_lt_one zero_lt_one halpha (zero_le_one.trans hZ) hZ
  obtain ⟨d2, hd2, hnear⟩ := exists_initial_twoJet_cutoff.{u} g0 hK hdJ
  let delta := min dB (min d2 (R + 1)⁻¹)
  have hdelta : 0 < delta := lt_min hdB (lt_min hd2 (inv_pos.mpr (by linarith)))
  refine ⟨delta, tau, M, hdelta, htau, hM, ?_⟩
  intro F hg0 a ha _ i T eta q hT hT1 hTtau hsmall hq S G hmetric hg Q heta hballs
    hcanonical hpinch hdomain
  subst g0
  have hReta : R < eta⁻¹ := by
    have hcut : eta ≤ (R + 1)⁻¹ := heta.trans ((min_le_right _ _).trans (min_le_right _ _))
    have hinv := one_div_le_one_div_of_le Q.eta_pos hcut
    simp only [one_div, inv_inv] at hinv
    linarith only [hinv]
  obtain ⟨e, hsource, hmap, htarget, hconnected⟩ :=
    exists_physical_birth_chart F a ha i hR0 hReta Q (hballs R hR0 hReta.le)
  have hheight := F.parameters.h_pos a (F.time_domain_nonnegative (F.surgery_times_subset ha))
  have htarget' : e.target = (G.metric 0).ball ((F.event a ha).caps i).tip R := by
    rw [normalized_birth_ball (F.metric a) (G.metric 0) hheight hg]
    exact htarget
  have hsub : e.source ⊆ K := by
    rw [hsource]
    intro y hy
    change F.standard_initial.metric.edist 0 y ≤ ENNReal.ofReal R
    exact hy.le
  have hcomparison : e.source ⊆ F.standard_initial.metric.ball 0 eta⁻¹ := by
    rw [hsource]
    exact fun _ hy => hy.trans_le (ENNReal.ofReal_le_ofReal hReta.le)
  have hlink := physical_birth_pullback_eq F a ha i Q (G.metric 0) hg
    e.open_source hcomparison (fun y _ => hmap y)
  obtain ⟨hjets, hcurv, hscalar⟩ := hbounds _ _ _ _ _ Q (heta.trans (min_le_left _ _))
    (F.slice a) (G.metric 0) (G.connection 0) e hsub hlink
  let V := F.standard_initial.metric.ball 0 (R - 2)
  have hV : IsOpen V := by
    dsimp only [V]
    rw [M36.standard_ball_eq_euclidean F.standard_initial (by linarith : 0 < R - 2)]
    exact Metric.isOpen_ball
  have hVs : V ⊆ e.source := by
    rw [hsource]
    exact fun _ hy => hy.trans_le (ENNReal.ofReal_le_ofReal (by linarith : R - 2 ≤ R))
  have hVimage : e '' V = (G.metric 0).ball ((F.event a ha).caps i).tip (R - 2) := by
    apply physical_birth_chart_image_ball F a ha i (by linarith) (by linarith) Q
      (hballs (R - 2) (by linarith) (by linarith)) (G.metric 0) hg e
    exact fun y _ => hmap y
  have hbuffer := physical_birth_chart_buffer_balls F (F.surgery_times_subset ha)
    (G.metric 0) ((F.event a ha).caps i).tip e
    (a := R - 2) (r := 1) (R := R) (by linarith) zero_le_one (by linarith) htarget'
    (le_of_eq hVimage)
  have hxK : x ∈ K := hsub (hVs hx)
  have hJnear := (hnear _ _ _ _ _ Q
    (heta.trans ((min_le_right _ _).trans (min_le_left _ _)))).2 x hxK
  have hcoeff : (G.metric 0).pullbackCoefficients e =ᶠ[𝓝 x] Q.normalizedCoefficients :=
    eventually_of_mem (e.open_source.mem_nhds (hVs hx)) hlink
  have htwo : metricTwoJet ((G.metric 0).pullbackCoefficients e) x =
      metricTwoJet Q.normalizedCoefficients x := by
    simp only [metricTwoJet, hcoeff.eq_of_nhds, hcoeff.fderiv_eq,
      (hcoeff.fderiv (𝕜 := ℝ)).fderiv_eq]
  obtain ⟨hkeep, hbound⟩ := hstop F hT hT1 hTtau (sq_pos_of_pos hheight) hsmall S G
    hmetric e hconnected (fun j hj y hy => hcurv y hy j hj) hscalar (hq.trans hM)
    (fun t y _ hhigh => hcanonical t.1 t.2 (S.identify ⟨t.1, t.2.1, t.2.2.le⟩ y)
      (by rwa [regularSlab_scalar_eq F S ⟨t.1, t.2.1, t.2.2.le⟩ y]))
    hpinch hdomain hV hVs (fun y hy => (hbuffer y hy).1) (fun y hy => (hbuffer y hy).2)
    (fun y hy => (hjets y (hVs hy)).1)
    (fun y hy => (hjets y (hVs hy)).2.1)
    (fun y hy j hj => (hjets y (hVs hy)).2.2 j (by omega)) x hx J (mem_singleton J)
    (by rw [htwo]; exact hJnear)
  exact ⟨e, hsource, htarget', hmap, hkeep, hbound⟩

end PoincareConjecture.M44
