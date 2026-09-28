import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_CylinderCoordinateEstimates
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_10_StandardSphereMargin










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 16

open Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M44

open SpacetimeBounds

local notation "E" => StandardCapSpace

noncomputable local instance initialSphereCoefficientNorm : NormedAddCommGroup
    (MetricCoefficient 3) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance initialSphereCoefficientSpace : NormedSpace ℝ
    (MetricCoefficient 3) := ContinuousLinearMap.toNormedSpace

noncomputable local instance initialSphereTwoJetNorm : NormedAddCommGroup
    (MetricTwoJet 3) := Prod.normedAddCommGroup

noncomputable local instance initialSphereTwoJetSpace : NormedSpace ℝ
    (MetricTwoJet 3) := Prod.normedSpace




theorem exists_initial_cylinder_twoJet_control
    (P : M44CapPersistencePredecessors.{u}) (g0 : StandardInitialMetric)
    {C : Set E} (hC : IsCompact C) {R0 H K accuracy : ℝ}
    (hR0 : 2 < R0) (hCsub : C ⊆ g0.metric.ball 0 (R0 - 2))
    (hH : 0 < H) (hK : 0 < K) (haccuracy : 0 < accuracy) :
    ∃ delta tau : ℝ, 0 < delta ∧ 0 < tau ∧
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
      ∀ T : ℝ, 0 < T → T < B → T ≤ H → T ≤ tau →
      (∀ s ∈ Icc (0 : ℝ) T, ∀ y, (G.flow.connection s).curvatureTensorNorm y ≤ K) →
      ∀ s ∈ Icc (0 : ℝ) T, ∀ x ∈ C,
        ‖metricTwoJet ((G.flow.metric s).pullbackCoefficients (targetChart f p)) x -
          metricTwoJet g0.metric.euclideanCoefficients x‖ ≤ accuracy := by
  obtain ⟨d1, alpha, Z, L, hd1, _halpha, _hZ, hL, hest⟩ :=
    exists_cylinder_coordinate_estimates P g0 2 hR0 hH hK
  obtain ⟨d2, hd2, hinit⟩ := exists_initial_twoJet_cutoff.{u} g0 hC (half_pos haccuracy)
  let tau := accuracy / (2 * (L + 1))
  have hden : 0 < 2 * (L + 1) := by positivity
  refine ⟨min d1 d2, tau, lt_min hd1 hd2, div_pos haccuracy hden, ?_⟩
  intro F hg0 a ha _ i R eta B hR hReta hB Q heta hballs f hfsource hfmap
    U e hfU hinitial G p T hT hTB hTH hTtau hcurv s hs x hx
  subst g0
  have hxf : x ∈ f.source := by
    rw [hfsource]
    exact (hCsub hx).trans_le (ENNReal.ofReal_le_ofReal (by linarith))
  have hbounds := hest F rfl a ha i hR hReta hB Q
    (heta.trans (min_le_left _ _)) hballs f hfsource hfmap e hfU hinitial G p
    T hT hTB hTH hcurv x (hCsub hx)
  have htime : ‖metricTwoJet ((G.flow.metric s).pullbackCoefficients (targetChart f p)) x -
      metricTwoJet ((G.flow.metric 0).pullbackCoefficients (targetChart f p)) x‖ ≤
        L * s := by
    simpa only [sub_zero, abs_of_nonneg hs.1] using metricTwoJet_time_modulus
      (fun t => (G.flow.metric t).pullbackCoefficients (targetChart f p)) x
        (fun j hj => (hbounds.2 j hj).2 0 ⟨le_rfl, hT.le⟩ s hs)
  have hLt : L * s ≤ accuracy / 2 := by
    have hmul := (le_div_iff₀ hden).mp hTtau
    have hLs : L * s ≤ L * T := mul_le_mul_of_nonneg_left hs.2 hL
    nlinarith only [hmul, hLs, hT]
  have hh := F.parameters.h_pos a (F.time_domain_nonnegative (F.surgery_times_subset ha))
  have hscale : 0 < (F.parameters.h a)⁻¹ ^ 2 := sq_pos_of_pos (inv_pos.mpr hh)
  let g := m01RescaledMetric (F.metric a) ((F.parameters.h a)⁻¹ ^ 2) hscale
  have hg (y) (w z) : g.inner y w z = (F.parameters.h a)⁻¹ ^ 2 *
      (F.metric a).inner y w z := rfl
  have hfQ : f.source ⊆ F.standard_initial.metric.ball 0 eta⁻¹ := by
    rw [hfsource]
    exact fun _ hy => hy.trans_le (ENNReal.ofReal_le_ofReal hReta.le)
  have hlink : (G.flow.metric 0).pullbackCoefficients (targetChart f p) =ᶠ[𝓝 x]
      Q.normalizedCoefficients := by
    filter_upwards [f.open_source.mem_nhds hxf] with y hy
    exact (G.initial_pullback_eq ⟨le_rfl, hB⟩ hfU hinitial g hg p hy).trans
      (physical_birth_pullback_eq F a ha i Q g hg f.open_source hfQ
        (fun z _ => hfmap z) hy)
  have htwo : metricTwoJet ((G.flow.metric 0).pullbackCoefficients (targetChart f p)) x =
      metricTwoJet Q.normalizedCoefficients x := by
    simp only [metricTwoJet, hlink.eq_of_nhds, hlink.fderiv_eq,
      (hlink.fderiv (𝕜 := ℝ)).fderiv_eq]
  have hbirth := (hinit _ _ _ _ _ Q (heta.trans (min_le_right _ _))).2 x hx
  calc
    _ ≤ ‖metricTwoJet ((G.flow.metric s).pullbackCoefficients (targetChart f p)) x -
        metricTwoJet ((G.flow.metric 0).pullbackCoefficients (targetChart f p)) x‖ +
      ‖metricTwoJet ((G.flow.metric 0).pullbackCoefficients (targetChart f p)) x -
        metricTwoJet F.standard_initial.metric.euclideanCoefficients x‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ accuracy / 2 + accuracy / 2 :=
      add_le_add (htime.trans hLt) (by rwa [htwo])
    _ = accuracy := by ring

end PoincareConjecture.M44
