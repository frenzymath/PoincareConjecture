import PoincareConjecture.Proofs.M47.BlowupControlsSourceControl
import PoincareConjecture.Proofs.M47.BlowupControlsSourceMetric










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M47



theorem exists_first_failure_short_search_geometry
    (P : M46Predecessors.{u}) (S : RepairedControlledSchedulesData.{u})
    (B : M47ComponentAnalyticBounds.{u} S.setup.C) {A : ℝ} (hA : 0 ≤ A) :
    ∃ Q0 tau K : ℝ, 0 < Q0 ∧ 0 < tau ∧ tau ≤ 1 ∧ 0 < K ∧
      ∀ (p : SurgeryParameterPrefix S.constants) (F : SurgeryFlowData.{u})
        (O : SurgeryObservation F),
      F.standard_initial = S.setup.standard_initial → F.local_constants = S.constants →
      F.parameters.epsilon = S.setup.epsilon → F.parameters.C = S.setup.C →
      ∀ (W : M33RegularHistoryWindow F) (H : M33RegularHistoryData W)
        {base Q r a : ℝ} (ht : base ∈ H.generalized.interval),
      base ∈ Ico (surgeryEpochStart p.i) O.H → Q0 ≤ Q → r⁻¹ ^ 2 ≤ Q →
      SurgeryFlowPinched F →
      SurgeryCanonicalOn F (surgeryObservationInterval O ∩ Iio base) r →
      (∀ t ∈ surgeryObservationInterval O ∩ Ico (surgeryEpochStart (p.i - 1)) O.H,
        F.parameters.delta t ≤ B.delta S.setup.standard_initial S.constants) →
      a ∈ Ico (-tau) 0 → ∀ x : (H.generalized.slice base).carrier,
      H.generalized.scalar ⟨base, x⟩ = Q →
      ∀ e : SurgeryFlowCylinder F (F.slice base) base Q (Icc a 0)
        ((F.metric base).ball (H.history.forward base ht x) (A / Real.sqrt Q)),
      (∀ hs y,
        y ∈ (F.metric base).ball (H.history.forward base ht x) (A / Real.sqrt Q) →
          HEq (e.forward 0 hs y) y) →
      ∀ s (hs : s ∈ Icc a 0),
        ∀ y ∈ (F.metric base).ball (H.history.forward base ht x) (A / Real.sqrt Q),
          (F.connection (base + s / Q)).scalarCurvature (e.forward s hs y) ≤ K * Q ∧
          |(F.connection (base + s / Q)).curvatureTensorNorm (e.forward s hs y)| ≤ K * Q ∧
          ∀ v : TangentSpace (𝓡 3) y,
            (F.metric base).inner y v v ≤
              2 * (F.metric (base + s / Q)).inner (e.forward s hs y)
                (mfderiv (𝓡 3) (𝓡 3) (e.forward s hs) y v)
                (mfderiv (𝓡 3) (𝓡 3) (e.forward s hs) y v) ∧
            (F.metric (base + s / Q)).inner (e.forward s hs y)
                (mfderiv (𝓡 3) (𝓡 3) (e.forward s hs) y v)
                (mfderiv (𝓡 3) (𝓡 3) (e.forward s hs) y v) ≤
              2 * (F.metric base).inner y v v := by
  obtain ⟨Qmin, tau0, K0, hQmin, htau0, htauOne, hK0, hscalar⟩ :=
    exists_first_failure_short_search_scalar_bound S B hA
  let K := 13 * max K0 1
  let tau := min tau0 (12 * K)⁻¹
  let Q0 := max Qmin (blowupPinchingThreshold K0 1)
  have hK : 0 < K := mul_pos (by norm_num) (zero_lt_one.trans_le (le_max_right _ _))
  have hK0K : K0 ≤ K := by
    have hm : 0 ≤ max K0 1 := le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_max_right _ _)
    dsimp only [K]
    linarith only [le_max_left K0 1, hm]
  refine ⟨Q0, tau, K, hQmin.trans_le (le_max_left _ _),
    lt_min htau0 (inv_pos.mpr (mul_pos (by norm_num) hK)),
    (min_le_left _ _).trans htauOne, hK, ?_⟩
  intro p F O hInitial hConstants he hC W H base Q r a ht hBase hLarge hThreshold
    hPinched hEarlier hOverlap ha x hscale e hbased
  let P44 : M44CapPersistencePredecessors.{u} := ⟨P.m04, P.m13.ordinary_flow⟩
  have hQ := e.scale_pos
  have ha0 : a ∈ Ico (-tau0) 0 :=
    ⟨(neg_le_neg (min_le_left tau0 (12 * K)⁻¹)).trans ha.1, ha.2⟩
  have hR := hscalar p P44 F O hInitial hConstants he hC W H ht hBase
    ((le_max_left _ _).trans hLarge) hThreshold hPinched hEarlier hOverlap ha0 x hscale e hbased
  have hRm (s : ℝ) (hs : s ∈ Icc a 0)
      (y : (F.slice base).carrier)
      (hy : y ∈ (F.metric base).ball (H.history.forward base ht x) (A / Real.sqrt Q)) :
      |(F.connection (base + s / Q)).curvatureTensorNorm (e.forward s hs y)| ≤ K * Q :=
    (pinched_blowup_curvature_bounds P
      (hPinched _ (e.time_subset (mem_image_of_mem _ hs))) hK0.le zero_lt_one
      ((le_max_right _ _).trans hLarge) (mem_univ _) (hR s hs y hy)).1
  have hshort : 6 * K * (-a) ≤ 1 / 2 := by
    have htime : -a ≤ (12 * K)⁻¹ :=
      (show -a ≤ tau by linarith only [ha.1]).trans (min_le_right _ _)
    calc
      _ ≤ (6 * K) * (12 * K)⁻¹ :=
        mul_le_mul_of_nonneg_left htime (mul_nonneg (by norm_num) hK.le)
      _ = 1 / 2 := by field_simp [hK.ne']; ring
  have hmetric := normalized_search_metric_comparison P44 hPinched e
    (M04.initial_ball_isOpen _ _ _) ha.2.le hK.le hbased
    (fun s hs y hy => (le_abs_self _).trans (hRm s hs y hy)) hshort
  intro s hs y hy
  exact ⟨(hR s hs y hy).trans (mul_le_mul_of_nonneg_right hK0K hQ.le),
    hRm s hs y hy, hmetric s hs y hy⟩

end PoincareConjecture.M47
