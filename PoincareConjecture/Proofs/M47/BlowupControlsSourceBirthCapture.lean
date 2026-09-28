import PoincareConjecture.Proofs.M47.BlowupControlsSourceBirthScalar
import PoincareConjecture.Proofs.M47.BlowupControlsSourceFrontier
import PoincareConjecture.Proofs.M47.CanonicalNeckCapCapture

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.M47

theorem exists_birth_cap_capture_radius
    (g0 : StandardInitialMetric) {A c D : ℝ} (hA : 0 ≤ A) (hc : 0 < c) (hD : 0 < D) :
    ∃ Acapture : ℝ, g0.cylindrical_end.radius + 5 < Acapture ∧
      ∀ (F : SurgeryFlowData.{u}), F.standard_initial = g0 →
      ∀ {t Q : ℝ} (hT : t ∈ F.surgery_times), ∀ [Nonempty (F.slice t).carrier],
        0 < Q → ∀ (p : (F.slice t).carrier) (i : Fin (F.event t hT).cap_count)
          (z : (F.slice t).carrier),
        z ∈ (F.metric t).ball p (A / Real.sqrt Q) →
        z ∈ ((F.event t hT).caps i).carrier →
        c / (2 * (F.parameters.h t) ^ 2) ≤ (F.connection t).scalarCurvature z →
        (F.connection t).scalarCurvature z ≤ D * Q →
        (F.metric t).ball p (A / Real.sqrt Q) ⊆
          (F.metric t).ball ((F.event t hT).caps i).tip (Acapture * F.parameters.h t) := by
  let L := 1 + 2 * D / c
  let Acap := g0.cylindrical_end.radius + 5
  let Acapture := Acap + 2 * A * L + 1
  have hL : 0 < L := by dsimp only [L]; positivity
  have hAcap : 0 < Acap := by
    dsimp only [Acap]
    linarith [g0.cylindrical_end.radius_pos]
  refine ⟨Acapture, ?_, ?_⟩
  · dsimp only [Acapture, Acap]
    nlinarith [mul_nonneg hA hL.le]
  intro F hinitial t Q hT hn hQ p i z hz hzcap hfloor hceiling y hy
  let h := F.parameters.h t
  let g := F.metric t
  let tip := ((F.event t hT).caps i).tip
  have hh : 0 < h := F.parameters.h_pos t (F.time_domain_nonnegative (F.surgery_times_subset hT))
  have hl : 0 < (Real.sqrt Q)⁻¹ := inv_pos.mpr (Real.sqrt_pos.mpr hQ)
  have hscale : (((Real.sqrt Q)⁻¹)⁻¹) ^ 2 = Q := by
    rw [inv_inv, Real.sq_sqrt hQ.le]
  have hratio : (Real.sqrt Q)⁻¹ ≤ L * h :=
    Proofs.M47.neck_scale_le_cap_height_of_scalar hc hD hl hh hfloor
      (by simpa only [hscale] using hceiling)
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : (F.slice t).carrier → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hsymm : g.edist z p = g.edist p z := Manifold.riemannianEDist_comm
  change g.edist p z < ENNReal.ofReal (A / Real.sqrt Q) at hz
  change g.edist p y < ENNReal.ofReal (A / Real.sqrt Q) at hy
  have hzy : g.edist z y ≤ ENNReal.ofReal (2 * A / Real.sqrt Q) := by
    calc
      _ ≤ g.edist z p + g.edist p y := Manifold.riemannianEDist_triangle
      _ ≤ ENNReal.ofReal (A / Real.sqrt Q) + ENNReal.ofReal (A / Real.sqrt Q) := by
        rw [hsymm]
        exact add_le_add hz.le hy.le
      _ = ENNReal.ofReal (2 * A / Real.sqrt Q) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring
  have htip : g.edist tip z ≤ ENNReal.ofReal (Acap * h) := by
    have houter := ((F.event t hT).caps i).outer_ball hzcap
    have hradius : F.standard_initial.cylindrical_end.radius + 5 = Acap :=
      congrArg (fun g : StandardInitialMetric => g.cylindrical_end.radius + 5) hinitial
    change g.edist tip z ≤ ENNReal.ofReal (h * (F.standard_initial.cylindrical_end.radius + 5))
      at houter
    rw [hradius] at houter
    simpa only [mul_comm] using houter
  have hscaled : 2 * A / Real.sqrt Q ≤ 2 * A * L * h := by
    have hbound := mul_le_mul_of_nonneg_left hratio (by positivity : 0 ≤ 2 * A)
    simpa only [div_eq_mul_inv, mul_assoc] using hbound
  have hstrict : Acap * h + 2 * A / Real.sqrt Q < Acapture * h := by
    dsimp only [Acapture]
    nlinarith only [hscaled, hh]
  change g.edist tip y < ENNReal.ofReal (Acapture * h)
  calc
    _ ≤ g.edist tip z + g.edist z y := Manifold.riemannianEDist_triangle
    _ ≤ ENNReal.ofReal (Acap * h) + ENNReal.ofReal (2 * A / Real.sqrt Q) := add_le_add htip hzy
    _ = ENNReal.ofReal (Acap * h + 2 * A / Real.sqrt Q) :=
      (ENNReal.ofReal_add (by positivity) (by positivity)).symm
    _ < _ := (ENNReal.ofReal_lt_ofReal_iff (by positivity : 0 < Acapture * h)).mpr hstrict

theorem exists_zero_age_search_cap_capture_cutoff
    (S : RepairedControlledSchedulesData.{u}) {A : ℝ} (hA : 0 ≤ A) :
    ∃ Q0 Acapture delta : ℝ, 0 < Q0 ∧
      S.standard_initial.cylindrical_end.radius + 5 < Acapture ∧ 0 < delta ∧
      ∀ (F : SurgeryFlowData.{u}), F.standard_initial = S.standard_initial →
        F.local_constants = S.constants →
        F.parameters.epsilon = S.setup.epsilon → F.parameters.C = S.setup.C →
      ∀ (W : M33RegularHistoryWindow F) (H : M33RegularHistoryData W) {base Q r : ℝ}
        (ht : base ∈ H.generalized.interval), 0 < base → 0 < Q →
        SurgeryFlowPinched F → SurgeryCanonicalOn F (Ico 0 base) r → r⁻¹ ^ 2 ≤ Q →
      ∀ x : (H.generalized.slice base).carrier, H.generalized.scalar ⟨base, x⟩ = Q → Q0 ≤ Q →
      ∀ (hT : base ∈ F.surgery_times), ∀ [Nonempty (F.slice base).carrier],
        F.parameters.delta base ≤ delta →
      ∀ (i : Fin (F.event base hT).cap_count) (y : (F.slice base).carrier),
        y ∈ (F.metric base).ball (H.history.forward base ht x) (A / Real.sqrt Q) →
        y ∈ ((F.event base hT).caps i).carrier →
        ∃ j : Fin (F.event base hT).cap_count,
          (F.metric base).ball (H.history.forward base ht x) (A / Real.sqrt Q) ⊆
            (F.metric base).ball ((F.event base hT).caps j).tip
              (Acapture * F.parameters.h base) := by
  have hepsilon : S.setup.epsilon ≤ S.calibration.epsilon₁₀ :=
    S.calibration.epsilon_source_le.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  obtain ⟨Q0, D, hQ0, hD, hcontact⟩ := exists_zero_age_cap_contact_scalar_bound S
    S.setup.epsilon_pos hepsilon S.setup.C_pos hA
  obtain ⟨c, delta, hc, hdelta, hfloor⟩ :=
    exists_inserted_cap_birth_scalar_floor_cutoff S.cap_persistence S.constants
  obtain ⟨Acapture, hAcapture, hcapture⟩ :=
    exists_birth_cap_capture_radius S.standard_initial hA hc hD
  refine ⟨Q0, Acapture, delta, hQ0, hAcapture, hdelta, ?_⟩
  intro F hinitial hconstants he hC W H base Q r ht hbase hQ hpinch hpast hthreshold
    x hscale hlarge hT hn hsmall i y hy hycap
  obtain ⟨j, z, hz, hzcap, hzscalar⟩ := hcontact F W H ht hbase hQ he hC hpinch
    hpast hthreshold x hscale hlarge hT i y hy hycap
  exact ⟨j, hcapture F hinitial hT hQ _ j z hz hzcap
    (hfloor F hinitial hconstants base hT hsmall j z hzcap) hzscalar⟩

end PoincareConjecture.M47
