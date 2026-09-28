import PoincareConjecture.Proofs.M47.CanonicalNeckCapCapture
import PoincareConjecture.Proofs.M47.BlowupControlsCapClock

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.M47

theorem exists_source_bottom_cap_capture_radius
    (g0 : StandardInitialMetric) {D K c : ℝ} (hD : 0 ≤ D) (hK : 0 < K) (hc : 0 < c) :
    ∃ Rcap : ℝ, g0.cylindrical_end.radius + 5 < Rcap ∧
      ∀ (F : SurgeryFlowData.{u}), F.standard_initial = g0 →
      ∀ (C : GeneralizedSliceCarrier.{u}) {base Q a : ℝ} {U : Set C.carrier}
        (ha : a < 0) (E : SurgeryFlowCylinder F C base Q (Icc a 0) U),
      let bottom : a ∈ Icc a 0 := ⟨le_rfl, ha.le⟩
      let birth := base + a / Q
      ∀ (hT : birth ∈ F.surgery_times), ∀ [Nonempty (F.slice birth).carrier],
      ∀ (i : Fin (F.event birth hT).cap_count) (contact : C.carrier),
        E.forward a bottom contact ∈ ((F.event birth hT).caps i).carrier →
        c / (2 * (F.parameters.h birth) ^ 2) ≤
          (F.connection birth).scalarCurvature (E.forward a bottom contact) →
        (F.connection birth).scalarCurvature (E.forward a bottom contact) ≤ K * Q →
        (∀ x ∈ U, (F.metric birth).edist (E.forward a bottom contact)
            (E.forward a bottom x) ≤ ENNReal.ofReal (D / Real.sqrt Q)) →
        ∀ x ∈ U, E.forward a bottom x ∈
          (F.metric birth).ball ((F.event birth hT).caps i).tip
            (Rcap * F.parameters.h birth) := by
  let L := 1 + 2 * K / c
  let Acap := g0.cylindrical_end.radius + 5
  let Rcap := Acap + D * L + 1
  have hL : 0 < L := by dsimp only [L]; positivity
  have hAcap : 0 < Acap := by
    dsimp only [Acap]
    linarith [g0.cylindrical_end.radius_pos]
  refine ⟨Rcap, by dsimp only [Rcap, Acap]; nlinarith only [mul_nonneg hD hL.le], ?_⟩
  intro F hstandard C base Q a U ha E
  dsimp only
  intro hT hn i contact hcap hfloor hceiling hdistance x hx
  let birth := base + a / Q
  let h := F.parameters.h birth
  let g := F.metric birth
  let bottom : a ∈ Icc a 0 := ⟨le_rfl, ha.le⟩
  let z := E.forward a bottom contact
  let w := E.forward a bottom x
  let tip := ((F.event birth hT).caps i).tip
  have hQ := E.scale_pos
  have hh : 0 < h :=
    F.parameters.h_pos birth (F.time_domain_nonnegative (F.surgery_times_subset hT))
  have hl : 0 < (Real.sqrt Q)⁻¹ := inv_pos.mpr (Real.sqrt_pos.mpr hQ)
  have hscale : (((Real.sqrt Q)⁻¹)⁻¹) ^ 2 = Q := by
    rw [inv_inv, Real.sq_sqrt hQ.le]
  have hratio : (Real.sqrt Q)⁻¹ ≤ L * h :=
    Proofs.M47.neck_scale_le_cap_height_of_scalar hc hK hl hh hfloor
      (by simpa only [hscale] using hceiling)
  have htip : g.edist tip z ≤ ENNReal.ofReal (Acap * h) := by
    have houter := ((F.event birth hT).caps i).outer_ball hcap
    have hAcapEq : F.standard_initial.cylindrical_end.radius + 5 = Acap :=
      congrArg (fun g0 : StandardInitialMetric => g0.cylindrical_end.radius + 5) hstandard
    change g.edist tip z ≤
      ENNReal.ofReal (h * (F.standard_initial.cylindrical_end.radius + 5)) at houter
    rw [hAcapEq] at houter
    simpa only [mul_comm] using houter
  have hscaled : D / Real.sqrt Q ≤ (D * L) * h := by
    have hr := mul_le_mul_of_nonneg_left hratio hD
    simpa only [div_eq_mul_inv, mul_assoc] using hr
  have hstrict : Acap * h + D / Real.sqrt Q < Rcap * h := by
    dsimp only [Rcap]
    nlinarith only [hscaled, hh]
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : (F.slice birth).carrier → Type _) :=
    ⟨g.toRiemannianMetric⟩
  change g.edist tip w < ENNReal.ofReal (Rcap * h)
  calc
    _ ≤ g.edist tip z + g.edist z w := Manifold.riemannianEDist_triangle
    _ ≤ ENNReal.ofReal (Acap * h) + ENNReal.ofReal (D / Real.sqrt Q) :=
      add_le_add htip (hdistance x hx)
    _ = ENNReal.ofReal (Acap * h + D / Real.sqrt Q) :=
      (ENNReal.ofReal_add (by positivity) (by positivity)).symm
    _ < _ := (ENNReal.ofReal_lt_ofReal_iff (by positivity : 0 < Rcap * h)).mpr hstrict

end PoincareConjecture.M47
