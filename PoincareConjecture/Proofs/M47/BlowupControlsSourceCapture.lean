import PoincareConjecture.Proofs.M47.BlowupControlsSourceMetric
import PoincareConjecture.Proofs.M47.CanonicalNeckCapCapture

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.M47

theorem exists_search_bottom_cap_capture_radius
    (g0 : StandardInitialMetric) {A K c : ℝ} (hA : 0 ≤ A) (hK : 0 < K) (hc : 0 < c) :
    ∃ Acapture : ℝ, g0.cylindrical_end.radius + 5 < Acapture ∧
      ∀ (F : SurgeryFlowData.{u}), F.standard_initial = g0 →
      ∀ {base Q a : ℝ} (ha : a < 0) (p : (F.slice base).carrier),
      ∀ e : SurgeryFlowCylinder F (F.slice base) base Q (Icc a 0)
        ((F.metric base).ball p (A / Real.sqrt Q)),
      let hbottom : a ∈ Icc a 0 := ⟨le_rfl, ha.le⟩
      let birth := base + a / Q
      ∀ (hT : birth ∈ F.surgery_times), ∀ [Nonempty (F.slice birth).carrier],
      ∀ (i : Fin (F.event birth hT).cap_count) (contact : (F.slice base).carrier),
      contact ∈ (F.metric base).ball p (A / Real.sqrt Q) →
      e.forward a hbottom contact ∈ ((F.event birth hT).caps i).carrier →
      c / (2 * (F.parameters.h birth) ^ 2) ≤
        (F.connection birth).scalarCurvature (e.forward a hbottom contact) →
      (F.connection birth).scalarCurvature (e.forward a hbottom contact) ≤ K * Q →
      (∀ y ∈ (F.metric base).ball p (A / Real.sqrt Q), ∀ v : TangentSpace (𝓡 3) y,
        (F.metric birth).inner (e.forward a hbottom y)
            (mfderiv (𝓡 3) (𝓡 3) (e.forward a hbottom) y v)
            (mfderiv (𝓡 3) (𝓡 3) (e.forward a hbottom) y v) ≤
          2 * (F.metric base).inner y v v) →
      ∀ y ∈ (F.metric base).ball p (A / Real.sqrt Q),
        e.forward a hbottom y ∈
          (F.metric birth).ball ((F.event birth hT).caps i).tip
            (Acapture * F.parameters.h birth) := by
  let L := 1 + 2 * K / c
  let Acap := g0.cylindrical_end.radius + 5
  let Acapture := Acap + 4 * A * L + 1
  have hL : 0 < L := by dsimp only [L]; positivity
  have hAcap : 0 < Acap := by
    dsimp only [Acap]
    linarith [g0.cylindrical_end.radius_pos]
  refine ⟨Acapture, by dsimp only [Acapture, Acap]; nlinarith [mul_nonneg hA hL.le], ?_⟩
  intro F hstandard base Q a ha p e
  dsimp only
  intro hT hn i contact hcontact hcap hfloor hceiling hmetric y hy
  let birth := base + a / Q
  let h := F.parameters.h birth
  let g := F.metric birth
  let bottom : a ∈ Icc a 0 := ⟨le_rfl, ha.le⟩
  let center := e.forward a bottom p
  let z := e.forward a bottom contact
  let w := e.forward a bottom y
  let tip := ((F.event birth hT).caps i).tip
  have hQ := e.scale_pos
  have hh : 0 < h :=
    F.parameters.h_pos birth (F.time_domain_nonnegative (F.surgery_times_subset hT))
  have hl : 0 < (Real.sqrt Q)⁻¹ := inv_pos.mpr (Real.sqrt_pos.mpr hQ)
  have hscale : (((Real.sqrt Q)⁻¹)⁻¹) ^ 2 = Q := by
    rw [inv_inv, Real.sq_sqrt hQ.le]
  have hratio : (Real.sqrt Q)⁻¹ ≤ L * h :=
    Proofs.M47.neck_scale_le_cap_height_of_scalar hc hK hl hh hfloor
      (by simpa only [hscale] using hceiling)
  have himage := normalized_search_image_ball_subset p e a bottom hmetric
  have hdz : g.edist center z ≤ ENNReal.ofReal (2 * (A / Real.sqrt Q)) :=
    (himage (mem_image_of_mem _ hcontact)).le
  have hdw : g.edist center w ≤ ENNReal.ofReal (2 * (A / Real.sqrt Q)) :=
    (himage (mem_image_of_mem _ hy)).le
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : (F.slice birth).carrier → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hsymm : g.edist z center = g.edist center z := Manifold.riemannianEDist_comm
  have hzw : g.edist z w ≤ ENNReal.ofReal (4 * A / Real.sqrt Q) := by
    calc
      _ ≤ g.edist z center + g.edist center w := Manifold.riemannianEDist_triangle
      _ ≤ ENNReal.ofReal (2 * (A / Real.sqrt Q)) +
          ENNReal.ofReal (2 * (A / Real.sqrt Q)) := by
        rw [hsymm]
        exact add_le_add hdz hdw
      _ = ENNReal.ofReal (4 * A / Real.sqrt Q) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring
  have htip : g.edist tip z ≤ ENNReal.ofReal (Acap * h) := by
    have houter := ((F.event birth hT).caps i).outer_ball hcap
    have hAcapEq : F.standard_initial.cylindrical_end.radius + 5 = Acap :=
      congrArg (fun g0 : StandardInitialMetric => g0.cylindrical_end.radius + 5) hstandard
    change g.edist tip z ≤
      ENNReal.ofReal (h * (F.standard_initial.cylindrical_end.radius + 5)) at houter
    rw [hAcapEq] at houter
    simpa only [mul_comm] using houter
  have hscaled : 4 * A / Real.sqrt Q ≤ (4 * A * L) * h := by
    have hr := mul_le_mul_of_nonneg_left hratio (by positivity : 0 ≤ 4 * A)
    simpa only [div_eq_mul_inv, mul_assoc] using hr
  have hstrict : Acap * h + 4 * A / Real.sqrt Q < Acapture * h := by
    dsimp only [Acapture]
    nlinarith only [hscaled, hh]
  change g.edist tip w < ENNReal.ofReal (Acapture * h)
  calc
    _ ≤ g.edist tip z + g.edist z w := Manifold.riemannianEDist_triangle
    _ ≤ ENNReal.ofReal (Acap * h) + ENNReal.ofReal (4 * A / Real.sqrt Q) :=
      add_le_add htip hzw
    _ = ENNReal.ofReal (Acap * h + 4 * A / Real.sqrt Q) :=
      (ENNReal.ofReal_add (by positivity) (by positivity)).symm
    _ < _ := (ENNReal.ofReal_lt_ofReal_iff (by positivity : 0 < Acapture * h)).mpr hstrict

end PoincareConjecture.M47
