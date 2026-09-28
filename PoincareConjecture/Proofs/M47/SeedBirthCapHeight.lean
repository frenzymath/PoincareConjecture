import PoincareConjecture.Proofs.M47.EventSeedGeometry









set_option autoImplicit false

open Set
open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareConjecture.Proofs.M47

variable {g0 : StandardInitialMetric} {K : MetricSurgeryConstants}
  {P : SurgeryParameters} {slice : ℝ → GeneralizedSliceCarrier.{u}}
  {metric : ∀ t, RiemannianMetric 3 (slice t).carrier} {T : ℝ}




theorem seed_birth_cap_height
    (E : SurgeryEventData g0 K P slice metric T) (D : LeviCivitaData (metric T))
    (i : Fin E.cap_count) (q z : (slice T).carrier) {r H : ℝ}
    (hr : 0 < r) (hH : 0 < H) (hbudget : H * r ^ 2 ≤ 1)
    (hz : z ∈ (E.caps i).carrier) (hclose : (metric T).edist q z < ENNReal.ofReal r)
    (hscalar : ∀ y ∈ (metric T).ball q (2 * r), D.scalarCurvature y ≤ H) :
    r / (4 * (g0.cylindrical_end.radius + 5) + 2) ≤ (E.necks i).neck.scale := by
  let d := g0.cylindrical_end.radius + 5
  let B := 4 * d + 2
  let h := (E.necks i).neck.scale
  let c := E.local_embed i ((E.local_result i).collapse (E.necks i).neck.center)
  have hd : 0 < d := by dsimp only [d]; linarith [g0.cylindrical_end.radius_pos]
  have hB : 1 < B := by dsimp only [B]; linarith
  have hh : 0 < h := (E.necks i).neck.scale_pos
  by_contra hsmall
  have hsmall' : h < r / B := lt_of_not_ge hsmall
  have hmul : h * B < r := (lt_div_iff₀ (zero_lt_one.trans hB)).mp hsmall'
  have hshort : r + 2 * h * d < 2 * r := by dsimp only [B] at hmul; nlinarith
  have hdist : (metric T).edist z c ≤ ENNReal.ofReal (2 * h * d) :=
    event_cap_contact_distance E i hz
  have hcenter : c ∈ (metric T).ball q (2 * r) := by
    calc
      (metric T).edist q c ≤ (metric T).edist q z + (metric T).edist z c :=
        M36.metric_edist_triangle (metric T) q z c
      _ ≤ ENNReal.ofReal r + ENNReal.ofReal (2 * h * d) := add_le_add hclose.le hdist
      _ = ENNReal.ofReal (r + 2 * h * d) :=
        (ENNReal.ofReal_add hr.le (by positivity)).symm
      _ < ENNReal.ofReal (2 * r) := ENNReal.ofReal_lt_ofReal_iff (by positivity) |>.mpr hshort
  have hceiling : h⁻¹ ^ 2 ≤ H := by
    have h := hscalar c hcenter
    rwa [event_retained_center_scalar E D i] at h
  have hunit : 1 ≤ H * h ^ 2 := by
    have hproduct := mul_le_mul_of_nonneg_right hceiling (sq_nonneg h)
    have hcancel : h⁻¹ ^ 2 * h ^ 2 = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ hh.ne', one_pow]
    rwa [hcancel] at hproduct
  have hhr : h < r := by nlinarith
  have hsquare : h ^ 2 < r ^ 2 := (sq_lt_sq₀ hh.le hr.le).mpr hhr
  have hcontradiction := (mul_lt_mul_of_pos_left hsquare hH).trans_le hbudget
  exact not_lt_of_ge hunit hcontradiction

end PoincareConjecture.Proofs.M47
