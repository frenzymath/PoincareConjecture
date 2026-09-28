import PoincareConjecture.Proofs.M47.SeedCapPersistenceDensity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.Proofs.M47

theorem seed_cap_contact_radius {c K h H r R : ℝ}
    (hc : 0 < c) (hK : 0 < K) (hh : 0 < h) (hr : 0 < r)
    (hfloor : c / (2 * h ^ 2) ≤ R) (hceiling : R ≤ 4 * H)
    (hbudget : H * r ^ 2 ≤ K) : r ≤ (1 + 8 * K / c) * h := by
  have hcross : c ≤ 8 * H * h ^ 2 := by
    have hb := (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2)
      (sq_pos_of_pos hh))).mp (hfloor.trans hceiling)
    nlinarith only [hb]
  have hcr : c * r ^ 2 ≤ 8 * K * h ^ 2 := by
    calc
      _ ≤ (8 * H * h ^ 2) * r ^ 2 :=
        mul_le_mul_of_nonneg_right hcross (sq_nonneg r)
      _ = (H * r ^ 2) * (8 * h ^ 2) := by ring
      _ ≤ K * (8 * h ^ 2) :=
        mul_le_mul_of_nonneg_right hbudget (by positivity)
      _ = _ := by ring
  have hr2 : r ^ 2 ≤ (8 * K / c) * h ^ 2 := by
    apply (mul_le_mul_iff_left₀ hc).mp
    calc
      r ^ 2 * c = c * r ^ 2 := mul_comm _ _
      _ ≤ 8 * K * h ^ 2 := hcr
      _ = ((8 * K / c) * h ^ 2) * c := by field_simp
  have hratio : 0 < 8 * K / c := by positivity
  have hsquare : 8 * K / c ≤ (1 + 8 * K / c) ^ 2 := by
    nlinarith [sq_nonneg (8 * K / c)]
  have hfinal : r ^ 2 ≤ ((1 + 8 * K / c) * h) ^ 2 := by
    rw [mul_pow]
    exact hr2.trans (mul_le_mul_of_nonneg_right hsquare (sq_nonneg h))
  nlinarith [mul_pos (show 0 < 1 + 8 * K / c by linarith) hh]

theorem exists_seed_cap_contact_small_density (g0 : StandardInitialMetric)
    {c K : ℝ} (hc : 0 < c) (hK : 0 < K) :
    ∃ A k : ℝ, g0.cylindrical_end.radius + 5 < A ∧ 0 < k ∧
      ∀ (F : SurgeryFlowData.{u}), F.standard_initial = g0 →
      ∀ (O : SurgeryObservation F) (t : ℝ) (hT : t ∈ F.surgery_times)
        (_hn : Nonempty (F.slice t).carrier) (i : Fin (F.event t hT).cap_count)
        (eta theta : ℝ),
        0 < eta → eta ≤ 1 / 2 → 0 < theta → t < O.H →
        SurgeryCapPersistenceAlternative F O t hT i A eta theta →
      ∀ (H r : ℝ), 0 < r → H * r ^ 2 ≤ K →
      ∀ z ∈ ((F.event t hT).caps i).carrier,
        c / (2 * (F.parameters.h t) ^ 2) ≤ (F.connection t).scalarCurvature z →
        (F.connection t).scalarCurvature z ≤ 4 * H →
      ∀ q : (F.slice t).carrier,
        (F.metric t).edist z q ≤ ENNReal.ofReal (2 * r) →
        ∀ s : ℝ, 0 < s → s ≤ r →
          ENNReal.ofReal (k * s ^ 3) ≤
            calibratedMetricVolume (F.metric t) ((F.metric t).ball q s) := by
  let Rmax := 1 + 8 * K / c
  let Acap := g0.cylindrical_end.radius + 5
  let Rtip := Acap + 2 * Rmax + 1
  let A := 2 * Rtip + Rmax + 1
  have hmax : 0 < Rmax := by dsimp only [Rmax]; positivity
  have hcap : 0 < Acap := by
    dsimp only [Acap]
    linarith [g0.cylindrical_end.radius_pos]
  have htip : 0 < Rtip := by dsimp only [Rtip]; positivity
  have hA : 2 * Rtip + Rmax ≤ A := by dsimp only [A]; linarith
  have hAcap : Acap < A := by dsimp only [A, Rtip]; linarith
  obtain ⟨k, hk, hdensity⟩ := exists_seed_cap_persistence_density g0 htip hmax
  refine ⟨A, k, hAcap, hk, ?_⟩
  intro F hinitial O t hT hn i eta theta heta hetaHalf htheta htH hpersist
    H r hr hbudget z hz hfloor hceiling q hdist s hs hsr
  let h := F.parameters.h t
  have hh : 0 < h :=
    F.parameters.h_pos t (F.time_domain_nonnegative (F.surgery_times_subset hT))
  have hrmax : r ≤ Rmax * h := seed_cap_contact_radius hc hK hh hr hfloor hceiling hbudget
  let g := F.metric t
  let tip := ((F.event t hT).caps i).tip
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : (F.slice t).carrier → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have houter : g.edist tip z ≤ ENNReal.ofReal (Acap * h) := by
    have ho := ((F.event t hT).caps i).outer_ball hz
    change (F.metric t).edist ((F.event t hT).caps i).tip z ≤
      ENNReal.ofReal (F.parameters.h t * (F.standard_initial.cylindrical_end.radius + 5))
      at ho
    have hradius : F.standard_initial.cylindrical_end.radius + 5 = Acap :=
      congrArg (fun g0 : StandardInitialMetric => g0.cylindrical_end.radius + 5) hinitial
    rw [hradius] at ho
    simpa only [g, tip, h, mul_comm] using ho
  have hnear : q ∈ g.ball tip (Rtip * h) := by
    change g.edist tip q < ENNReal.ofReal (Rtip * h)
    have hstrict : Acap * h + 2 * r < Rtip * h := by
      dsimp only [Rtip]
      nlinarith only [hrmax, hh]
    calc
      _ ≤ g.edist tip z + g.edist z q := Manifold.riemannianEDist_triangle
      _ ≤ ENNReal.ofReal (Acap * h) + ENNReal.ofReal (2 * r) :=
        add_le_add houter hdist
      _ = ENNReal.ofReal (Acap * h + 2 * r) :=
        (ENNReal.ofReal_add (by positivity) (by positivity)).symm
      _ < _ := (ENNReal.ofReal_lt_ofReal_iff (mul_pos htip hh)).mpr hstrict
  exact hdensity F hinitial O t hT hn i A eta theta hA heta hetaHalf htheta htH
    hpersist q hnear s hs (hsr.trans hrmax)

theorem exists_seed_cap_contact_density (g0 : StandardInitialMetric)
    {c K : ℝ} (hc : 0 < c) (hK : 0 < K) :
    ∃ A k : ℝ, g0.cylindrical_end.radius + 5 < A ∧ 0 < k ∧
      ∀ (F : SurgeryFlowData.{u}), F.standard_initial = g0 →
      ∀ (O : SurgeryObservation F) (t : ℝ) (hT : t ∈ F.surgery_times)
        (_hn : Nonempty (F.slice t).carrier) (i : Fin (F.event t hT).cap_count)
        (eta theta : ℝ),
        0 < eta → eta ≤ 1 / 2 → 0 < theta → t < O.H →
        SurgeryCapPersistenceAlternative F O t hT i A eta theta →
      ∀ (H r : ℝ), 0 < r → H * r ^ 2 ≤ K →
      ∀ z ∈ ((F.event t hT).caps i).carrier,
        c / (2 * (F.parameters.h t) ^ 2) ≤ (F.connection t).scalarCurvature z →
        (F.connection t).scalarCurvature z ≤ 4 * H →
      ∀ q : (F.slice t).carrier,
        (F.metric t).edist z q ≤ ENNReal.ofReal (2 * r) →
          ENNReal.ofReal (k * r ^ 3) ≤
            calibratedMetricVolume (F.metric t) ((F.metric t).ball q r) := by
  obtain ⟨A, k, hA, hk, hsmall⟩ := exists_seed_cap_contact_small_density g0 hc hK
  refine ⟨A, k, hA, hk, ?_⟩
  intro F hinitial O t hT hn i eta theta heta hetaHalf htheta htH hpersist
    H r hr hbudget z hz hfloor hceiling q hdist
  exact hsmall F hinitial O t hT hn i eta theta heta hetaHalf htheta htH hpersist
    H r hr hbudget z hz hfloor hceiling q hdist r hr le_rfl

end PoincareConjecture.Proofs.M47
