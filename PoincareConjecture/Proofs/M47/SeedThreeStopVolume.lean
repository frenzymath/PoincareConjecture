import PoincareConjecture.Proofs.M47.SeedThreeStopAncestors
import PoincareConjecture.Proofs.M47.SeedSearchVolumeTransfer
import PoincareConjecture.Proofs.M47.SeedRetainedSearch
import PoincareConjecture.Proofs.M47.SeedOldNoncollapse
import PoincareConjecture.Proofs.M47.SeedInitialVolume
import PoincareConjecture.Proofs.M47.SeedBirthCapVolume
import PoincareConjecture.Proofs.M47.OldCapInnerVolume









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.Proofs.M47



theorem exists_three_stop_birth_volume
    (P : M47Predecessors.{u}) (S : RepairedControlledSchedulesData.{u})
    (p : SurgeryParameterPrefix S.constants) (compatible : S.SeedCompatible p)
    {H B d r : ℝ} (hH : 0 < H)
    (hlevel : (p.r (Fin.last p.i))⁻¹ ^ 2 ≤ H)
    (hB : M46.seedAnalyticConstant S ≤ B) (hd : 0 < d) (hr : 0 < r)
    (hscalarTime : 64 * B * H * d ≤ 1)
    (hmetricTime : 6 * (13 * max (4 * H) (Real.exp 4)) * d ≤ 1 / 2)
    (hrOne : r ≤ 1) (hrEpsilon : r ≤ p.setup.epsilon)
    (hrTime : (r / 4) ^ 2 ≤ d / 2)
    (hrCurv : 13 * max (4 * H) (Real.exp 4) ≤ (r / 4)⁻¹ ^ 2)
    (hrScalar : 2 * H * r ^ 2 ≤ 1)
    (hrTube : 3 * r ≤ (Real.sqrt (4 * H))⁻¹ / (8 * B)) :
    ∃ k : ℝ, 0 < k ∧ ∀ (F : SurgeryFlowData.{u}) (O : SurgeryObservation F),
      SurgeryPrefixControls p F O → SurgeryFlowPinched F →
      SurgeryFlowTerminalPolicyOn F (surgeryObservationInterval O) →
      ∀ origin ∈ surgeryObservationInterval O ∩ prefixFinalInterval p,
        ∀ q : (F.slice origin).carrier,
          (∀ y ∈ (F.metric origin).ball q (2 * r),
            (F.connection origin).scalarCurvature y ≤ 2 * H) →
          (∀ y ∈ connectedComponent q, ∀ v : TangentSpace (𝓡 3) y,
            0 ≤ (F.connection origin).ricci y v v) →
          (¬ SurgeryPositiveComponentAt F origin q ∨
            ∃ hT : origin ∈ F.surgery_times,
              ∀ [Nonempty (F.slice origin).carrier],
                ∃ i : Fin (F.event origin hT).cap_count,
                  (connectedComponent q ∩ ((F.event origin hT).caps i).carrier).Nonempty) →
          ENNReal.ofReal (k * (r / 2) ^ 3) ≤
            calibratedMetricVolume (F.metric origin) ((F.metric origin).ball q (r / 2)) := by
  have hlevel4 : (p.r (Fin.last p.i))⁻¹ ^ 2 ≤ 4 * H := by linarith
  obtain ⟨kcap, hkcap, hcapVolume⟩ :=
    exists_old_cap_inner_volume P S p compatible hlevel4 hr hB hrTube
  let kinit := euclideanUnitBallLebesgueVolume.toReal / 2
  let kbirth := birthCapSeedDensity p.setup.standard_initial
  let k := min kbirth (min (kcap / 64) (min (kinit / 64) (p.kappa (Fin.last p.i) / 64)))
  have hkinit : 0 < kinit := initial_seed_density_pos
  have hkbirth : 0 < kbirth := birthCapSeedDensity_pos _
  have hk : 0 < k := lt_min hkbirth (lt_min (by positivity) (lt_min (by positivity)
    (div_pos (p.kappa_pos _) (by norm_num))))
  have hkBirth : k ≤ kbirth := min_le_left _ _
  have hkCap : k ≤ kcap / 64 := (min_le_right _ _).trans (min_le_left _ _)
  have hkInit : k ≤ kinit / 64 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hkOld : k ≤ p.kappa (Fin.last p.i) / 64 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨k, hk, ?_⟩
  intro F O old hpinch hpolicy origin horigin q hscalar hRic hbirth
  let : CompactSpace (F.slice origin).carrier :=
    isCompact_univ_iff.mp (F.slices_compact origin (O.interval_subset horigin.1))
  have hrHalf : 0 < r / 2 := by positivity
  have hrQuarter : 0 < r / 4 := by positivity
  have hqBall : q ∈ (F.metric origin).ball q r := by
    change (F.metric origin).edist q q < ENNReal.ofReal r
    rw [M36.metric_edist_self]
    exact ENNReal.ofReal_pos.mpr hr
  have hcompact : IsCompact (closure ((F.metric origin).ball q (r / 2))) :=
    isClosed_closure.isCompact
  have hbuffer : closure ((F.metric origin).ball q (r / 2)) ⊆ (F.metric origin).ball q r :=
    M04.initial_half_ball_closure_subset_initial_ball (F.metric origin) q hr
  have htime0 : 0 ≤ origin := horigin.1.1
  by_cases hzero : origin = 0
  · subst origin
    have hki : k ≤ kinit := hkInit.trans (by linarith)
    exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hki
      (pow_nonneg hrHalf.le 3))).trans
        (seed_initial_ball_volume F q hrHalf (by linarith))
  have horiginPos : 0 < origin := lt_of_le_of_ne htime0 (Ne.symm hzero)
  let a := max (-origin) (-d)
  have ha : a < 0 := max_lt (neg_neg_of_pos horiginPos) (neg_neg_of_pos hd)
  have haOrigin : -origin ≤ a := le_max_left _ _
  have haDuration : -d ≤ a := le_max_right _ _
  have hJ : Icc (origin + a) origin ⊆ F.time_domain := by
    intro t ht
    apply O.interval_subset
    exact ⟨by linarith [ht.1], ht.2.trans_lt horigin.1.2⟩
  let U := (F.metric origin).ball q r
  have hU : IsOpen U := isOpen_Iio.preimage ((M36.metric_edist_continuous
    (F.metric origin)).comp (continuous_const.prodMk continuous_id))
  obtain ⟨c, hc, e, hbase, hstop⟩ := exists_open_region_seed_search F ha.le hJ U hU ⟨q, hqBall⟩
  let K := 13 * max (4 * H) (Real.exp 4)
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hBpos : 0 < B := (M46.seedAnalyticConstant_pos S).trans_le hB
  have hshort : 64 * B * H * (-c) ≤ 1 :=
    (mul_le_mul_of_nonneg_left (by linarith [hc.1]) (by positivity)).trans hscalarTime
  have hmetricShort : 6 * K * (-c) ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_left (by linarith [hc.1]) (by positivity)).trans hmetricTime
  have hbounds := seed_search_bounds_of_birth P S p compatible old hpinch hpolicy e hc.2
    (by linarith [hc.1]) horigin hH hlevel hB hbase q
    (M46.metric_ball_subset_connectedComponent (F.metric origin) q r) hbirth
    (fun x hx => hscalar x (hx.trans_le (ENNReal.ofReal_le_ofReal (by linarith)))) hshort
  have hRm : ∀ s (hs : s ∈ Icc c 0), ∀ x ∈ U,
      (F.connection (origin + s / 1)).curvatureTensorNorm (e.forward s hs x) ≤ K :=
    fun s hs x hx => (hbounds s hs x hx).2
  have hOldTime (s : ℝ) (hs : s ∈ Icc c 0) :
      origin + s / 1 ∈ surgeryObservationInterval O ∩ prefixFinalInterval p := by
    change (0 ≤ origin + s / 1 ∧ origin + s / 1 < O.H) ∧
      (0 ≤ origin + s / 1 ∧ origin + s / 1 < surgeryEpochStart p.i)
    simp only [div_one]
    constructor
    · exact ⟨by linarith [hc.1, hs.1], by linarith [horigin.1.2, hs.2]⟩
    · exact ⟨by linarith [hc.1, hs.1], by linarith [horigin.2.2, hs.2]⟩
  have htransfer (s : ℝ) (hs : s ∈ Icc c 0) (v : ℝ) (hkv : k ≤ v / 64)
      (hv : ENNReal.ofReal (v * (r / 4) ^ 3) ≤
        calibratedMetricVolume (F.metric (origin + s / 1))
          ((F.metric (origin + s / 1)).ball (e.forward s hs q) (r / 4))) :
      ENNReal.ofReal (k * (r / 2) ^ 3) ≤
        calibratedMetricVolume (F.metric origin) ((F.metric origin).ball q (r / 2)) := by
    apply (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hkv (pow_nonneg hrHalf.le 3))).trans
    apply seed_search_volume_density_transfer P hpinch e hU hK hbase hRm hmetricShort
      q hrHalf hcompact hbuffer s hs
    simpa only [div_div, show (2 : ℝ) * 2 = 4 by norm_num] using hv
  rcases hstop with hplanned | ⟨hT, hcap⟩
  · subst c
    by_cases hshortBirth : origin ≤ d
    · have haEq : a = -origin := max_eq_left (by linarith)
      have ht : origin + a / 1 = 0 := by rw [haEq]; simp
      apply htransfer a ⟨le_rfl, ha.le⟩ kinit hkInit
      have initial (t : ℝ) (ht : t = 0) (x : (F.slice t).carrier) :
          ENNReal.ofReal (kinit * (r / 4) ^ 3) ≤
            calibratedMetricVolume (F.metric t) ((F.metric t).ball x (r / 4)) := by
        subst t
        exact seed_initial_ball_volume F x hrQuarter (by linarith)
      exact initial _ ht _
    · have haEq : a = -d := max_eq_right (by linarith)
      have hs : a / 2 ∈ Icc a 0 := ⟨by linarith, by linarith⟩
      apply htransfer (a / 2) hs (p.kappa (Fin.last p.i)) hkOld
      apply seed_search_old_noncollapsed P old hpinch e hU hK hbase hRm hmetricShort
        q hrHalf hrQuarter hcompact hbuffer hs ?_ ?_ ?_ hrCurv (hOldTime _ hs)
      · exact seed_search_before_birth_nonpositive P hpolicy e ha.le horigin.1 hbase q
          (M46.metric_ball_subset_connectedComponent (F.metric origin) q r) hbirth
          (a / 2) hs (by linarith) q hqBall
      · rw [haEq]
        linarith
      · linarith
      · linarith
  · let : Nonempty (F.slice (origin + c / 1)).carrier := ⟨e.forward c ⟨le_rfl, hc.2⟩ q⟩
    obtain ⟨i, z, ⟨x, hx, hxz⟩, hz⟩ := hcap
    by_cases hcZero : c = 0
    · subst c
      have birthAt (t : ℝ) (ht : t = origin)
          (f : (F.slice origin).carrier → (F.slice t).carrier)
          (hf : ∀ y ∈ U, HEq (f y) y) (hT : t ∈ F.surgery_times)
          [Nonempty (F.slice t).carrier] (i : Fin (F.event t hT).cap_count)
          (x : (F.slice origin).carrier) (hx : x ∈ U)
          (hz : f x ∈ ((F.event t hT).caps i).carrier) :
          ENNReal.ofReal (k * (r / 2) ^ 3) ≤
            calibratedMetricVolume (F.metric origin) ((F.metric origin).ball q (r / 2)) := by
        subst t
        rw [eq_of_heq (hf x hx)] at hz
        have hvol := seed_birth_cap_volume (F.event origin hT) (F.connection origin)
          i q x hr (by positivity : 0 < 2 * H) hrScalar hz hx hscalar hRic hrHalf (by linarith)
        rw [old.standard_initial_eq] at hvol
        exact (ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_right hkBirth (pow_nonneg hrHalf.le 3))).trans hvol
      apply birthAt (origin + 0 / 1) (by simp) (e.forward 0 ⟨le_rfl, hc.2⟩)
        (hbase _) hT i x hx
      rwa [hxz]
    · have hcNeg : c < 0 := lt_of_le_of_ne hc.2 hcZero
      have hs : c ∈ Icc c 0 := ⟨le_rfl, hc.2⟩
      apply htransfer c hs kcap hkCap
      apply hcapVolume F O old _ (hOldTime c hs) hT i (e.forward c hs q) z hz
      · exact seed_search_before_birth_nonpositive P hpolicy e hc.2 horigin.1 hbase q
          (M46.metric_ball_subset_connectedComponent (F.metric origin) q r) hbirth
          c hs hcNeg q hqBall
      · exact (hbounds c hs q hqBall).1
      · rw [← hxz]
        exact (hbounds c hs x hx).1
      · let chart := M44.cylinderSliceChart e hU c hs
        have hcomparison := seed_search_metric_comparison P hpinch e hU hK hbase hRm
          hmetricShort c hs
        have hupper : ∀ y ∈ chart.source, ∀ v : TangentSpace (𝓡 3) y,
            (F.metric (origin + c / 1)).inner (chart y)
              (mfderiv (𝓡 3) (𝓡 3) chart y v) (mfderiv (𝓡 3) (𝓡 3) chart y v) ≤
                4 * (F.metric origin).inner y v v := by
          intro y hy v
          have hnonnegative : 0 ≤ (F.metric origin).inner y v v := by
            by_cases hv : v = 0
            · simp [hv]
            · exact ((F.metric origin).pos y v hv).le
          have h := (hcomparison y hy v).2
          change (F.metric (origin + c / 1)).inner (e.forward c hs y)
            (mfderiv (𝓡 3) (𝓡 3) (e.forward c hs) y v)
            (mfderiv (𝓡 3) (𝓡 3) (e.forward c hs) y v) ≤
              4 * (F.metric origin).inner y v v
          nlinarith
        exact seed_image_ball_subset (F.metric origin) (F.metric (origin + c / 1))
          chart hupper q (Subset.refl U) ⟨x, hx, hxz⟩
      · exact hrQuarter
      · linarith

end PoincareConjecture.Proofs.M47
