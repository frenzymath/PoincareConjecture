import PoincareConjecture.Proofs.M47.SeedPastCapDensity
import PoincareConjecture.Proofs.M47.SeedObservedSearchBounds
import PoincareConjecture.Proofs.M47.SeedNearAncestor
import PoincareConjecture.Proofs.M47.SeedRetainedSearch
import PoincareConjecture.Proofs.M47.SeedSearchVolumeTransfer
import PoincareConjecture.Proofs.M46.Sec16_3_Assembly.Prop16_1_Prefix










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.Proofs.M47

open M46



theorem exists_seed_past_search_volume
    (P : M47Predecessors.{u}) (S : RepairedControlledSchedulesData.{u})
    (p : SurgeryParameterPrefix S.constants) (hp : S.SeedCompatible p) :
    ∃ k : ℝ, 0 < k ∧ ∀ rNext : ℝ, 0 < rNext → rNext ≤ p.r (Fin.last p.i) →
      ∃ cutoff : ℝ, 0 < cutoff ∧ cutoff ≤ p.Delta (Fin.last p.i) ∧
        ∀ H B d r : ℝ, 0 < H → seedAnalyticConstant S ≤ B → 0 < d → 0 < r →
          (p.r (Fin.last p.i))⁻¹ ^ 2 ≤ H → (Real.sqrt H)⁻¹ ≤ 1 / 200 →
          64 * B * H * d ≤ 1 → 312 * H * d ≤ 1 / 2 →
          r ≤ p.setup.epsilon → H * r ^ 2 ≤ 1 → r ^ 2 ≤ d →
          52 * H ≤ (r / 2)⁻¹ ^ 2 →
        ∀ (F : SurgeryFlowData.{u}) (O : SurgeryObservation F),
          O.H ≤ surgeryEpochStart (p.i + 1) →
          SurgeryPrefixControls p F O → SurgeryFlowAdmissible F → SurgeryFlowPinched F →
          SurgeryFlowTerminalPolicyOn F (surgeryObservationInterval O) →
          SurgeryPostPrefixScales p F O rNext cutoff →
          SurgeryCanonicalOn F (surgeryObservationInterval O) rNext →
          (∀ t ∈ surgeryObservationInterval O ∩ overlapInterval p,
            F.parameters.delta t ≤ cutoff) →
          ∀ origin : ℝ, origin < surgeryEpochStart p.i →
            Icc (origin - d) origin ⊆
              surgeryObservationInterval O ∩ Ici (surgeryEpochStart (p.i - 1)) →
          ∀ q : (F.slice origin).carrier,
            (∀ y ∈ (F.metric origin).ball q r,
              (F.connection origin).scalarCurvature y ≤ 2 * H) →
            (¬ SurgeryPositiveComponentAt F origin q ∨
              ∃ hT : origin ∈ F.surgery_times,
                ∀ [Nonempty (F.slice origin).carrier],
                  ∃ i : Fin (F.event origin hT).cap_count,
                    (connectedComponent q ∩ ((F.event origin hT).caps i).carrier).Nonempty) →
            ENNReal.ofReal (k * (r / 2) ^ 3) ≤
              calibratedMetricVolume (F.metric origin) ((F.metric origin).ball q (r / 2)) := by
  classical
  obtain ⟨kcap, hkcap, capDensity⟩ := exists_seed_past_cap_contact_density S p hp
  let k := min (p.kappa (Fin.last p.i) / 512) (kcap / 64)
  have hk : 0 < k := lt_min (div_pos (p.kappa_pos _) (by norm_num))
    (div_pos hkcap (by norm_num))
  refine ⟨k, hk, ?_⟩
  intro rNext hrNext hrLast
  obtain ⟨cutoff, hcutoff, hlast, hcapDensity⟩ := capDensity rNext hrNext hrLast
  refine ⟨cutoff, hcutoff, hlast, ?_⟩
  intro H B d r hH hB hd hr hlevel hsmall hscalarTime hmetricTime hrEpsilon
    hbudget hrd htest F O hHorizon old admissible pinched policy scales canonical overlap
    origin hOldOrigin hwindow q hscalar hbirth
  have hnoncollapse := prefix_noncollapsed old (le_refl (p.kappa (Fin.last p.i)))
  have horigin := (hwindow (show origin ∈ Icc (origin - d) origin from
    ⟨by linarith only [hd], le_rfl⟩)).1
  let U := (F.metric origin).ball q r
  have hU : IsOpen U := isOpen_Iio.preimage
    ((M36.metric_edist_continuous (F.metric origin)).comp
      (continuous_const.prodMk continuous_id))
  have hqU : q ∈ U := by
    change (F.metric origin).edist q q < ENNReal.ofReal r
    rw [M36.metric_edist_self]
    exact ENNReal.ofReal_pos.mpr hr
  have hJ : Icc (origin + -d) origin ⊆ F.time_domain := by
    intro t ht
    exact O.interval_subset (hwindow (by simpa only [sub_eq_add_neg] using ht)).1
  obtain ⟨c, hc, e, hbased, hstop⟩ := exists_open_region_seed_search F
    (neg_nonpos.mpr hd.le) hJ U hU ⟨q, hqU⟩
  have htimes (s : ℝ) (hs : s ∈ Icc c 0) : origin + s / 1 ∈
      surgeryObservationInterval O ∩ Ici (surgeryEpochStart (p.i - 1)) := by
    apply hwindow
    simp only [div_one]
    constructor <;> linarith only [hc.1, hs.1, hs.2]
  have hold (s : ℝ) (hs : s ∈ Icc c 0) : origin + s / 1 ∈
      surgeryObservationInterval O ∩ prefixFinalInterval p := by
    refine ⟨(htimes s hs).1, (htimes s hs).1.1, ?_⟩
    simp only [div_one]
    linarith only [hs.2, hOldOrigin]
  have hshort : 64 * B * H * (-c) ≤ 1 :=
    (mul_le_mul_of_nonneg_left (by linarith only [hc.1]) (by
      have hBpos := (seedAnalyticConstant_pos S).trans_le hB
      positivity)).trans hscalarTime
  have hmetricShort : 6 * (52 * H) * (-c) ≤ 1 / 2 := by
    have h := mul_le_mul_of_nonneg_left
      (by linarith only [hc.1] : -c ≤ d) (by positivity : 0 ≤ 312 * H)
    nlinarith only [h, hmetricTime]
  have hcomponent : U ⊆ connectedComponent q :=
    metric_ball_subset_connectedComponent (F.metric origin) q r
  have hbounds := seed_search_scalar_and_curvature P S p hp old pinched e hc.2
    hH hlevel hB hbased hscalar (fun s hs => hold s (Ioo_subset_Icc_self hs))
    (fun s hs x hx => seed_search_before_birth_nonpositive P policy e hc.2
      horigin hbased q hcomponent hbirth s (Ioo_subset_Icc_self hs) hs.2 x hx) hshort
  have hRm : ∀ s (hs : s ∈ Icc c 0), ∀ x ∈ U,
      (F.connection (origin + s / 1)).curvatureTensorNorm (e.forward s hs x) ≤ 52 * H := by
    intro s hs x hx
    have hscale : (((Real.sqrt H)⁻¹)⁻¹) ^ 2 = H := by
      rw [inv_inv, Real.sq_sqrt hH.le]
    simpa only [hscale] using low_scalar_curvature_le_fifty_two P.toM46
      (pinched _ (e.time_subset (mem_image_of_mem _ hs)))
      (inv_pos.mpr (Real.sqrt_pos.mpr hH)) hsmall (e.forward s hs x)
      (by simpa only [hscale] using (hbounds s hs x hx).1)
  have hrHalf : 0 < r / 2 := half_pos hr
  have hrQuarter : 0 < r / 4 := by positivity
  have hmono (k' : ℝ) (hle : k ≤ k')
      (hv : ENNReal.ofReal (k' * (r / 2) ^ 3) ≤
        calibratedMetricVolume (F.metric origin) ((F.metric origin).ball q (r / 2))) :
      ENNReal.ofReal (k * (r / 2) ^ 3) ≤
        calibratedMetricVolume (F.metric origin) ((F.metric origin).ball q (r / 2)) :=
    (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hle (pow_nonneg hrHalf.le 3))).trans hv
  rcases hstop with hplanned | ⟨hT, hcap⟩
  · subst c
    have htimeSmall : Icc (-(r / 2) ^ 2) 0 ⊆ Icc (-d) 0 := by
      intro s hs
      constructor <;> nlinarith only [hs.1, hs.2, hrd, sq_nonneg r]
    have hspaceSmall : (F.metric origin).ball q (r / 2) ⊆ U := by
      intro y hy
      exact hy.trans_le (ENNReal.ofReal_le_ofReal (half_le_self hr.le))
    let test := e.restrict htimeSmall ordConnected_Icc hspaceSmall
    let a := -(r / 2) ^ 2 / 8
    have ha : a ∈ Icc (-(r / 2) ^ 2) 0 := by
      dsimp only [a]
      constructor <;> nlinarith only [sq_nonneg (r / 2)]
    have haNeg : a < 0 := div_neg_of_neg_of_pos
      (neg_neg_of_pos (sq_pos_of_pos hrHalf)) (by norm_num)
    have hancestor := seed_search_before_birth_nonpositive P policy e hc.2
      horigin hbased q hcomponent hbirth a (htimeSmall ha) haNeg q hqU
    have hre : r / 2 ≤ F.parameters.epsilon := by
      rw [old.epsilon_eq]
      exact (half_le_self hr.le).trans hrEpsilon
    apply hmono (p.kappa (Fin.last p.i) / 512) (min_le_left _ _)
    exact seed_volume_of_near_nonpositive_ancestor P hnoncollapse q hrHalf hre test
      (fun hs y hy => hbased (htimeSmall hs) y (hspaceSmall hy))
      (fun s hs y hy => (hRm s (htimeSmall hs) y (hspaceSmall hy)).trans htest)
      ha le_rfl (hold a (htimeSmall ha)) hancestor
  · let : Nonempty (F.slice (origin + c / 1)).carrier := ⟨e.forward c ⟨le_rfl, hc.2⟩ q⟩
    obtain ⟨i, z, ⟨x, hx, hxz⟩, hz⟩ := hcap
    have hs : c ∈ Icc c 0 := ⟨le_rfl, hc.2⟩
    let chart := M44.cylinderSliceChart e hU c hs
    have hcomparison := seed_search_metric_comparison P pinched e hU
      (by positivity : 0 ≤ 52 * H) hbased hRm hmetricShort c hs
    have hupper : ∀ y ∈ chart.source, ∀ v : TangentSpace (𝓡 3) y,
        (F.metric (origin + c / 1)).inner (chart y)
          (mfderiv (𝓡 3) (𝓡 3) chart y v) (mfderiv (𝓡 3) (𝓡 3) chart y v) ≤
            4 * (F.metric origin).inner y v v := by
      intro y hy v
      have hn : 0 ≤ (F.metric origin).inner y v v := by
        by_cases hv : v = 0
        · simp [hv]
        · exact ((F.metric origin).pos y v hv).le
      have h := (hcomparison y hy v).2
      change (F.metric (origin + c / 1)).inner (e.forward c hs y)
        (mfderiv (𝓡 3) (𝓡 3) (e.forward c hs) y v)
        (mfderiv (𝓡 3) (𝓡 3) (e.forward c hs) y v) ≤
          4 * (F.metric origin).inner y v v
      linarith only [h, hn]
    have hdist0 := seed_image_ball_subset (F.metric origin) (F.metric (origin + c / 1))
      chart hupper q (Subset.refl U) ⟨x, hx, hxz⟩
    have hdist : (F.metric (origin + c / 1)).edist z (e.forward c hs q) ≤
        ENNReal.ofReal (2 * r) := by
      let : Bundle.RiemannianBundle
          (TangentSpace (𝓡 3) : (F.slice (origin + c / 1)).carrier → Type _) :=
        ⟨(F.metric (origin + c / 1)).toRiemannianMetric⟩
      have hsymm : (F.metric (origin + c / 1)).edist z (e.forward c hs q) =
          (F.metric (origin + c / 1)).edist (e.forward c hs q) z :=
        Manifold.riemannianEDist_comm
      rw [hsymm]
      exact hdist0.le
    have hcapScalar : (F.connection (origin + c / 1)).scalarCurvature z ≤ 4 * H := by
      rw [← hxz]
      exact (hbounds c hs x hx).1
    have hv := hcapDensity F O hHorizon old admissible pinched scales canonical overlap
      (origin + c / 1) hT inferInstance (htimes c hs).1 (htimes c hs).2
      i H r hr hbudget z hz hcapScalar (e.forward c hs q) hdist (r / 4) hrQuarter
      (by linarith only [hr])
    have hcompact : IsCompact (closure ((F.metric origin).ball q (r / 2))) :=
      (F.slices_compact origin (O.interval_subset horigin)).of_isClosed_subset
        isClosed_closure (subset_univ _)
    have hbuffer : closure ((F.metric origin).ball q (r / 2)) ⊆ U :=
      M04.initial_half_ball_closure_subset_initial_ball (F.metric origin) q hr
    apply hmono (kcap / 64) (min_le_right _ _)
    apply seed_search_volume_density_transfer P pinched e hU
      (by positivity : 0 ≤ 52 * H) hbased hRm hmetricShort q hrHalf hcompact hbuffer c hs
    simpa only [div_div, show (2 : ℝ) * 2 = 4 by norm_num] using hv

end PoincareConjecture.Proofs.M47
