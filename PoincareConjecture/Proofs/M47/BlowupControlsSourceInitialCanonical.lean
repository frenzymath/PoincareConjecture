import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialModelBuffer
import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialNearbyFamily
import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialPositiveCanonical
import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialZeroCanonical
import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialRecentOrdinary
import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialRecentReadout

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

open Proofs.M47

theorem exists_source_standard_initial_neck_canonical_neighborhood
    (P : M47Predecessors.{u}) (S : RepairedControlledSchedulesData.{u})
    (B : M47ComponentAnalyticBounds.{u} S.setup.C)
    (p : SurgeryParameterPrefix S.constants) (hp : S.SeedCompatible p)
    {theta v : ℝ} (htheta : theta < 1) (hv : v ∈ Icc 0 theta)
    {z : StandardCapSpace}
    (N : StandardEvolvingNeck S.cap_persistence.standard_cap.atlas
      S.cap_persistence.standard_cap.flow v (S.calibration.beta * S.setup.epsilon / 3) z
      (Icc (-v * (S.cap_persistence.standard_cap.flow.connection v).scalarCurvature z) 0))
    (hdisjoint : Disjoint N.patch.carrier {y | S.standard_initial.metric.edist 0 y ≤
      ENNReal.ofReal (S.standard_initial.cylindrical_end.radius + 4)})
    (hshort : v * (S.cap_persistence.standard_cap.flow.connection v).scalarCurvature z <
      1 + S.calibration.beta * S.setup.epsilon / 3) :
    ∃ A0 eta0 nearTime Q0 : ℝ, ∃ V : Set StandardCapSpace,
      0 < A0 ∧ 0 < eta0 ∧ 0 < nearTime ∧ 0 < Q0 ∧ IsOpen V ∧ z ∈ V ∧
      ∀ A : ℝ, A0 ≤ A → ∀ eta : ℝ, 0 < eta → eta ≤ eta0 →
      ∀ rNext : ℝ, 0 < rNext → rNext ≤ p.r (Fin.last p.i) →
        ∃ cutoff : ℝ, 0 < cutoff ∧ cutoff ≤ p.Delta (Fin.last p.i) ∧
        ∀ (F : SurgeryFlowData.{u}) (O : SurgeryObservation F),
          O.H ≤ surgeryEpochStart (p.i + 1) →
        ∀ prior : SurgeryPrefixControls p F O,
          SurgeryFlowAdmissible F → SurgeryFlowPinched F →
          SurgeryPostPrefixScales p F O rNext cutoff →
          (∀ b ∈ surgeryObservationInterval O ∩ overlapInterval p,
            F.parameters.delta b ≤ cutoff) →
        ∀ (t : ℝ) (hT : t ∈ F.surgery_times),
        ∀ [Nonempty (F.slice t).carrier], ∀ (i : Fin (F.event t hT).cap_count)
          (J : Set ℝ)
          (e : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2) J
            ((F.metric t).ball ((F.event t hT).caps i).tip (A * F.parameters.h t)))
          (initial : SurgeryCapInitialComparison F t hT i A),
          SurgeryCapFamilyComparison F
            (O.redecorateTo prior.standard_initial_eq).standard_flow A eta e initial.chart →
        ∀ hzero : (0 : ℝ) ∈ J,
          (∀ y ∈ (F.metric t).ball ((F.event t hT).caps i).tip (A * F.parameters.h t),
            HEq (e.forward 0 hzero y) y) →
          0 < F.parameters.h t →
        ∀ (s : ℝ) (hs : s ∈ J), s ∈ Icc 0 theta → Icc 0 s ⊆ J →
          |s - v| < nearTime → ∀ z' ∈ V,
          let base := t + s / ((F.parameters.h t)⁻¹ ^ 2)
          let x := e.forward s hs (initial.chart z')
          let Q := (F.connection base).scalarCurvature x
          base ∈ Ico (surgeryEpochStart p.i) O.H → Q0 ≤ Q → rNext⁻¹ ^ 2 ≤ Q →
          SurgeryCanonicalOn F (surgeryObservationInterval O ∩ Iio base) rNext →
          Q * (base - t) ∈ Icc 0 1 →
          SurgeryCanonicalControl F base x S.setup.epsilon S.setup.C := by
  let gamma := S.calibration.beta * S.setup.epsilon / 3
  let epsilonOld := S.calibration.beta * S.setup.epsilon / 2
  have hepsilon : 0 < S.setup.epsilon := S.setup.epsilon_pos
  have hepsilonSmall : S.setup.epsilon < 1 / 2 :=
    (S.setup.epsilon_le.trans (min_le_left _ _)).trans_lt (by norm_num)
  have hgamma : 0 < gamma := N.epsilon_pos
  have hsmall : gamma ≤ 1 / 1200 := by
    have he : S.setup.epsilon ≤ 1 / 200 := S.setup.epsilon_le.trans (min_le_left _ _)
    have hb := mul_le_mul S.calibration.beta_lt_half.le he hepsilon.le
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
    dsimp only [gamma]
    linarith only [hb]
  have hL : (1200 : ℝ) ≤ gamma⁻¹ := by
    have h := inv_anti₀ hgamma hsmall
    norm_num at h
    exact h
  have heOld : 0 < epsilonOld := div_pos (mul_pos S.calibration.beta_pos hepsilon) (by norm_num)
  have heOldSmall : epsilonOld < 1 / 2 := by
    have hb := mul_lt_mul_of_pos_right S.calibration.beta_lt_half hepsilon
    dsimp only [epsilonOld]
    linarith only [hb, hepsilonSmall]
  have hproduct : 3 * gamma = S.calibration.beta * S.setup.epsilon := by
    dsimp only [gamma]
    ring
  have hOldInverse : epsilonOld⁻¹ = 2 * gamma⁻¹ / 3 := by
    dsimp only [epsilonOld, gamma]
    field_simp
  have hhalfInverse : (2 * gamma)⁻¹ = gamma⁻¹ / 2 := by
    simp only [mul_inv_rev, div_eq_mul_inv]
  have hthirdInverse : (S.calibration.beta * S.setup.epsilon)⁻¹ = gamma⁻¹ / 3 := by
    rw [← hproduct]
    simp only [mul_inv_rev, div_eq_mul_inv]
  obtain ⟨r, hr, E, hEpsilon, hEconnection, hEcenter, hEmap, hEinverse, hEcarrier, hEr⟩ :=
    exists_source_initial_model_buffer N hsmall
  let A0 := r + 3
  have hA0 : 0 < A0 := by dsimp only [A0]; linarith only [hr]
  have hEA0 : E.carrier ⊆ S.standard_initial.metric.ball 0 A0 := by
    intro x hx
    exact (hEr hx).trans_le (ENNReal.ofReal_le_ofReal (by dsimp only [A0]; linarith))
  obtain ⟨hRlo, hRhi, _hInvR, _hBirthR⟩ :=
    standard_initial_neck_birth_scale_bounds N hsmall hdisjoint hshort
  obtain ⟨etaRecent, deltaRecent, V, hetaRecent, hdeltaRecent, hV, hzV, hVE, hheight, nearby⟩ :=
    exists_source_initial_nearby_family S.cap_persistence.standard_cap htheta hA0 hv N
      (by linarith only [hRlo]) (by linarith only [hRhi])
      E hEpsilon hEmap hEcenter hEA0
  obtain ⟨etaGeometry, deltaGeometry, hetaGeometry, hdeltaGeometry, geometry⟩ :=
    exists_source_initial_fixed_geometry_tolerance S.cap_persistence.standard_cap N
      hsmall hdisjoint hshort
  obtain ⟨omega, Qold, homega, _homegaOne, hQold, older⟩ :=
    exists_source_initial_older_family P S B p hp heOld heOldSmall hr
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 3)
  let Q0 := max 128 Qold
  have hQ0 : 0 < Q0 := hQold.trans_le (le_max_right _ _)
  refine ⟨A0, min etaRecent etaGeometry, deltaRecent, Q0, V,
    hA0, lt_min hetaRecent hetaGeometry, hdeltaRecent, hQ0, hV, hzV, ?_⟩
  intro A hA eta heta hetaSmall rNext hrNext hrLast
  obtain ⟨deltaOld, hdeltaOld, hdeltaLast, oldFamily⟩ := older rNext hrNext hrLast
  let cutoff := min deltaOld deltaGeometry
  have hcutOld : cutoff ≤ deltaOld := min_le_left _ _
  have hcutGeometry : cutoff ≤ deltaGeometry := min_le_right _ _
  refine ⟨cutoff, lt_min hdeltaOld hdeltaGeometry, hcutOld.trans hdeltaLast, ?_⟩
  intro F O hH prior hadmissible hpinched next overlap T hT hn i J e initial comparison
    hzero hbased hh s hs hst hJ hnear x hxV base point Q hBase hLarge hThreshold hEarlier hage
  have hinitial : F.standard_initial = S.standard_initial := by
    rw [prior.standard_initial_eq, hp.setup_eq]
    exact S.setup_standard_initial_eq
  have hpflow : HEq p.setup.standard_flow S.cap_persistence.standard_cap.flow := by
    rw [hp.setup_eq]
    exact S.setup_standard_flow_eq
  have hmodel := (Proofs.M46.redecorateTo_standard_flow O prior.standard_initial_eq).trans hpflow
  have hQ : 0 < Q := hQ0.trans_le hLarge
  have h128 : 128 ≤ Q := (le_max_left _ _).trans hLarge
  have hQoldLarge : Qold ≤ Q := (le_max_right _ _).trans hLarge
  have hTA := source_initial_recent_time_mem_overlap p hBase hH h128 hage
  have hdelta : ((F.event T hT).necks i).neck.epsilon ≤ deltaGeometry := by
    rw [(F.event T hT).neck_delta i]
    exact (overlap T hTA).trans hcutGeometry
  have hxE : x ∈ E.carrier := hVE hxV
  have hxR : x ∈ F.standard_initial.metric.ball 0 r := hinitial.symm ▸ hEr hxE
  have hEA : E.carrier ⊆ F.standard_initial.metric.ball 0 A := by
    intro y hy
    rw [hinitial]
    exact (hEA0 hy).trans_le (ENNReal.ofReal_le_ofReal hA)
  have hhalfSub : N.patch.coordinate '' (univ ×ˢ Ioo (-gamma⁻¹ / 2) (gamma⁻¹ / 2)) ⊆
      N.patch.carrier := by
    rintro y ⟨w, hw, rfl⟩
    rw [← N.patch.coordinate_image]
    refine ⟨w, ⟨mem_univ _, ?_⟩, rfl⟩
    constructor <;> linarith only [hw.2.1, hw.2.2, hL]
  have hxN : x ∈ N.patch.carrier := hhalfSub (hEcarrier ▸ hxE)
  have hxHeight : |(N.patch.inverse x).2| ≤ 1 := by
    rw [← hEinverse]
    exact (hheight x hxV).le
  have hsource : N.patch.coordinate '' (univ ×ˢ Ioo (-gamma⁻¹ / 2) (gamma⁻¹ / 2)) ⊆
      F.standard_initial.metric.ball 0 A := hEcarrier ▸ hEA
  obtain ⟨hxUs, havoid, hmargin, hcapture⟩ := geometry F hinitial _ hmodel
    T hT hn i A eta J e initial comparison hzero hbased heta
      (hetaSmall.trans (min_le_right _ _)) hdelta hsource x hxN hxHeight
  obtain ⟨hHlo, hHhi, hclockRecent, hfamilyRecent⟩ := nearby A hA F hinitial _ hmodel
    T hT hn i J _ e initial eta heta (hetaSmall.trans (min_le_left _ _)) comparison hh
      s hs hst hJ hnear x hxV
  have hqeq : ((F.event T hT).necks i).neck.scale⁻¹ ^ 2 = (F.parameters.h T)⁻¹ ^ 2 := by
    rw [(F.event T hT).neck_scale i]
  obtain ⟨old⟩ := hadmissible.strong_boundaries T hT i
  have hAroom : r + 2 < A := by dsimp only [A0] at hA; linarith only [hA]
  have hmarginOld :
      (((F.event T hT).necks i).neck.coordinate_inverse (sourceInitialOldMap initial x)).2 +
        epsilonOld⁻¹ < 0 := by rwa [hOldInverse]
  have hdata := oldFamily F O hH prior hadmissible hpinched (next.mono_delta hcutOld)
    (fun t ht => (overlap t ht).trans hcutOld) hBase hQoldLarge hThreshold hEarlier
      T hT i old hage (by simpa only [hqeq] using hHlo.le)
        (by simpa only [hqeq] using hHhi.le) initial hAroom x hxR (havoid x hxUs) hmarginOld
  obtain ⟨Eold, hOldEps, _hOldConnection, hOldCenter, hOldCarrier, _hOldMap, _hOldInverse,
    hOldNegative, hOldScale, hk, hOldClock, rawOld, _hOldFuture, hRawZero, hRawMetric,
    hRawFamily⟩ := hdata
  have hOldData : ∃ eold : SurgeryFlowCylinder F (F.event T hT).terminal T
      (((F.event T hT).necks i).neck.scale⁻¹ ^ 2) (Icc (-(1 + omega)) 0) Eold.carrier,
      (∀ hz y, HEq (eold.forward 0 hz y)
        ((F.event T hT).retention.map ((F.event T hT).limit_identify.inverse y))) ∧
      (∀ hz, ∀ y ∈ Eold.carrier, ∀ a b : TangentSpace (𝓡 3) y,
        eold.pullbackInner 0 hz y a b = (((F.event T hT).necks i).neck.scale⁻¹ ^ 2) *
          (F.event T hT).limit_metric.inner y a b) ∧
      RoundCylinderFamilyClose epsilonOld (Icc (-1 : ℝ) 0)
        (fun u z a b =>
          (((F.event T hT).necks i).neck.connection.scalarCurvature
            (sourceInitialOldMap initial x) / (((F.event T hT).necks i).neck.scale⁻¹ ^ 2)) *
            surgeryCylinderPullback eold Eold.coordinate_map
              (u / (((F.event T hT).necks i).neck.connection.scalarCurvature
                (sourceInitialOldMap initial x) / (((F.event T hT).necks i).neck.scale⁻¹ ^ 2)))
              z a b) := ⟨rawOld, hRawZero, hRawMetric, hRawFamily⟩
  rw [hqeq] at hOldData
  obtain ⟨eold, hOldZero, hOldMetric, hOldFamily⟩ := hOldData
  simp only [hqeq] at hOldScale hk hOldClock
  have htau : 0 < 1 + omega := by linarith only [homega]
  have hkpos : 0 < ((F.event T hT).necks i).neck.connection.scalarCurvature
      (sourceInitialOldMap initial x) / ((F.parameters.h T)⁻¹ ^ 2) := by linarith only [hk.1]
  have hOldFamily' : RoundCylinderFamilyClose Eold.epsilon (Icc (-1 : ℝ) 0)
      (fun u z a b =>
        (((F.event T hT).necks i).neck.connection.scalarCurvature (sourceInitialOldMap initial x) /
          ((F.parameters.h T)⁻¹ ^ 2)) * surgeryCylinderPullback eold Eold.coordinate_map
            (u / (((F.event T hT).necks i).neck.connection.scalarCurvature
              (sourceInitialOldMap initial x) / ((F.parameters.h T)⁻¹ ^ 2))) z a b) := by
    simpa only [hOldEps] using hOldFamily
  obtain ⟨D, hDsource, hDpoint, hDretained, hDmetric⟩ := exists_source_initial_birth_slice_chart
    hT i eold Eold.carrier_open ⟨by linarith only [htau], le_rfl⟩ hOldNegative
      (fun y => hOldZero _ y)
  have hUsOpen : IsOpen
      (N.patch.coordinate '' (univ ×ˢ Ioo (-gamma⁻¹ / 2) (gamma⁻¹ / 2))) := by
    simpa only [neg_div] using N.patch.open_axial_slab
      (show gamma⁻¹ / 2 ≤ gamma⁻¹ by linarith only [hL])
  have hDcapture : MapsTo (sourceInitialOldMap initial)
      (N.patch.coordinate '' (univ ×ˢ Ioo (-gamma⁻¹ / 2) (gamma⁻¹ / 2))) D.source := by
    rw [hDsource, hOldCarrier, hOldInverse]
    exact hcapture
  obtain ⟨_hUpOpen, hUpD, hDmaps⟩ := source_initial_birth_slice_capture hT i initial hUsOpen
    hsource havoid D hDretained hDcapture
  have hDcenter : D Eold.center = initial.chart x := by
    rw [hOldCenter]
    exact (hDmaps x hxUs).1
  have hmetricD : ∀ y ∈ D.source, ∀ a b : TangentSpace (𝓡 3) y,
      (F.metric T).inner (D y) (mfderiv (𝓡 3) (𝓡 3) D y a)
        (mfderiv (𝓡 3) (𝓡 3) D y b) = (F.event T hT).limit_metric.inner y a b := by
    intro y hy a b
    exact hDmetric y (hDsource ▸ hy) a b
  have hbasedAll : ∀ hz y, y ∈ (F.metric T).ball ((F.event T hT).caps i).tip
      (A * F.parameters.h T) → HEq (e.forward 0 hz y) y := fun _ y hy => hbased y hy
  by_cases hs0 : s = 0
  · have heOldLe : Eold.epsilon ≤ S.setup.epsilon := by
      rw [hOldEps]
      have hb := mul_lt_mul_of_pos_right S.calibration.beta_lt_half hepsilon
      dsimp only [epsilonOld]
      linarith only [hb, hepsilon]
    have hcanonical := source_initial_zero_age_canonical
      (F := F) (C := (F.event T hT).terminal) (T := T)
      (q := (F.parameters.h T)⁻¹ ^ 2) (tau := 1 + omega) Eold hkpos htau heOldLe
      hepsilonSmall hOldScale hOldClock eold hOldFamily' D hDsource
        (fun y => (hDpoint y).symm) hmetricD (Cc := S.setup.C)
    rw [hDcenter] at hcanonical
    have hpoint : (⟨base, point⟩ : Σ t, (F.slice t).carrier) = ⟨T, initial.chart x⟩ := by
      apply Sigma.ext (by dsimp only [base]; rw [hs0]; simp only [zero_div, add_zero])
      have hxImage : initial.chart x ∈ (F.metric T).ball ((F.event T hT).caps i).tip
          (A * F.parameters.h T) :=
        comparison.choose_spec.2.2.2.1 ▸ mem_image_of_mem initial.chart (hEA hxE)
      have hsame (a : ℝ) (ha : a ∈ J) (ha0 : a = 0) :
          HEq (e.forward a ha (initial.chart x)) (initial.chart x) := by
        subst a
        exact hbasedAll ha (initial.chart x) hxImage
      exact hsame s hs hs0
    exact (congrArg (fun p : Σ t, (F.slice t).carrier =>
      SurgeryCanonicalControl F p.1 p.2 S.setup.epsilon S.setup.C) hpoint).mpr hcanonical
  · have hspos : 0 < s := lt_of_le_of_ne hst.1 (Ne.symm hs0)
    have hpatchMargin : |(N.patch.inverse x).2| +
        (S.calibration.beta * S.setup.epsilon)⁻¹ ≤ gamma⁻¹ / 2 := by
      rw [hthirdInverse]
      linarith only [hxHeight, hL]
    have hsource' : N.patch.coordinate '' (univ ×ˢ Ioo (-(gamma⁻¹ / 2)) (gamma⁻¹ / 2)) ⊆
        F.standard_initial.metric.ball 0 A := by simpa only [neg_div] using hsource
    obtain ⟨hUp, hxUp, patch, hcoordinate, _hinverse⟩ := exists_source_initial_recent_patch
      initial N.patch (show gamma⁻¹ / 2 ≤ gamma⁻¹ by linarith only [hL])
        (inv_pos.mpr (mul_pos S.calibration.beta_pos hepsilon)) x hxN hpatchMargin hsource'
    let Up : TopologicalSpace.Opens (F.slice T).carrier :=
      ⟨initial.chart '' (N.patch.coordinate ''
        (univ ×ˢ Ioo (-(gamma⁻¹ / 2)) (gamma⁻¹ / 2))), hUp⟩
    let center : Up := ⟨initial.chart x, hxUp⟩
    have hUpD' : (Up : Set _) ⊆ D.target := by
      change initial.chart '' (N.patch.coordinate ''
        (univ ×ˢ Ioo (-(gamma⁻¹ / 2)) (gamma⁻¹ / 2))) ⊆ D.target
      simpa only [neg_div] using hUpD
    have hUpV : (Up : Set _) ⊆ (F.metric T).ball ((F.event T hT).caps i).tip
        (A * F.parameters.h T) := by
      rw [← comparison.choose_spec.2.2.2.1]
      exact image_mono hsource'
    obtain ⟨hRecentTimes, _recent, Grecent, _hRecentMaps, hRecentMetric, hfinal, hjoinMetric⟩ :=
      exists_source_initial_recent_ordinary P e hQ hspos hJ hbasedAll Up hUpV center rfl
    have hdomain : ∀ a ∈ Ioo (-(S.calibration.beta * S.setup.epsilon)⁻¹)
        (S.calibration.beta * S.setup.epsilon)⁻¹,
        a + (E.coordinate_inverse x).2 ∈ Ioo (-E.epsilon⁻¹) E.epsilon⁻¹ := by
      intro a ha
      rw [hEpsilon, hhalfInverse, hEinverse]
      have hc := abs_le.mp hxHeight
      rw [hthirdInverse] at ha
      constructor <;> linarith only [ha.1, ha.2, hc.1, hc.2, hL]
    have hcoordinate' : ∀ w : RoundCylinderSpace,
        w.2 ∈ Ioo (-(S.calibration.beta * S.setup.epsilon)⁻¹)
          (S.calibration.beta * S.setup.epsilon)⁻¹ →
        (patch.coordinate w).val =
          initial.chart (E.coordinate_map (neckAxialSpaceMap 1 (E.coordinate_inverse x).2 w)) := by
      simpa only [hEmap, hEinverse] using hcoordinate
    have hread : ∀ u (hu : u ∈ Icc (-(Q / ((F.parameters.h T)⁻¹ ^ 2)) * s) 0),
        ∀ y : Up, ∀ a b : TangentSpace (𝓡 3) y,
        (Grecent.metric u).inner y a b = (Q / ((F.parameters.h T)⁻¹ ^ 2)) *
          e.pullbackInner (s + u / (Q / ((F.parameters.h T)⁻¹ ^ 2))) (hclockRecent hu) y.val
            (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : Up → (F.slice T).carrier) y a)
            (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : Up → (F.slice T).carrier) y b) := by
      intro u hu y a b
      exact hRecentMetric u (by simpa only [neg_mul] using hu) y a b
    have hfamily := source_initial_recent_family_on_patch e initial comparison hh E hEA hdomain
      hclockRecent Up patch hcoordinate' Grecent hread
        (by convert hfamilyRecent using 1; ring)
    have hVopen : IsOpen ((F.metric T).ball ((F.event T hT).caps i).tip
        (A * F.parameters.h T)) := comparison.choose_spec.2.2.2.1 ▸
      (Proofs.M46.capInitialPartialDiffeomorph initial).open_target
    exact source_initial_positive_age_canonical (F := F) (C := (F.event T hT).terminal)
      (T := T) (q := (F.parameters.h T)⁻¹ ^ 2) (tau := 1 + omega)
      P S.calibration.gluing hepsilon hepsilonSmall
      S.calibration.beta_pos (S.calibration.beta_lt_half.le.trans (by norm_num))
      Eold hOldEps hQ hkpos htau hspos hOldScale hOldClock eold hOldMetric hOldFamily'
      e hVopen hJ hbasedAll Up hUpV center D hDsource hUpD'
      hDpoint hmetricD hDcenter Grecent patch hRecentTimes hRecentMetric hjoinMetric hfinal
      (by simpa only [neg_mul] using hfamily) rfl

end PoincareConjecture.M47
