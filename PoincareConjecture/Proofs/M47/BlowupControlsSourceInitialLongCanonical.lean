import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialModelBuffer
import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialNearbyFamily
import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialRecentOrdinary
import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialRecentReadout
import PoincareConjecture.Proofs.M47.BlowupControlsSourceLongRecent
import PoincareConjecture.Proofs.M46.Sec16_1_LGeometry.Prop16_5_OverlapCaps

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

open Proofs.M47

theorem exists_source_standard_initial_neck_long_canonical_neighborhood
    (P : M47Predecessors.{u}) (S : RepairedControlledSchedulesData.{u})
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
          1 ≤ Q * (base - t) →
          SurgeryCanonicalControl F base x S.setup.epsilon S.setup.C := by
  let gamma := S.calibration.beta * S.setup.epsilon / 3
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
  have hproduct : 3 * gamma = S.calibration.beta * S.setup.epsilon := by
    dsimp only [gamma]
    ring
  have hhalfInverse : (2 * gamma)⁻¹ = gamma⁻¹ / 2 := by
    simp only [mul_inv_rev, div_eq_mul_inv]
  have hthirdInverse : (S.calibration.beta * S.setup.epsilon)⁻¹ = gamma⁻¹ / 3 := by
    rw [← hproduct]
    simp only [mul_inv_rev, div_eq_mul_inv]
  obtain ⟨r, hr, E, hEpsilon, _hEconnection, hEcenter, hEmap, hEinverse, hEcarrier, hEr⟩ :=
    exists_source_initial_model_buffer N hsmall
  let A0 := r + 3
  have hA0 : 0 < A0 := by dsimp only [A0]; linarith only [hr]
  have hEA0 : E.carrier ⊆ S.standard_initial.metric.ball 0 A0 := by
    intro x hx
    exact (hEr hx).trans_le (ENNReal.ofReal_le_ofReal (by dsimp only [A0]; linarith))
  obtain ⟨hRlo, hRhi, _hInvR, _hBirthR⟩ :=
    standard_initial_neck_birth_scale_bounds N hsmall hdisjoint hshort
  obtain ⟨eta0, nearTime, V, heta0, hnearTime, hV, hzV, hVE, hheight, nearby⟩ :=
    exists_source_initial_nearby_family S.cap_persistence.standard_cap htheta hA0 hv N
      (by linarith only [hRlo]) (by linarith only [hRhi]) E hEpsilon hEmap hEcenter hEA0
  refine ⟨A0, eta0, nearTime, 1, V, hA0, heta0, hnearTime, zero_lt_one, hV, hzV, ?_⟩
  intro A hA eta heta hetaSmall rNext _hrNext _hrLast
  refine ⟨p.Delta (Fin.last p.i), p.Delta_pos _, le_rfl, ?_⟩
  intro F O _hH prior _hadmissible _hpinched _next _overlap T hT hn i J e initial comparison
    hzero hbased hh s hs hst hJ hnear x hxV base point Q _hBase hLarge _hThreshold _hEarlier hage
  have hinitial : F.standard_initial = S.standard_initial := by
    rw [prior.standard_initial_eq, hp.setup_eq]
    exact S.setup_standard_initial_eq
  have hpflow : HEq p.setup.standard_flow S.cap_persistence.standard_cap.flow := by
    rw [hp.setup_eq]
    exact S.setup_standard_flow_eq
  have hmodel := (Proofs.M46.redecorateTo_standard_flow O prior.standard_initial_eq).trans hpflow
  have hQ : 0 < Q := zero_lt_one.trans_le hLarge
  have hxE : x ∈ E.carrier := hVE hxV
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
  obtain ⟨hHlo, _hHhi, hclockRecent, hfamilyRecent⟩ := nearby A hA F hinitial _ hmodel
    T hT hn i J _ e initial eta heta hetaSmall comparison hh s hs hst hJ hnear x hxV
  have hHpos : 0 < Q / ((F.parameters.h T)⁻¹ ^ 2) := by linarith only [hHlo]
  have hlong : 1 ≤ Q / ((F.parameters.h T)⁻¹ ^ 2) * s := by
    have heq : Q * (base - T) = Q / ((F.parameters.h T)⁻¹ ^ 2) * s := by
      dsimp only [base]
      ring
    exact heq ▸ hage
  have hspos : 0 < s := pos_of_mul_pos_right (zero_lt_one.trans_le hlong) hHpos.le
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
  have hUpV : (Up : Set _) ⊆ (F.metric T).ball ((F.event T hT).caps i).tip
      (A * F.parameters.h T) := by
    rw [← comparison.choose_spec.2.2.2.1]
    exact image_mono hsource'
  have hbasedAll : ∀ hz y, y ∈ (F.metric T).ball ((F.event T hT).caps i).tip
      (A * F.parameters.h T) → HEq (e.forward 0 hz y) y := fun _ y hy => hbased y hy
  obtain ⟨hRecentTimes, _recent, Grecent, _hRecentMaps, hRecentMetric, hfinal, _hjoinMetric⟩ :=
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
  have hbetaOne : S.calibration.beta ≤ 1 :=
    S.calibration.beta_lt_half.le.trans (by norm_num)
  have haccuracy : S.calibration.beta * S.setup.epsilon ≤ S.setup.epsilon := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hbetaOne hepsilon.le
  exact source_long_recent_canonical e hQ hspos hJ Up hUpV center Grecent patch
    (mul_pos S.calibration.beta_pos hepsilon) haccuracy hepsilonSmall
    hRecentTimes hRecentMetric hfinal (by simpa only [neg_mul] using hfamily) hlong rfl

end PoincareConjecture.M47
