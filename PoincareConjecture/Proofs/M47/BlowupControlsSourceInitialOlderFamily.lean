import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialRawSearch
import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialRetainedTensor
import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialStaticRecenter
import PoincareConjecture.Proofs.M47.SeedVolume

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M47

open Proofs.M47

theorem exists_source_initial_older_family
    (P : M47Predecessors.{u}) (S : RepairedControlledSchedulesData.{u})
    (B : M47ComponentAnalyticBounds.{u} S.setup.C)
    (p : SurgeryParameterPrefix S.constants) (hp : S.SeedCompatible p)
    {epsilon r m M : ℝ} (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon < 1 / 2)
    (hr : 0 < r) (hm : 0 < m) (hM : 0 < M) :
    ∃ omega Q0 : ℝ, 0 < omega ∧ omega ≤ 1 ∧ 0 < Q0 ∧
      ∀ rNext : ℝ, 0 < rNext → rNext ≤ p.r (Fin.last p.i) →
      ∃ cutoff : ℝ, 0 < cutoff ∧ cutoff ≤ p.Delta (Fin.last p.i) ∧
      ∀ (F : SurgeryFlowData.{u}) (O : SurgeryObservation F),
        O.H ≤ surgeryEpochStart (p.i + 1) →
      ∀ _prior : SurgeryPrefixControls p F O,
        SurgeryFlowAdmissible F → SurgeryFlowPinched F →
        SurgeryPostPrefixScales p F O rNext cutoff →
        (∀ t ∈ surgeryObservationInterval O ∩ overlapInterval p,
          F.parameters.delta t ≤ cutoff) →
      ∀ {base Q : ℝ}, base ∈ Ico (surgeryEpochStart p.i) O.H → Q0 ≤ Q →
        rNext⁻¹ ^ 2 ≤ Q →
        SurgeryCanonicalOn F (surgeryObservationInterval O ∩ Iio base) rNext →
      ∀ (T : ℝ) (hT : T ∈ F.surgery_times), ∀ [Nonempty (F.slice T).carrier],
      ∀ (i : Fin (F.event T hT).cap_count) (old : SurgeryTerminalStrongNeck F T hT i),
        Q * (base - T) ∈ Icc (0 : ℝ) 1 →
        m ≤ Q / (((F.event T hT).necks i).neck.scale⁻¹ ^ 2) →
        Q / (((F.event T hT).necks i).neck.scale⁻¹ ^ 2) ≤ M →
      ∀ {A : ℝ} (initial : SurgeryCapInitialComparison F T hT i A), r + 2 < A →
      ∀ x ∈ F.standard_initial.metric.ball 0 r,
        initial.chart x ∉ ((F.event T hT).caps i).carrier →
      let N := ((F.event T hT).necks i).neck
      let y := sourceInitialOldMap initial x
      let c := (N.coordinate_inverse y).2
      let q := N.scale⁻¹ ^ 2
      let k := N.connection.scalarCurvature y / q
      c + epsilon⁻¹ < 0 →
      ∃ E : EpsilonNeck (F.event T hT).limit_metric,
        E.epsilon = epsilon ∧ E.connection = N.connection ∧ E.center = y ∧
        E.carrier = N.region (c - epsilon⁻¹) (c + epsilon⁻¹) ∧
        E.coordinate_map = N.coordinate_map ∘ neckAxialSpaceMap 1 c ∧
        E.coordinate_inverse = neckAxialInverse 1 c ∘ N.coordinate_inverse ∧
        E.carrier ⊆ N.region (-N.epsilon⁻¹) 0 ∧
        E.scale⁻¹ ^ 2 = q * k ∧ k ∈ Icc (3 / 4 : ℝ) (5 / 4) ∧
        MapsTo (fun u : ℝ => u / k) (Icc (-1 : ℝ) 0) (Icc (-(1 + omega)) 0) ∧
      ∃ e : SurgeryFlowCylinder F (F.event T hT).terminal T q
          (Icc (-(1 + omega)) 0) E.carrier,
        (∀ s (hs : s ∈ Ioo (-1 : ℝ) 0)
          (hs' : s ∈ Icc (-(1 + omega)) 0), ∀ y ∈ E.carrier,
            e.forward s hs' y = old.cylinder.forward s hs y) ∧
        (∀ hs y, HEq (e.forward 0 hs y)
          ((F.event T hT).retention.map ((F.event T hT).limit_identify.inverse y))) ∧
        (∀ hz, ∀ y ∈ E.carrier, ∀ v w : TangentSpace (𝓡 3) y,
          e.pullbackInner 0 hz y v w = q * (F.event T hT).limit_metric.inner y v w) ∧
        RoundCylinderFamilyClose epsilon (Icc (-1 : ℝ) 0)
          (fun u z v w => k * surgeryCylinderPullback e E.coordinate_map (u / k) z v w) := by
  let W := epsilon⁻¹
  let R := 4 * r + W + 3
  have hW : 0 < W := inv_pos.mpr hepsilon
  have hWone : 1 ≤ W := (one_le_inv₀ hepsilon).mpr (by linarith only [hepsilonSmall])
  have hR : 0 < R := by dsimp only [R]; positivity
  obtain ⟨zeta, K, Qsearch, hzeta, hzetaSmall, hK, hQsearch, search⟩ :=
    exists_source_initial_raw_search P.toM46 S B p hp hm hM hR
  obtain ⟨omega, deltaTensor, homega, homegaZeta, homegaOne,
    hdeltaTensor, _hdeltaE, _hdeltaSmall, tensor⟩ :=
    exists_source_initial_older_tensor_tolerance P hepsilon hzeta hzetaSmall hK
  let Q0 := max 128 Qsearch
  have hQ0 : 0 < Q0 := hQsearch.trans_le (le_max_right _ _)
  refine ⟨omega, Q0, homega, homegaOne, hQ0, ?_⟩
  intro rNext hrNext hrLast
  obtain ⟨deltaSearch, hdeltaSearch, hdeltaLast, rawSearch⟩ := search rNext hrNext hrLast
  let cutoff := min deltaSearch (min deltaTensor (R + 2)⁻¹)
  have hcutoff : 0 < cutoff := lt_min hdeltaSearch (lt_min hdeltaTensor (by positivity))
  have hcutSearch : cutoff ≤ deltaSearch := min_le_left _ _
  have hcutTensor : cutoff ≤ deltaTensor := (min_le_right _ _).trans (min_le_left _ _)
  have hcutSize : cutoff ≤ (R + 2)⁻¹ := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨cutoff, hcutoff, hcutSearch.trans hdeltaLast, ?_⟩
  intro F O hH prior hadmissible hpinched next overlap base Q hBase hLarge hThreshold
    hEarlier T hT hn i old hage hmH hHM A initial hA x hx havoid N y c q k hmargin
  have h128 : 128 ≤ Q := (le_max_left _ _).trans hLarge
  have hSearchLarge : Qsearch ≤ Q := (le_max_right _ _).trans hLarge
  have hTOverlap := source_initial_recent_time_mem_overlap p hBase hH h128 hage
  have hdelta : N.epsilon ≤ cutoff := by
    rw [show N.epsilon = F.parameters.delta T from (F.event T hT).neck_delta i]
    exact overlap T hTOverlap
  have hbuffer : R + 1 < N.epsilon⁻¹ := by
    have h := inv_anti₀ N.epsilon_pos (hdelta.trans hcutSize)
    simp only [inv_inv] at h
    linarith only [h]
  have hsize : 4 * r + W + 4 < N.epsilon⁻¹ := by
    dsimp only [R] at hbuffer
    linarith only [hbuffer]
  have hxA : x ∈ F.standard_initial.metric.ball 0 A :=
    hx.trans_le (ENNReal.ofReal_le_ofReal (by linarith only [hA]))
  have hy : y ∈ N.carrier := (source_initial_chart_retention hT i initial hxA havoid).2.2.1
  have hheight : |c| < 4 * r := source_initial_old_map_height_lt hT i initial hr hA hx havoid
  have hband : ∀ a ∈ Ioo (-epsilon⁻¹) epsilon⁻¹, a + c ∈ Ioo (-R) R := by
    intro a ha
    have hh := abs_lt.mp hheight
    dsimp only [R, W]
    constructor <;> linarith only [ha.1, ha.2, hh.1, hh.2]
  have hdomain : ∀ a ∈ Ioo (-epsilon⁻¹) epsilon⁻¹,
      a + c ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
    intro a ha
    have hb := hband a ha
    constructor <;> linarith only [hb.1, hb.2, hbuffer]
  obtain ⟨left, hleft, U, hU, hne, D, hagree, hcurv⟩ :=
    rawSearch F O hH prior hadmissible hpinched (next.mono_delta hcutSearch)
      (fun t ht => (overlap t ht).trans hcutSearch) hBase hSearchLarge hThreshold
      hEarlier T hT i old hage hmH hHM
  obtain ⟨hk, hclock, hBzero, hfamily⟩ := tensor hT i old (hdelta.trans hcutTensor)
    hR hbuffer hleft U hU hne D hagree hcurv y hy hband
  have hq : 0 < q := sq_pos_of_pos (inv_pos.mpr N.scale_pos)
  have hkpos : 0 < k := by linarith only [hk.1]
  have hqk : q * k = N.connection.scalarCurvature y := by
    dsimp only [k]
    field_simp
  have hscalar : 0 < N.connection.scalarCurvature y := hqk ▸ mul_pos hq hkpos
  have hclockW : MapsTo (fun u : ℝ => u / k) (Icc (-1 : ℝ) 0) (Icc (-1 - W) 0) := by
    intro u hu
    have h : u / k ∈ Icc (-1 - omega) 0 := hclock hu
    exact ⟨by linarith only [h.1, homegaOne, hWone], h.2⟩
  obtain ⟨E, V, hepsilon, hconnection, hcenter, hcarrier, hmap, hinverse, _hsphere,
    hEV, hnegativeV, _hqscale, _hpositive, _hclockW⟩ :=
    exists_source_initial_static_recentered_neck hT i initial
      (U := {x}) (by simpa only [singleton_subset_iff] using hxA)
      (by intro z hz; simpa only [mem_singleton_iff.mp hz] using havoid)
      (mem_singleton x) hx hr hW hA hmargin hsize le_rfl hepsilon hepsilonSmall hdomain
      hq rfl ⟨hk, hclockW⟩ hqk rfl hscalar hBzero hfamily
  have hnegative : E.carrier ⊆ N.region (-N.epsilon⁻¹) 0 := hEV.trans hnegativeV
  have hEraw : E.carrier ⊆ U := by
    have hg := source_initial_older_carrier_geometry hT i initial hr hW hA hx havoid
      hmargin hsize
    intro z hz
    rw [hU]
    have hzV : z ∈ N.region (c - W) (c + W) := by simpa only [hcarrier, W] using hz
    have hh := hg.2.2.2.2 hzV
    exact ⟨hh.1, by linarith only [hh.2.1], by linarith only [hh.2.2]⟩
  have hEne : E.carrier.Nonempty := ⟨E.center, E.central_sphere_subset E.center_on_central_sphere⟩
  obtain ⟨closed, hpast, hold, hzero⟩ := exists_source_initial_closed_cylinder hT i old D
    (by linarith only [hleft, hzeta]) E.carrier_open hEne hEraw hnegative hagree
  have hinterval : Icc (-(1 + omega)) 0 ⊆ Icc left 0 := by
    intro s hs
    exact ⟨by linarith only [hs.1, hleft, homegaZeta, hzeta], hs.2⟩
  let e := closed.restrict hinterval ordConnected_Icc (Subset.refl E.carrier)
  have hclock' : MapsTo (fun u : ℝ => u / k) (Icc (-1 : ℝ) 0)
      (Icc (-(1 + omega)) 0) := by
    intro u hu
    have h : u / k ∈ Icc (-1 - omega) 0 := hclock hu
    exact ⟨by linarith only [h.1], h.2⟩
  have hscale : E.scale⁻¹ ^ 2 = q * k := by
    rw [E.scale_eq_scalar, show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring,
      Real.rpow_neg E.scalar_center_pos.le, ← Real.sqrt_eq_rpow, inv_inv,
      Real.sq_sqrt E.scalar_center_pos.le, hconnection, hcenter]
    exact hqk.symm
  refine ⟨E, hepsilon, hconnection, hcenter, hcarrier, hmap, hinverse, hnegative,
    hscale, hk, hclock', e, ?_, ?_, ?_, ?_⟩
  · intro s hs hs' z hz
    exact hold s hs (hinterval hs') z hz
  · intro hs z
    exact hzero (hinterval hs) z
  · intro hs z hz v w
    exact source_initial_closed_zero_metric hT i e hs
      (fun z => hzero (hinterval hs) z) (hnegative hz) v w
  · apply hfamily.congr_cylinder
    intro u hu z hz v w
    have hrawMem := hclock' hu
    have hbigMem := hinterval hrawMem
    have hzE : z.2 ∈ Ioo (-E.epsilon⁻¹) E.epsilon⁻¹ := by
      simpa only [hepsilon] using hz
    have hzMap : N.coordinate_map (neckAxialSpaceMap 1 c z) ∈ E.carrier := by
      have h := M36.neck_coordinate_mem E z ⟨mem_univ _, hzE⟩
      simpa only [hmap, Function.comp_apply] using h
    have ha : 1 * z.2 + c ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
      simpa only [one_mul] using hdomain z.2 hz
    have htensor := source_initial_older_tensor_on_closed_cylinder hT i old D closed
      E.carrier_open hnegative hpast hold hzero (u / k) hbigMem
      (neckAxialSpaceMap 1 c z) hzMap
      (neckAxialLinearMap 1 v) (neckAxialLinearMap 1 w)
    rw [hmap, source_initial_cylinder_affine_pullback N e 1 c (u / k) hrawMem ha]
    apply congrArg (k * ·)
    change sourceInitialOlderTensor old D (u / k) (neckAxialSpaceMap 1 c z)
      (neckAxialLinearMap 1 v) (neckAxialLinearMap 1 w) = _
    exact htensor.trans (by
      simp only [surgeryCylinderPullback, dif_pos hbigMem, dif_pos hrawMem]
      rfl)

end PoincareConjecture.M47
