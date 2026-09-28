import PoincareConjecture.Proofs.M47.BlowupControlsSourceRecentFamily
import PoincareConjecture.Proofs.M47.CanonicalCapNearbyErrors
import PoincareConjecture.Proofs.M47.BlowupControlsSourceRestriction











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

open Proofs.M47

private theorem initialRestricted_comparison
    {F : SurgeryFlowData.{u}} {S : MaximalStandardCapFlow F.standard_initial}
    {T A a eta : ℝ} {hT : T ∈ F.surgery_times}
    [Nonempty (F.slice T).carrier] {i : Fin (F.event T hT).cap_count}
    {J : Set ℝ} {U : Set (F.slice T).carrier}
    (e : SurgeryFlowCylinder F (F.slice T) T ((F.parameters.h T)⁻¹ ^ 2) J U)
    (initial : SurgeryCapInitialComparison F T hT i A)
    (comparison : SurgeryCapFamilyComparison F S A eta e initial.chart)
    (ha : 0 < a) (haa : a ≤ A)
    (himage : initial.chart '' F.standard_initial.metric.ball 0 a ⊆ U) :
    ∃ small : SurgeryCapInitialComparison F T hT i a,
      small.chart = initial.chart ∧ SurgeryCapFamilyComparison F S a eta
        (e.restrict Subset.rfl e.interval_connected himage) small.chart := by
  have hball : F.standard_initial.metric.ball 0 a ⊆ F.standard_initial.metric.ball 0 A := by
    intro x hx
    exact hx.trans_le (ENNReal.ofReal_le_ofReal haa)
  let small : SurgeryCapInitialComparison F T hT i a := {
    A_pos := ha
    chart := initial.chart
    inverse := initial.inverse
    chart_smooth := initial.chart_smooth.mono hball
    inverse_smooth := initial.inverse_smooth
    left_inverse := initial.left_inverse.mono hball
    right_inverse := initial.right_inverse
    tip_eq := initial.tip_eq
    local_metric_link := by
      obtain ⟨kappa, hkappa, Q, hdelta, hcontain, hmap⟩ := initial.local_metric_link
      exact ⟨kappa, hkappa, Q, hdelta, hball.trans hcontain,
        fun x hx => hmap x (hball hx)⟩ }
  obtain ⟨bound, hbound, hlifetime, hinterval, _himage, hjet⟩ := comparison
  exact ⟨small, rfl, bound, hbound, hlifetime, hinterval, rfl,
    fun s hs x hx => hjet s hs x (hball hx)⟩




theorem exists_source_initial_nearby_family
    {g0 : StandardInitialMetric} (standard : RepairedStandardCapExistenceData g0)
    {theta A0 v gamma : ℝ} (htheta : theta < 1) (hA0 : 0 < A0)
    (hv : v ∈ Icc 0 theta) {z : StandardCapSpace}
    (N : StandardEvolvingNeck standard.atlas standard.flow v gamma z
      (Icc (-v * (standard.flow.connection v).scalarCurvature z) 0))
    (hRlo : (3 / 4 : ℝ) < (standard.flow.connection v).scalarCurvature z)
    (hRhi : (standard.flow.connection v).scalarCurvature z < (5 / 2 : ℝ))
    (E : EpsilonNeck (standard.flow.metric v)) (heps : E.epsilon = 2 * gamma)
    (hmap : E.coordinate_map = N.patch.coordinate) (hcenter : E.center = z)
    (hsource : E.carrier ⊆ g0.metric.ball 0 A0) :
    ∃ eta0 delta : ℝ, ∃ V : Set StandardCapSpace,
      0 < eta0 ∧ 0 < delta ∧ IsOpen V ∧ z ∈ V ∧ V ⊆ E.carrier ∧
      (∀ x ∈ V, |(E.coordinate_inverse x).2| < 1) ∧
      ∀ A : ℝ, A0 ≤ A →
      ∀ (F : SurgeryFlowData.{u}) (_hinitial : F.standard_initial = g0)
        (S : MaximalStandardCapFlow F.standard_initial), HEq S standard.flow →
      ∀ (T : ℝ) (hT : T ∈ F.surgery_times) (_hn : Nonempty (F.slice T).carrier)
        (i : Fin (F.event T hT).cap_count) (J : Set ℝ) (U : Set (F.slice T).carrier)
        (e : SurgeryFlowCylinder F (F.slice T) T ((F.parameters.h T)⁻¹ ^ 2) J U)
        (initial : SurgeryCapInitialComparison F T hT i A)
        (eta : ℝ), 0 < eta → eta ≤ eta0 →
      ∀ (comparison : SurgeryCapFamilyComparison F S A eta e initial.chart)
        (hh : 0 < F.parameters.h T) (s : ℝ) (hs : s ∈ J), s ∈ Icc 0 theta →
      Icc 0 s ⊆ J → |s - v| < delta → ∀ x ∈ V,
      let Q := (F.connection (T + s / ((F.parameters.h T)⁻¹ ^ 2))).scalarCurvature
        (e.forward s hs (initial.chart x))
      let H := Q / ((F.parameters.h T)⁻¹ ^ 2)
      (1 / 2 : ℝ) < H ∧ H < 3 ∧
        ∃ hclock : MapsTo (fun u : ℝ => s + u / H) (Icc (-H * s) 0) J,
          RoundCylinderFamilyClose (3 * gamma) (Icc (-H * s) 0)
            (sourceRecentCapTensor e initial comparison hh E s H
              (E.coordinate_inverse x).2 hclock) := by
  let R := (standard.flow.connection v).scalarCurvature z
  obtain ⟨etaF, deltaF, hetaF, hdeltaF, family⟩ :=
    exists_actualCap_initial_recent_family_tolerance standard htheta hA0 hv.2 N E heps hmap hsource
  let nu := min deltaF (1 / 4)
  have hnu : 0 < nu := lt_min hdeltaF (by norm_num)
  have hnuF : nu ≤ deltaF := min_le_left _ _
  have hnuQuarter : nu ≤ 1 / 4 := min_le_right _ _
  obtain ⟨etaA, deltaA, hetaA, hdeltaA, analytic⟩ :=
    exists_actualCap_nearby_analytic_tolerance standard htheta hA0 (half_pos hnu)
  let radius := min deltaF 1
  have hradius : 0 < radius := lt_min hdeltaF zero_lt_one
  let V := E.region (-radius) radius ∩
    {x | |(standard.flow.connection v).scalarCurvature x - R| < nu / 2}
  have hV : IsOpen V := (E.region_isOpen _ _).inter
    (isOpen_lt (((M34.contMDiff_scalarCurvature
      (standard.flow.connection v)).continuous.sub continuous_const).abs) continuous_const)
  have hzE : z ∈ E.carrier := hcenter ▸ E.central_sphere_subset E.center_on_central_sphere
  have hzV : z ∈ V := by
    refine ⟨⟨hzE, ?_⟩, ?_⟩
    · have hz0 : (E.coordinate_inverse z).2 = 0 :=
        (E.mem_central_sphere_iff_of_mem hzE).mp (hcenter ▸ E.center_on_central_sphere)
      rw [hz0]
      exact ⟨neg_neg_of_pos hradius, hradius⟩
    · simpa only [mem_ofPred_eq, R, sub_self, abs_zero] using half_pos hnu
  refine ⟨min etaF etaA, min deltaF deltaA, V, lt_min hetaF hetaA,
    lt_min hdeltaF hdeltaA, hV, hzV, fun x hx => hx.1.1,
    fun x hx => (abs_lt.mpr hx.1.2).trans_le (min_le_right _ _), ?_⟩
  intro A hA F hinitial S hS T hT hn i J U e initial eta heta hetaSmall comparison hh
    s hs hst hJ hnear x hx Q H
  have hball : F.standard_initial.metric.ball 0 A0 ⊆ F.standard_initial.metric.ball 0 A := by
    intro y hy
    exact hy.trans_le (ENNReal.ofReal_le_ofReal hA)
  have himage : initial.chart '' F.standard_initial.metric.ball 0 A0 ⊆ U := by
    rw [← (comparison.choose_spec.2.2.2.1 :
      initial.chart '' F.standard_initial.metric.ball 0 A = U)]
    exact image_mono hball
  obtain ⟨small, hchart, hsmall⟩ := initialRestricted_comparison e initial comparison hA0 hA himage
  let esmall := e.restrict Subset.rfl e.interval_connected himage
  have hxSource : x ∈ F.standard_initial.metric.ball 0 A0 := hinitial.symm ▸ hsource hx.1.1
  have htuple := analytic F hinitial S hS T hT hn i J _ esmall small eta heta
    (hetaSmall.trans (min_le_right _ _)) hsmall hh s hs hst.2 v hv
      (hnear.trans_le (min_le_right _ _)) x hxSource
  have hphysical : |H - (standard.flow.connection v).scalarCurvature x| ≤ nu / 2 := by
    have hfirst := (norm_fst_le _).trans htuple
    simp only [Prod.fst_sub, Real.norm_eq_abs, hchart] at hfirst
    have hscale : Q / ((F.parameters.h T)⁻¹ ^ 2) = (F.parameters.h T) ^ 2 * Q := by
      field_simp
    change |H - (standard.flow.connection v).scalarCurvature x| ≤ nu / 2
    rw [show H = (F.parameters.h T) ^ 2 * Q from hscale]
    cases hinitial
    cases hS
    exact hfirst
  have hmodel : |(standard.flow.connection v).scalarCurvature x - R| < nu / 2 := hx.2
  have hHR : |H - R| < nu :=
    (abs_sub_le H ((standard.flow.connection v).scalarCurvature x) R).trans_lt
      (by linarith only [hphysical, hmodel])
  have hHlo : (1 / 2 : ℝ) < H := by
    have hh := (abs_lt.mp hHR).1
    change (3 / 4 : ℝ) < R at hRlo
    linarith only [hh, hRlo, hnuQuarter]
  have hHhi : H < 3 := by
    have hh := (abs_lt.mp hHR).2
    change R < (5 / 2 : ℝ) at hRhi
    linarith only [hh, hRhi, hnuQuarter]
  have hc : |(E.coordinate_inverse x).2| < deltaF :=
    (abs_lt.mpr hx.1.2).trans_le (min_le_left _ _)
  obtain ⟨_hH, hclock, hfamily⟩ := family F hinitial S hS T hT hn i J _ esmall small eta heta
    (hetaSmall.trans (min_le_left _ _)) hsmall hh s H (E.coordinate_inverse x).2 hst hJ
      (hnear.trans_le (min_le_left _ _)) (hHR.trans_le hnuF) hc
  refine ⟨hHlo, hHhi, hclock, ?_⟩
  apply hfamily.congr_cylinder
  intro u hu p _hp a b
  have hphi : (actualCapSliceChart esmall small hsmall (s + u / H) (hclock hu) :
      StandardCapSpace → (F.slice (T + (s + u / H) / ((F.parameters.h T)⁻¹ ^ 2))).carrier) =
      actualCapSliceChart e initial comparison (s + u / H) (hclock hu) := by
    funext y
    simp only [actualCapSliceChart_apply, hchart]
    rfl
  simp only [sourceRecentCapTensor, dif_pos hu, hphi]

end PoincareConjecture.M47
