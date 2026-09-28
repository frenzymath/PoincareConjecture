import PoincareConjecture.Proofs.M47.CanonicalCapNearbyErrors
import PoincareConjecture.Proofs.M47.CanonicalNeckClockBuffer

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

open Proofs.M47

theorem standard_evolving_neck_birth_gap
    {g0 : StandardInitialMetric} {G : MaximalStandardCapFlow g0}
    {atlas : StandardCylinderAtlas} {v gamma : ℝ} {z : StandardCapSpace}
    (N : StandardEvolvingNeck atlas G v gamma z (Ioc (-(1 + gamma)) 0)) :
    0 < v - ((G.connection v).scalarCurvature z)⁻¹ := by
  let q := (G.connection v).scalarCurvature z
  have hq : 0 < q := N.scalar_pos
  have hu : -(1 + gamma / 2) ∈ Ioc (-(1 + gamma)) 0 := by
    constructor <;> linarith only [N.epsilon_pos]
  have htime : 0 ≤ v + (-(1 + gamma / 2)) / q := (N.interval_survival _ hu).1
  have hmargin : 0 < (gamma / 2) / q := div_pos (half_pos N.epsilon_pos) hq
  have heq : v - q⁻¹ = (v + (-(1 + gamma / 2)) / q) + (gamma / 2) / q := by
    simp only [div_eq_mul_inv]
    ring
  change 0 < v - q⁻¹
  rw [heq]
  exact add_pos_of_nonneg_of_pos htime hmargin

theorem exists_source_evolving_clock_tolerance
    {v q nu : ℝ} (hq : 0 < q) (hgap : 0 < v - q⁻¹) (hnu : 0 < nu) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ s rho : ℝ,
      |s - v| < delta → |rho - q| < delta →
      0 < rho ∧ ∀ u ∈ Icc (-1 : ℝ) 0,
        s + u / rho ∈ Ioc 0 s ∧
          |s + u / rho - (v + u / q)| < nu := by
  have hnear := eventually_normalized_neck_clock_in_buffer
    (p0 := (v, q)) (T := fun p : ℝ × ℝ => p.1)
    (R := fun p : ℝ × ℝ => p.2) continuousAt_fst continuousAt_snd hq hgap
    (show v < v + 1 by linarith) hnu
  obtain ⟨delta, hdelta, hball⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨delta, hdelta, ?_⟩
  intro s rho hs hrho
  have hmem : (s, rho) ∈ Metric.ball (v, q) delta := by
    simpa only [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, max_lt_iff] using ⟨hs, hrho⟩
  obtain ⟨hpositive, htimes⟩ := hball hmem
  refine ⟨hpositive, ?_⟩
  intro u hu
  obtain ⟨hwindow, hclose⟩ := htimes u hu
  refine ⟨⟨hwindow.1, ?_⟩, hclose⟩
  exact add_le_of_nonpos_right (div_nonpos_of_nonpos_of_nonneg hu.2 hpositive.le)

theorem exists_actualCap_evolving_clock_tolerance
    {g0 : StandardInitialMetric} (standard : RepairedStandardCapExistenceData g0)
    {theta A v gamma nu : ℝ} (htheta : theta < 1) (hA : 0 < A)
    (hv : v ∈ Icc 0 theta) {z : StandardCapSpace}
    (N : StandardEvolvingNeck standard.atlas standard.flow v gamma z
      (Ioc (-(1 + gamma)) 0))
    (hz : z ∈ g0.metric.ball 0 A) (hnu : 0 < nu) :
    ∃ eta0 delta : ℝ, ∃ V : Set StandardCapSpace,
      0 < eta0 ∧ 0 < delta ∧ IsOpen V ∧ z ∈ V ∧ V ⊆ g0.metric.ball 0 A ∧
      ∀ (F : SurgeryFlowData.{u}) (_hinitial : F.standard_initial = g0)
        (S : MaximalStandardCapFlow F.standard_initial), HEq S standard.flow →
      ∀ (t : ℝ) (hT : t ∈ F.surgery_times) (_hn : Nonempty (F.slice t).carrier)
        (i : Fin (F.event t hT).cap_count) (J : Set ℝ) (U : Set (F.slice t).carrier)
        (e : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2) J U)
        (initial : SurgeryCapInitialComparison F t hT i A)
        (eta : ℝ), 0 < eta → eta ≤ eta0 →
      ∀ (_comparison : SurgeryCapFamilyComparison F S A eta e initial.chart)
        (_hh : 0 < F.parameters.h t) (s : ℝ) (hs : s ∈ J),
      s ≤ theta → |s - v| < delta → ∀ z' ∈ V,
      let h := F.parameters.h t
      let b := t + s / (h⁻¹ ^ 2)
      let p := e.forward s hs (initial.chart z')
      let Q := (F.connection b).scalarCurvature p
      let rho := h ^ 2 * Q
      let q := (standard.flow.connection v).scalarCurvature z
      0 < Q ∧ |rho - q| < nu ∧
        0 < (standard.flow.connection v).scalarCurvature z' ∧
        |(standard.flow.connection v).scalarCurvature z' - q| < nu ∧
        ∀ u ∈ Icc (-1 : ℝ) 0,
          s + u / rho ∈ Ioc 0 s ∧
          |s + u / rho - (v + u / q)| < nu ∧
          b + u / Q = t + (s + u / rho) / (h⁻¹ ^ 2) := by
  let q := (standard.flow.connection v).scalarCurvature z
  have hq : 0 < q := N.scalar_pos
  obtain ⟨dclock, hdclock, hclock⟩ := exists_source_evolving_clock_tolerance
    hq (standard_evolving_neck_birth_gap N) hnu
  let xi := min (min dclock nu) (q / 2)
  have hxi : 0 < xi := lt_min (lt_min hdclock hnu) (half_pos hq)
  have hxiClock : xi ≤ dclock := (min_le_left _ _).trans (min_le_left _ _)
  have hxiNu : xi ≤ nu := (min_le_left _ _).trans (min_le_right _ _)
  have hxiQ : xi ≤ q / 2 := min_le_right _ _
  obtain ⟨eta0, dtime, heta0, hdtime, hanalytic⟩ :=
    exists_actualCap_nearby_analytic_tolerance standard htheta hA (half_pos hxi)
  let V := g0.metric.ball 0 A ∩
    {x | |(standard.flow.connection v).scalarCurvature x - q| < xi / 2}
  have hball : IsOpen (g0.metric.ball 0 A) := by
    rw [M36.standard_ball_eq_euclidean g0 hA]
    exact Metric.isOpen_ball
  have hV : IsOpen V := hball.inter
    (isOpen_lt (((M34.contMDiff_scalarCurvature
      (standard.flow.connection v)).continuous.sub continuous_const).abs) continuous_const)
  have hzV : z ∈ V := by
    refine ⟨hz, ?_⟩
    simpa only [mem_ofPred_eq, q, sub_self, abs_zero] using half_pos hxi
  refine ⟨eta0, min dtime dclock, V, heta0, lt_min hdtime hdclock, hV, hzV,
    inter_subset_left, ?_⟩
  intro F hinitial S hS t hT hn i J U e initial eta heta hetaSmall
    comparison hh s hs hst hnear z' hz'
  have hnearTime : |s - v| < dtime := hnear.trans_le (min_le_left _ _)
  have hnearClock : |s - v| < dclock := hnear.trans_le (min_le_right _ _)
  have hzSource : z' ∈ F.standard_initial.metric.ball 0 A := hinitial.symm ▸ hz'.1
  have htuple := hanalytic F hinitial S hS t hT hn i J U e initial eta heta hetaSmall
    comparison hh s hs hst v hv hnearTime z' hzSource
  let h := F.parameters.h t
  let b := t + s / (h⁻¹ ^ 2)
  let p := e.forward s hs (initial.chart z')
  let Q := (F.connection b).scalarCurvature p
  let rho := h ^ 2 * Q
  have hphysical : |rho - (standard.flow.connection v).scalarCurvature z'| ≤ xi / 2 := by
    cases hinitial
    cases hS
    exact (show |rho - (standard.flow.connection v).scalarCurvature z'| ≤
      ‖(h ^ 2 * Q,
          h ^ 3 * scalarGradientNorm (F.metric b) (F.connection b) p,
          h ^ 4 * ((F.connection b).laplacian (F.connection b).scalarCurvature p +
            2 * (F.connection b).ricciNormSq p)) -
        ((standard.flow.connection v).scalarCurvature z',
          scalarGradientNorm (standard.flow.metric v) (standard.flow.connection v) z',
          (standard.flow.connection v).laplacian
            (standard.flow.connection v).scalarCurvature z' +
            2 * (standard.flow.connection v).ricciNormSq z')‖ by
        exact le_max_left _ _).trans htuple
  have hmodel : |(standard.flow.connection v).scalarCurvature z' - q| < xi / 2 := hz'.2
  have hrho : |rho - q| < xi :=
    (abs_sub_le rho ((standard.flow.connection v).scalarCurvature z') q).trans_lt
      (by linarith only [hphysical, hmodel])
  obtain ⟨hrhoPos, htimes⟩ := hclock s rho hnearClock (hrho.trans_le hxiClock)
  have hQ : 0 < Q := (mul_pos_iff_of_pos_left (sq_pos_of_pos hh)).mp hrhoPos
  have hmodelPos : 0 < (standard.flow.connection v).scalarCurvature z' := by
    have hleft := (abs_lt.mp hmodel).1
    linarith only [hleft, hq, hxiQ]
  refine ⟨hQ, hrho.trans_le hxiNu, hmodelPos,
    hmodel.trans_le (by linarith only [hxiNu, hxi.le]), ?_⟩
  intro u hu
  obtain ⟨hwindow, hclose⟩ := htimes u hu
  refine ⟨hwindow, hclose, ?_⟩
  field_simp [hh.ne', hQ.ne']
  ring

end PoincareConjecture.M47
