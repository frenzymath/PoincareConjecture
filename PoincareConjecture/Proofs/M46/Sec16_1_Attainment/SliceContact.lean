import PoincareConjecture.Proofs.M46.Sec16_1_Attainment.CappedSliceValue
import PoincareConjecture.Proofs.M46.Sec16_1_LGeometry.Prop16_4_SliceIndex
import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Cor6_67_InteriorSurvival










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M46

variable {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport 3 X time I}
  {T start : ℝ} {x : G.Point}



theorem cappedSliceAction_active_contact
    (hCoordinates : M12MetricPredecessors.{0} 3)
    (hM04 : RicciFlowCurvatureTheory.{0})
    (hM12 : GeneralizedRicciGaugeTheory.{u} 3)
    (LG : GeneralizedLGeometryConclusion G)
    (E : M14ExponentialFamily G T x) (C : ActionConfinement G T start x)
    (hstrip : Icc start T ⊆ I.domain)
    {b c : ℝ} (hb : 0 < b) (hbc : b < c) (hc : c ^ 2 ≤ T - start)
    (hactive : cappedSliceAction G T x C.barrier b < C.barrier) :
    ∃ phi : ℝ → ℝ, ∃ d : ℝ, HasDerivAt phi d b ∧
      phi b = cappedSliceAction G T x C.barrier b / (2 * b) ∧
      (∀ᶠ s in 𝓝[>] b, cappedSliceAction G T x C.barrier s / (2 * s) ≤ phi s) ∧
      d ≤ (3 - 2 * (cappedSliceAction G T x C.barrier b / (2 * b))) / b := by
  have hcpos := hb.trans hbc
  have hbStart : b ^ 2 ≤ T - start :=
    ((sq_le_sq₀ hb.le hcpos.le).mpr hbc.le).trans hc
  obtain ⟨Z, hZ, hp, hact⟩ := cappedSliceAction_exponential hM04 hM12 LG E C hb hbStart hactive
  let p := E.path Z b hZ hb
  let R := E.square_path Z b hZ hb
  have hpact : M14BackwardLAction G p = cappedSliceAction G T x C.barrier b :=
    (E.action_eq Z b hZ hb).symm.trans hact
  have hB : M14BackwardLAction G p < C.barrier := hpact.trans_lt hactive
  have hmin (z : G.Point) (q : M14BackwardPath G T 0 (b ^ 2) x z)
      (_hq : M14BackwardLAction G q < C.barrier) :
      M14BackwardLAction G p ≤ M14BackwardLAction G q := hpact.le.trans
    ((cappedSliceAction_alternative hM04 hM12 LG E C hb hbStart).2.1 z q)
  have hvelocity : R.horizontal_velocity b = 0 := by
    have h := sliceMinimum_terminal_velocity_eq_zero hCoordinates hM12 (R := R) hB hp hmin
    have htransport : ∀ s, s = Real.sqrt (b ^ 2) → R.horizontal_velocity s = 0 := by
      rintro s rfl
      exact h
    exact htransport b (Real.sqrt_sq hb.le).symm
  have hindex := sliceMinimum_scalar_reducedLength_le_dimension
    hCoordinates hM04 hM12 R hB hp hmin
  rw [Real.sqrt_sq hb.le, ← E.action_eq Z b hZ hb] at hindex
  have hphysical : T - b ^ 2 ∈ interior I.domain := by
    apply interior_mono hstrip
    rw [interior_Icc]
    constructor <;> nlinarith [sq_pos_of_pos hb]
  obtain ⟨r, hbr, hZr⟩ := exists_surviving_extension_at_interior E hb hZ hphysical
  have hdomain : {s : ℝ | (Z, s) ∈ E.domain} ∈ 𝓝 b := by
    apply mem_of_superset (Ioo_mem_nhds hb hbr)
    intro s hs
    exact (E.maximal_lifetime Z).out (E.domain_zero Z) hZr ⟨hs.1.le, hs.2.le⟩
  have hder := (E.action_time_derivative Z b hZ hb).hasDerivAt hdomain
  change HasDerivAt (fun s => E.action Z s)
    ((1 / 2 : ℝ) * G.spacetime.horizontalMetric.inner (R.curve b)
      (R.horizontal_velocity b) (R.horizontal_velocity b) +
      2 * b ^ 2 * horizontalScalarCurvature G.leafwise (R.curve b)) b at hder
  simp only [hvelocity, map_zero, mul_zero, zero_add] at hder
  let rho := horizontalScalarCurvature G.leafwise (R.curve b)
  let ell := E.action Z b / (2 * b)
  have hquot : HasDerivAt (fun s => E.action Z s / (2 * s)) (b * rho - ell / b) b := by
    convert hder.div ((hasDerivAt_id b).const_mul 2) (by positivity : 2 * b ≠ 0) using 1
      <;> try rfl
    dsimp [rho, ell]
    field_simp [hb.ne']
  refine ⟨fun s => E.action Z s / (2 * s), b * rho - ell / b, hquot,
    by change E.action Z b / (2 * b) = _; rw [hact], ?_, ?_⟩
  · have hnear : ∀ᶠ s in 𝓝[>] b, s ∈ Ioo 0 c :=
      mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds hb hbc)
    have hsurv : ∀ᶠ s in 𝓝[>] b, (Z, s) ∈ E.domain :=
      mem_nhdsWithin_of_mem_nhds hdomain
    filter_upwards [hnear, hsurv] with s hs hsZ
    have hsStart := ((sq_le_sq₀ hs.1.le hcpos.le).mpr hs.2.le).trans hc
    have hm := (cappedSliceAction_alternative hM04 hM12 LG E C hs.1 hsStart).2.1
      (E.gamma Z s) (E.path Z s hsZ hs.1)
    rw [← E.action_eq Z s hsZ hs.1] at hm
    exact div_le_div_of_nonneg_right hm (mul_nonneg (by norm_num) hs.1.le)
  · rw [← hact]
    apply (le_div_iff₀ hb).mpr
    have hcancel : (b * rho - ell / b) * b = b ^ 2 * rho - ell := by
      field_simp
    rw [hcancel]
    change b ^ 2 * rho + ell ≤ 3 at hindex
    change b ^ 2 * rho - ell ≤ 3 - 2 * ell
    linarith

end PoincareConjecture.Proofs.M46
