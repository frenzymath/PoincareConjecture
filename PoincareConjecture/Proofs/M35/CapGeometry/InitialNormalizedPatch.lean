import PoincareConjecture.Proofs.M35.CapGeometry.InitialAxialJets
import PoincareConjecture.Proofs.M35.CapGeometry.InitialAxialScale
import PoincareConjecture.Proofs.M35.CapGeometry.InitialClockScalar
import PoincareConjecture.Definitions.M35StandardCapUniqueness

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35

local notation "V" => StandardCapSpace

def InitialNormalizedPatchComparison {g₀ : StandardInitialMetric}
    (E : RepairedStandardCapExistenceData g₀) (t epsilon : ℝ) (he : 0 < epsilon)
    {d : ℝ} {x : V} (N : StandardCylinderPatch d⁻¹ x) : Prop :=
  let Q := (E.flow.connection t).scalarCurvature x
  let c := (Real.sqrt Q)⁻¹
  ∃ hc : 0 < c, c < 2 ∧ ∃ hcl : c * epsilon⁻¹ ≤ d⁻¹,
    StandardSpacetimeCylinderClose E.atlas E.flow.metric epsilon t Q (Icc (-t * Q) 0)
      (N.axialRescale c epsilon⁻¹ hc (inv_pos.mpr he) hcl)

theorem exists_initial_normalized_patch_comparison {g₀ : StandardInitialMetric}
    (E : RepairedStandardCapExistenceData g₀) {theta epsilon : ℝ}
    (htheta : theta ∈ Ico 0 E.flow.base.lifetime) (he : 0 < epsilon) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ d : ℝ, 0 < d → d ≤ delta →
      ∀ (x : V) (N : StandardCylinderPatch d⁻¹ x),
        StandardSpacetimeCylinderClose E.atlas E.flow.metric d 0 1 (Icc 0 theta) N →
          ∀ t ∈ Icc 0 theta, InitialNormalizedPatchComparison E t epsilon he N := by
  classical
  have htone : theta < 1 := E.lifetime_one ▸ htheta.2
  obtain ⟨dscale, hdscale, hscale⟩ := exists_initial_axial_scale_control htone he
  by_contra hnone
  push Not at hnone
  choose d hd hdmax x N hfamily t ht hbad using fun k : ℕ =>
    hnone (min dscale (1 / ((k : ℝ) + 1))) (lt_min hdscale (by positivity))
  let Q (k : ℕ) := (E.flow.connection (t k)).scalarCurvature (x k)
  let c (k : ℕ) := (Real.sqrt (Q k))⁻¹
  have hfamily' (k : ℕ) : RoundCylinderFamilyClose (d k) (Icc 0 theta)
      (fun v => roundCylinderPullback (E.flow.metric v) (N k).coordinate) := by
    simpa only [StandardSpacetimeCylinderClose, div_one, zero_add, one_mul] using hfamily k
  have hstatic (k : ℕ) {v : ℝ} (hv : v ∈ Icc 0 theta) :
      RoundCylinderClose (d k) v (roundCylinderPullback (E.flow.metric v) (N k).coordinate) :=
    ⟨(hfamily' k).1 v hv, (hfamily' k).2.choose, (hfamily' k).2.choose_spec.1,
      (hfamily' k).2.choose_spec.2 v hv⟩
  have hcontrols (k : ℕ) := hscale (d k) (hd k)
    ((hdmax k).trans (min_le_left _ _)) (t k) (ht k)
    (E.flow.metric (t k)) (E.flow.connection (t k)) (x k) (N k) (hstatic k (ht k))
  have hQlo (k : ℕ) : 1 / 2 < Q k := (hcontrols k).1
  have hQhi (k : ℕ) : Q k < 3 / (2 * (1 - theta)) := (hcontrols k).2.1
  have hQ (k : ℕ) : 0 < Q k := (by norm_num : (0 : ℝ) < 1 / 2).trans (hQlo k)
  have hc (k : ℕ) : 0 < c k := (hcontrols k).2.2.1
  have hcsmall (k : ℕ) : c k < 2 := (hcontrols k).2.2.2.1
  have hcl (k : ℕ) : c k * epsilon⁻¹ ≤ (d k)⁻¹ := (hcontrols k).2.2.2.2.1
  have hdegree (k : ℕ) : ⌊epsilon⁻¹⌋₊ ≤ ⌊(d k)⁻¹⌋₊ := (hcontrols k).2.2.2.2.2
  let M k := (N k).axialRescale (c k) epsilon⁻¹ (hc k) (inv_pos.mpr he) (hcl k)
  let B (k : ℕ) (u : ℝ) : RoundCylinderTwoTensor := fun z a b => Q k *
    roundCylinderPullback (E.flow.metric (t k + u / Q k)) (M k).coordinate z a b
  have hbadpoint (k : ℕ) : ∃ u ∈ Icc (-t k * Q k) 0,
      ∃ z : RoundCylinderSpace, z.2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹ ∧
        epsilon ^ 2 / 2 < roundCylinderJetErrorSquared u (B k u) ⌊epsilon⁻¹⌋₊ z := by
    by_contra hn
    push Not at hn
    apply hbad k
    refine ⟨hc k, hcsmall k, hcl k, ?_, epsilon ^ 2 / 2,
      by nlinarith only [sq_pos_of_pos he], ?_⟩
    · intro u _hu
      exact roundCylinderPullback_scaled_smoothOn _ (M k).coordinate epsilon
        (Q k) (M k).coordinate_smooth
    · exact hn
  choose u hu z hz herror using hbadpoint
  let H := 3 / (2 * (1 - theta))
  have hucompact (k : ℕ) : u k ∈ Icc (-theta * H) 0 := by
    have hprod : t k * Q k ≤ theta * H :=
      mul_le_mul (ht k).2 (hQhi k).le (hQ k).le htheta.1
    exact ⟨by linarith only [hprod, (hu k).1], (hu k).2⟩
  have hzcompact (k : ℕ) : (z k).2 ∈ Icc (-epsilon⁻¹) epsilon⁻¹ :=
    ⟨(hz k).1.le, (hz k).2.le⟩
  obtain ⟨p₀, hp₀, phi, hphi, hlim⟩ :=
    (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).tendsto_subseq
      (fun k => show (t k, u k, (z k).2) ∈
        Icc 0 theta ×ˢ (Icc (-theta * H) 0 ×ˢ Icc (-epsilon⁻¹) epsilon⁻¹) from
          ⟨ht k, hucompact k, hzcompact k⟩)
  have htlim : Tendsto (t ∘ phi) atTop (𝓝 p₀.1) :=
    (continuous_fst.tendsto p₀).comp hlim
  have hulim : Tendsto (u ∘ phi) atTop (𝓝 p₀.2.1) :=
    ((continuous_fst.comp continuous_snd).tendsto p₀).comp hlim
  have hslim : Tendsto (fun k => (z (phi k)).2) atTop (𝓝 p₀.2.2) :=
    ((continuous_snd.comp continuous_snd).tendsto p₀).comp hlim
  have hdlim : Tendsto d atTop (𝓝 0) :=
    squeeze_zero (fun k => (hd k).le)
      (fun k => (hdmax k).trans (min_le_right _ _))
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hnormal := initial_cylinder_center_normalization_tendsto htone d t
    (fun k => E.flow.metric (t k)) (fun k => E.flow.connection (t k)) x N hd ht
    (fun k => hstatic k (ht k)) hdlim
  have hQlim : Tendsto (Q ∘ phi) atTop (𝓝 (1 / (1 - p₀.1))) :=
    initial_cylinder_center_scalar_tendsto htone (d ∘ phi) (t ∘ phi)
      (fun k => E.flow.metric (t (phi k))) (fun k => E.flow.connection (t (phi k)))
      (x ∘ phi) (fun k => N (phi k)) (fun k => hd (phi k)) (fun k => ht (phi k))
      (fun k => hstatic (phi k) (ht (phi k))) (hdlim.comp hphi.tendsto_atTop)
      (hp₀.1.2.trans_lt htone) htlim
  have hclim : Tendsto (c ∘ phi) atTop
      (𝓝 ((Real.sqrt (1 / (1 - p₀.1)))⁻¹)) :=
    ((Real.continuous_sqrt.tendsto _).comp hQlim).inv₀
      (Real.sqrt_pos.mpr (one_div_pos.mpr (sub_pos.mpr (hp₀.1.2.trans_lt htone)))).ne'
  let v (k : ℕ) := t k + u k / Q k
  have hv (k : ℕ) : v k ∈ Icc 0 theta := (initial_affine_clock (ht k) (hQ k) (hu k)).1
  have hunit (k : ℕ) : Q k * c k ^ 2 = 1 := by
    dsimp only [c]
    rw [inv_pow, Real.sq_sqrt (hQ k).le, mul_inv_cancel₀ (hQ k).ne']
  have hclockerror : Tendsto (fun k => Q (phi k) * (1 - v (phi k)) -
      (1 - u (phi k))) atTop (𝓝 0) := by
    have hh := (hnormal.comp hphi.tendsto_atTop).sub_const 1
    simp only [sub_self] at hh
    apply hh.congr'
    exact Eventually.of_forall fun k =>
      (initial_affine_clock (ht (phi k)) (hQ (phi k)) (hu (phi k))).2.symm
  have hjet := initial_axial_jetError_tendsto_zero (d ∘ phi) (u ∘ phi) (v ∘ phi)
    (Q ∘ phi) (c ∘ phi) (fun k => (z (phi k)).2)
    (fun k => E.flow.metric (v (phi k))) (x ∘ phi) (fun k => N (phi k)) epsilon he
    (fun k => hc (phi k)) (fun k => hcl (phi k)) (fun k => (z (phi k)).1)
    ⌊epsilon⁻¹⌋₊ (fun k => hd (phi k))
    (fun k => (by norm_num : (-1 : ℝ) ≤ 0).trans (hv (phi k)).1)
    (fun k => (hv (phi k)).2.trans_lt htone) (fun k => hz (phi k))
    (fun k => hstatic (phi k) (hv (phi k))) (fun k => hdegree (phi k))
    (fun k => hunit (phi k)) (fun k => (hu (phi k)).2.trans_lt zero_lt_one)
    (hp₀.2.1.2.trans_lt zero_lt_one) (hdlim.comp hphi.tendsto_atTop) hulim hQlim hclim
    hslim hclockerror
  obtain ⟨k, hk⟩ := (hjet.eventually
    (eventually_lt_nhds (by positivity : (0 : ℝ) < epsilon ^ 2 / 2))).exists
  exact (not_lt_of_ge (herror (phi k)).le) hk

end PoincareConjecture.M35
