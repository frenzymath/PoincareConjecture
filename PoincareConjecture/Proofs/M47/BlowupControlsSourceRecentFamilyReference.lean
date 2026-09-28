import PoincareConjecture.Proofs.M47.BlowupControlsSourceRecentFamilyTime
import PoincareConjecture.Proofs.M47.BlowupControlsSourceRecentFamilyRegion
import PoincareConjecture.Proofs.M47.BlowupControlsSourceRecentFamilyModelJets
import PoincareConjecture.Proofs.M47.BlowupControlsSourceRecentFamilyClocks

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff BigOperators Topology

universe u

namespace PoincareConjecture.M47

open Proofs.M47 M34 M44

local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "E₃" => EuclideanSpace ℝ (Fin 3)
local notation "V" => RoundCylinderCoordinates
local notation "Ic" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem exists_source_recent_reference_tolerance
    {M : Type u} [TopologicalSpace M] [ChartedSpace E₃ M]
    [IsManifold (𝓡 3) ∞ M] [T3Space M]
    {T gamma : ℝ} (hT : 0 < T) (hgamma : 0 < gamma)
    (F : RicciFlow 3 M (Icc 0 T))
    {g : RiemannianMetric 3 M} (N : EpsilonNeck g) (heps : N.epsilon = 2 * gamma)
    {v H0 : ℝ} (hv : v ∈ Icc 0 T) (hH0 : 0 < H0)
    (hfamily : RoundCylinderFamilyClose gamma (Icc (-v * H0) 0)
      (fun u p a b => H0 *
        roundCylinderPullback (F.metric (v + u / H0)) N.coordinate_map p a b))
    {nu : ℝ} (hnu : 0 < nu) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ s ∈ Icc 0 T, ∀ H c : ℝ,
      |s - v| < delta → |H - H0| < delta → |c| < delta →
      0 < H ∧ H ≤ H0 + 1 ∧
      (∀ r ∈ Icc (-(3 * gamma)⁻¹) (3 * gamma)⁻¹,
        r + c ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) ∧
      ∀ w ∈ Icc (0 : ℝ) 1,
        let u := -H * s * (1 - w)
        let u0 := -H0 * v * (1 - w)
        let B : RoundCylinderTwoTensor := fun p a b => H * neckAxialTensorPullback 1 c
          (roundCylinderPullback (F.metric (s * w)) N.coordinate_map) p a b
        let C := sourceRecentTimeCorrection u u0 (fun p a b => H0 *
          neckAxialTensorPullback 1 c
            (roundCylinderPullback (F.metric (v * w)) N.coordinate_map) p a b)
        RoundCylinderTensorSmoothOn (3 * gamma) C ∧
        (∀ z : RoundCylinderSpace, z.2 ∈ Ioo (-(3 * gamma)⁻¹) (3 * gamma)⁻¹ →
          roundCylinderJetErrorSquared u C (Nat.floor (3 * gamma)⁻¹) z ≤ 2 * gamma ^ 2) ∧
        ∀ q : UnitTwoSphere, ∀ r ∈ Ioo (-(3 * gamma)⁻¹) (3 * gamma)⁻¹,
          ∀ j ≤ Nat.floor (3 * gamma)⁻¹, ∀ a b : Fin 3,
            ‖iteratedFDeriv ℝ j (fun y => roundCylinderTensorCoefficient B (chartAt E₂ q) y a b -
              roundCylinderTensorCoefficient C (chartAt E₂ q) y a b) (0, r)‖ ≤ nu := by
  have heps3 : 0 < 3 * gamma := by positivity
  have hinv : (3 * gamma)⁻¹ < N.epsilon⁻¹ :=
    (inv_lt_inv₀ heps3 N.epsilon_pos).mpr (by rw [heps]; linarith)
  obtain ⟨R, hRleft, hRright⟩ := exists_between hinv
  let m := Nat.floor (3 * gamma)⁻¹
  have hm : m ≤ Nat.floor N.epsilon⁻¹ := Nat.floor_mono hinv.le
  obtain ⟨dtime, hdtime, henergy⟩ := exists_source_recent_time_energy_tolerance m
  obtain ⟨Z, hZ, hgram⟩ := exists_source_recent_model_coefficient_time_bound m
  obtain ⟨dmodel, hdmodel, hmodel⟩ := exists_source_recent_normalized_coefficient_tolerance
    hT F N hRright hv hH0 m hm (half_pos hnu)
  let L := H0 + 1 + v
  have hL : 0 < L := by dsimp only [L]; linarith only [hH0, hv.1]
  let D := min dtime (nu / (2 * (Z + 1)))
  have hD : 0 < D := lt_min hdtime (div_pos hnu (by positivity))
  let delta := min dmodel (min (R - (3 * gamma)⁻¹) (D / (L + 1)))
  have hdelta : 0 < delta := lt_min hdmodel
    (lt_min (sub_pos.mpr hRleft) (div_pos hD (by positivity)))
  have hdmodel' : delta ≤ dmodel := min_le_left _ _
  have hdshift : delta ≤ R - (3 * gamma)⁻¹ := (min_le_right _ _).trans (min_le_left _ _)
  have hdbudget : (L + 1) * delta ≤ D := by
    have h := (le_div_iff₀ (by positivity : 0 < L + 1)).mp
      ((min_le_right _ _).trans (min_le_right _ _) : delta ≤ D / (L + 1))
    change delta * (L + 1) ≤ D at h
    simpa only [mul_comm delta (L + 1)] using h
  have hZD : Z * D ≤ nu / 2 := by
    have h := (le_div_iff₀ (by positivity : 0 < 2 * (Z + 1))).mp
      (min_le_right dtime (nu / (2 * (Z + 1))))
    change D * (2 * (Z + 1)) ≤ nu at h
    nlinarith only [h, hD]
  refine ⟨delta, hdelta, ?_⟩
  intro s hs H c hsv hHH0 hc
  obtain ⟨hH, hHL, hnear⟩ := hmodel s hs H (hsv.trans_le hdmodel') (hHH0.trans_le hdmodel')
  have hshift (r : ℝ) (hr : r ∈ Icc (-(3 * gamma)⁻¹) (3 * gamma)⁻¹) :
      r + c ∈ Ioo (-R) R := by
    apply abs_lt.mp
    have hrabs : |r| ≤ (3 * gamma)⁻¹ := abs_le.mpr hr
    exact (abs_add_le r c).trans_lt (by linarith only [hrabs, hc, hdshift])
  have hdom (r : ℝ) (hr : r ∈ Icc (-(3 * gamma)⁻¹) (3 * gamma)⁻¹) :
      r + c ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
    ⟨(neg_lt_neg hRright).trans (hshift r hr).1, (hshift r hr).2.trans hRright⟩
  have hgam : N.epsilon⁻¹ ≤ gamma⁻¹ := inv_anti₀ hgamma (by rw [heps]; linarith)
  have hdomGamma (r : ℝ) (hr : r ∈ Ioo (-(3 * gamma)⁻¹) (3 * gamma)⁻¹) :
      r + c ∈ Ioo (-gamma⁻¹) gamma⁻¹ :=
    ⟨(neg_le_neg hgam).trans_lt (hdom r ⟨hr.1.le, hr.2.le⟩).1,
      (hdom r ⟨hr.1.le, hr.2.le⟩).2.trans_le hgam⟩
  refine ⟨hH, hHL, hdom, ?_⟩
  intro w hw
  let u := -H * s * (1 - w)
  let u0 := -H0 * v * (1 - w)
  have hu : u ≤ 0 := mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hH.le) hs.1) (sub_nonneg.mpr hw.2)
  have hu0 : u0 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hH0.le) hv.1) (sub_nonneg.mpr hw.2)
  have hu0mem : u0 ∈ Icc (-v * H0) 0 := by
    refine ⟨?_, hu0⟩
    dsimp only [u0]
    nlinarith only [mul_nonneg (mul_nonneg hH0.le hv.1) hw.1]
  have hclock : v + u0 / H0 = v * w := by dsimp only [u0]; field_simp; ring
  have hclockSmall : |u - u0| ≤ D :=
    (source_recent_clock_difference_le hH hHL hv.1 hsv.le hHH0.le hw).trans
      ((mul_le_mul_of_nonneg_right (by linarith : L ≤ L + 1) hdelta.le).trans hdbudget)
  let raw : RoundCylinderTwoTensor := fun p a b => H *
    roundCylinderPullback (F.metric (s * w)) N.coordinate_map p a b
  let raw0 : RoundCylinderTwoTensor := fun p a b => H0 *
    roundCylinderPullback (F.metric (v * w)) N.coordinate_map p a b
  let B := neckAxialTensorPullback 1 c raw
  let B0 := neckAxialTensorPullback 1 c raw0
  let C := sourceRecentTimeCorrection u u0 B0
  let linear (time scale : ℝ) : RoundCylinderSpace → V →L[ℝ] V →L[ℝ] ℝ := fun p =>
    let A : V →L[ℝ] E₃ := mfderiv Ic (𝓡 3) N.coordinate_map p
    let G : E₃ →L[ℝ] E₃ →L[ℝ] ℝ := (F.metric time).inner (N.coordinate_map p)
    scale • G.bilinearComp A A
  have hraw : RoundCylinderTensorSmoothOn N.epsilon raw :=
    (capPersistence_roundCylinderTensorSmoothOn_pullback
      (F.metric (s * w)) N.coordinate_map_smooth).const_mul
  have hraw0 : RoundCylinderClose gamma u0 raw0 := by
    obtain ⟨hf, b, hb, hbound⟩ := hfamily
    refine ⟨?_, b, hb, ?_⟩
    · simpa only [raw0, hclock] using hf u0 hu0mem
    · intro z hz
      simpa only [raw0, hclock] using hbound u0 hu0mem z hz
  have hBsmooth : RoundCylinderTensorSmoothOn (3 * gamma) B :=
    source_recent_translation_smooth (fun r hr => hdom r ⟨hr.1.le, hr.2.le⟩)
      (linear (s * w) H) hraw
  have hB0smooth : RoundCylinderTensorSmoothOn (3 * gamma) B0 :=
    source_recent_translation_smooth hdomGamma (linear (v * w) H0) hraw0.1
  have hCsmooth : RoundCylinderTensorSmoothOn (3 * gamma) C :=
    sourceRecentTimeCorrection_smooth hB0smooth
  change RoundCylinderTensorSmoothOn (3 * gamma) C ∧
    (∀ z, z.2 ∈ Ioo (-(3 * gamma)⁻¹) (3 * gamma)⁻¹ →
      roundCylinderJetErrorSquared u C m z ≤ 2 * gamma ^ 2) ∧
    ∀ q r, r ∈ Ioo (-(3 * gamma)⁻¹) (3 * gamma)⁻¹ → ∀ j ≤ m, ∀ a b,
      ‖iteratedFDeriv ℝ j (fun y => roundCylinderTensorCoefficient B (chartAt E₂ q) y a b -
        roundCylinderTensorCoefficient C (chartAt E₂ q) y a b) (0, r)‖ ≤ nu
  refine ⟨hCsmooth, ?_, ?_⟩
  · intro z hz
    have hz0 : (neckAxialSpaceMap 1 c z).2 ∈ Ioo (-gamma⁻¹) gamma⁻¹ := by
      simpa only [neckAxialSpaceMap, one_mul] using hdomGamma z.2 hz
    have horder : m ≤ Nat.floor gamma⁻¹ := Nat.floor_mono (hinv.le.trans hgam)
    obtain ⟨b, hb, hbound⟩ := hraw0.2
    have hbase := (M34.roundCylinderJetErrorSquared_mono_order (hu0.trans_lt zero_lt_one)
      raw0 horder (neckAxialSpaceMap 1 c z)).trans (hbound _ hz0)
    have hax := roundCylinderJetErrorSquared_neckAxialTensorPullback_le
      (show (1 : ℝ) ∈ Icc 0 1 by norm_num) hu0 (show (0 : ℝ) < 1 / 3 by norm_num)
      c (linear (v * w) H0) hraw0.1 m z hz0
    norm_num only [one_pow, sub_self, zero_pow (by decide : 2 ≠ 0),
      mul_zero, add_zero] at hax
    have hC := henergy hu hu0 (hclockSmall.trans (min_le_left _ _)) B0 z
    change roundCylinderJetErrorSquared u0 B0 m z ≤
      (4 / 3 : ℝ) * roundCylinderJetErrorSquared u0 raw0 m (neckAxialSpaceMap 1 c z) at hax
    change roundCylinderJetErrorSquared u C m z ≤
      (3 / 2 : ℝ) * roundCylinderJetErrorSquared u0 B0 m z at hC
    nlinarith only [hbase, hb, hax, hC]
  · intro q r hr j hj a b
    let f : V → ℝ := fun y => roundCylinderTensorCoefficient B (chartAt E₂ q) y a b -
      roundCylinderTensorCoefficient B0 (chartAt E₂ q) y a b
    let g' : V → ℝ := fun y => roundCylinderGram u (chartAt E₂ q) y a b -
      roundCylinderGram u0 (chartAt E₂ q) y a b
    have heq : (fun y => roundCylinderTensorCoefficient B (chartAt E₂ q) y a b -
        roundCylinderTensorCoefficient C (chartAt E₂ q) y a b) = fun y => f y - g' y := by
      funext y
      simp only [C, sourceRecentTimeCorrection_coefficient, f, g']
      ring
    have hmem : (0, r) ∈ (chartAt E₂ q).target ×ˢ Ioo (-(3 * gamma)⁻¹) (3 * gamma)⁻¹ := by
      refine ⟨?_, hr⟩
      rw [roundCylinder_sphereChart_target]
      trivial
    have hnhds := ((chartAt E₂ q).open_target.prod isOpen_Ioo).mem_nhds hmem
    have hf : ContDiffAt ℝ ∞ f (0, r) :=
      ((hBsmooth q a b).contDiffAt hnhds).sub ((hB0smooth q a b).contDiffAt hnhds)
    have hg : ContDiffAt ℝ ∞ g' (0, r) :=
      (evolving_roundCylinderGram_contDiff u q a b).contDiffAt.sub
        (evolving_roundCylinderGram_contDiff u0 q a b).contDiffAt
    have hfnorm : ‖iteratedFDeriv ℝ j f (0, r)‖ < nu / 2 := by
      change ‖iteratedFDeriv ℝ j (fun y =>
        roundCylinderTensorCoefficient (neckAxialTensorPullback 1 c raw) (chartAt E₂ q) y a b -
        roundCylinderTensorCoefficient (neckAxialTensorPullback 1 c raw0) (chartAt E₂ q) y a b)
        (0, r)‖ < nu / 2
      rw [source_recent_translation_coefficient_jet]
      exact hnear w hw q (r + c) (Ioo_subset_Icc_self (hshift r ⟨hr.1.le, hr.2.le⟩)) j hj a b
    have hgnorm : ‖iteratedFDeriv ℝ j g' (0, r)‖ ≤ nu / 2 :=
      (hgram u u0 q r j hj a b).trans
        ((mul_le_mul_of_nonneg_left hclockSmall hZ).trans hZD)
    rw [heq, fun_iteratedFDeriv_sub_apply
      (hf.of_le (by exact_mod_cast le_top)) (hg.of_le (by exact_mod_cast le_top))]
    exact (norm_sub_le _ _).trans (by linarith only [hfnorm, hgnorm])

end PoincareConjecture.M47
