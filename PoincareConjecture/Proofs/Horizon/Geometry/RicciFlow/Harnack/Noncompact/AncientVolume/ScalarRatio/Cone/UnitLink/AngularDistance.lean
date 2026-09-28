import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.UnitLink.Distance
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.Metric.AngularPaths
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.Polar.Tensor
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.ZeroRatio.MetricArc
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 8

open Set Filter MeasureTheory TopologicalSpace PoincareConjecture
open Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Topology NNReal ENNReal Bundle

namespace PoincareConjecture.RiemannianMetric



theorem tangentNorm_deriv_of_edist_affine_segment
    {n : ℕ} (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
    {γ : ℝ → EuclideanSpace ℝ (Fin n)} {a b C : ℝ} (hC : 0 ≤ C)
    (hmetric : ∀ s ∈ Ioo a b, ∀ t ∈ Ioo a b,
      g.edist (γ s) (γ t) = ENNReal.ofReal (C * |s - t|))
    {t : ℝ} (ht : t ∈ Ioo a b) :
    g.tangentNorm (γ t) (deriv γ t) = C := by
  obtain ⟨hgeo, hsm⟩ := g.isGeodesicOn_and_contMDiffOn_of_edist_affine_segment hC hmetric
  let δ := min (t - a) (b - t) / 4
  have hδ : 0 < δ := div_pos (lt_min (sub_pos.mpr ht.1) (sub_pos.mpr ht.2)) (by norm_num)
  have hδa : 4 * δ ≤ t - a := by dsimp only [δ]; linarith [min_le_left (t - a) (b - t)]
  have hδb : 4 * δ ≤ b - t := by dsimp only [δ]; linarith [min_le_right (t - a) (b - t)]
  let η := fun s : ℝ => γ (δ * s + t)
  have htime (s : ℝ) (hs : s ∈ Ioo (-1 : ℝ) 2) : δ * s + t ∈ Ioo a b := by
    constructor <;> nlinarith [hs.1, hs.2]
  have hη : g.IsGeodesicOn η (Ioo (-1 : ℝ) (1 + 1)) := by
    intro s hs
    apply hgeo.comp_affine δ t s
    exact htime s ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hη0 : η 0 = γ t := by simp [η]
  have hγdiff : DifferentiableAt ℝ γ t :=
    ((contMDiffAt_iff_contDiffAt.mp (hsm.contMDiffAt (isOpen_Ioo.mem_nhds ht))).differentiableAt
      (by simp))
  have hdη : HasDerivAt η (δ • deriv γ t) 0 := by
    have hγd : HasDerivAt γ (deriv γ t) (δ * 0 + t) := by simpa using hγdiff.hasDerivAt
    have hh := hγd.scomp 0
      (((hasDerivAt_id (0 : ℝ)).const_mul δ).add_const t)
    simpa only [mul_zero, zero_add, mul_one, Function.comp_def, id_eq] using hh
  have hdist : g.edist (η 0) (η 1) = ENNReal.ofReal (C * δ) := by
    rw [hmetric _ (htime 0 (by norm_num)) _ (htime 1 (by norm_num))]
    have he : δ * 0 + t - (δ * 1 + t) = -δ := by ring
    rw [he, abs_neg, abs_of_pos hδ]
  have hmin : ∀ s ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
      g.edist (η s) (η u) = ENNReal.ofReal |s - u| * g.edist (η 0) (η 1) := by
    intro s hs u hu
    rw [hmetric _ (htime s ⟨by linarith [hs.1], by linarith [hs.2]⟩)
      _ (htime u ⟨by linarith [hu.1], by linarith [hu.2]⟩), hdist,
      add_sub_add_right_eq_sub, ← mul_sub, abs_mul, abs_of_pos hδ,
      ← ENNReal.ofReal_mul (abs_nonneg _)]
    congr 1
    ring
  have hn := hη.initial_tangentNorm_eq_of_edist_segment (by norm_num : (0 : ℝ) < 1)
    (p := η 0) (q := η 1) rfl (by simpa using hdη) hmin
  rw [hdist] at hn
  have hn' := (ENNReal.ofReal_eq_ofReal_iff (Real.sqrt_nonneg _) (mul_nonneg hC hδ.le)).mp hn
  rw [hη0] at hn'
  change g.tangentNorm (γ t) (δ • deriv γ t) = C * δ at hn'
  have hscale : g.tangentNorm (γ t) (δ • deriv γ t) = δ * g.tangentNorm (γ t) (deriv γ t) := by
    simp only [tangentNorm, map_smul, smul_apply, smul_eq_mul]
    rw [← mul_assoc, ← pow_two, Real.sqrt_mul (sq_nonneg δ), Real.sqrt_sq hδ.le]
  rw [hscale] at hn'
  nlinarith [hn']

end PoincareConjecture.RiemannianMetric

namespace Poincare.AncientVolume.ScalarRatio

variable {X : Type*} [MetricSpace X] {p : X} {hc : RayComparison p} {n : ℕ}


def asymptoticConeUnitDirection (hc : RayComparison p)
    (x : AsymptoticConeUnitSlice p hc) (a : AsymptoticCone p hc) :
    AsymptoticConeUnitSlice p hc :=
  if ha : 0 < asymptoticConeRadius hc a then asymptoticConeNormalize hc ⟨a, ha⟩ else x

theorem asymptoticConeUnitDirection_val (x : AsymptoticConeUnitSlice p hc)
    {a : AsymptoticCone p hc} (ha : 0 < asymptoticConeRadius hc a) :
    (asymptoticConeUnitDirection hc x a).1 =
      asymptoticConeDilation hc (asymptoticConeRadius hc a)⁻¹ a := by
  simp only [asymptoticConeUnitDirection, dif_pos ha, asymptoticConeNormalize]




theorem radial_angular_energy_of_metric_arc
    (hcover : ∀ x : AsymptoticConeUnitSlice p hc,
      ∃ (d : UnitSliceRadialChartData hc n) (z : d.Level), (d.levelHomeomorph z).1 = x)
    (x : AsymptoticConeUnitSlice p hc) (γ : ℝ → AsymptoticCone p hc)
    {a b C : ℝ} (hC : 0 ≤ C)
    (hmetric : ∀ s ∈ Ioo a b, ∀ t ∈ Ioo a b, dist (γ s) (γ t) = C * |s - t|)
    {t : ℝ} (ht : t ∈ Ioo a b) (hpos : 0 < asymptoticConeRadius hc (γ t)) :
    letI := unitSliceChartedSpace hc n hcover
    letI := unitSlice_isManifold hc n hcover
    let r := fun s : ℝ => (asymptoticConeRadius hc (γ s) : ℝ)
    let θ := fun s : ℝ => asymptoticConeUnitDirection hc x (γ s)
    ContDiffAt ℝ ∞ r t ∧ ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n) ∞ θ t ∧
      C ^ 2 = (deriv r t) ^ 2 + (r t) ^ 2 *
        (unitSliceMetric hcover).inner (θ t)
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) θ t 1) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) θ t 1) := by
  let := unitSliceChartedSpace hc n hcover
  let := unitSlice_isManifold hc n hcover
  let : Fact (Module.finrank ℝ (UnitSliceAmbient n) = n + 1) := ⟨finrank_euclideanSpace_fin⟩
  let r := fun s : ℝ => (asymptoticConeRadius hc (γ s) : ℝ)
  let θ := fun s : ℝ => asymptoticConeUnitDirection hc x (γ s)
  let c := asymptoticConeRadius hc (γ t)
  obtain ⟨d, z, hz⟩ := hcover (asymptoticConeNormalize hc ⟨γ t, hpos⟩)
  let H := (d.dilate c hpos).ambientChart
  let g := (d.dilate c hpos).metric
  let β := fun s : ℝ => H.symm (γ s)
  have hunit : d.ambientChart (openLevelIncl d.potential d.source (1 / 2) z) =
      asymptoticConeDilation hc c⁻¹ (γ t) := congrArg Subtype.val hz
  have hcenter : H (openLevelIncl d.potential d.source (1 / 2) z) = γ t := by
    rw [d.dilate_apply, hunit, asymptoticConeDilation_mul,
      mul_inv_cancel₀ hpos.ne', asymptoticConeDilation_one]
  have hHt : γ t ∈ H.target := hcenter ▸ H.map_source z.1.2
  have hβt : β t = openLevelIncl d.potential d.source (1 / 2) z := by
    rw [show β t = H.symm (γ t) from rfl, ← hcenter]
    exact H.left_inv z.1.2
  obtain ⟨Q, hzQ, hQz, hQtarget, hQ, hQs, hQis, hQr, hQθ, hQtensor⟩ :=
    d.exists_smooth_polar_coordinates c hpos z
  have hβQ : β t ∈ Q.target := hβt ▸ hQz ▸ Q.map_source hzQ
  have hγLip : LipschitzOnWith (Real.toNNReal C) γ (Ioo a b) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro s hs u hu
    rw [hmetric s hs u hu, Real.coe_toNNReal _ hC, Real.dist_eq]
  have hγcont : ContinuousAt γ t := hγLip.continuousOn.continuousAt (isOpen_Ioo.mem_nhds ht)
  have hβcont : ContinuousAt β t := (H.continuousAt_symm hHt).comp hγcont
  have hnear : ∀ᶠ s in 𝓝 t, s ∈ Ioo a b ∧ γ s ∈ H.target ∧ β s ∈ Q.target := by
    filter_upwards [isOpen_Ioo.mem_nhds ht, hγcont (H.open_target.mem_nhds hHt),
      hβcont (Q.open_target.mem_nhds hβQ)] with s hs hH hQ
    exact ⟨hs, hH, hQ⟩
  obtain ⟨a', b', ht', hsub⟩ := hnear.exists_Ioo_subset
  have hβmetric (s : ℝ) (hs : s ∈ Ioo a' b') (u : ℝ) (hu : u ∈ Ioo a' b') :
      g.edist (β s) (β u) = ENNReal.ofReal (C * |s - u|) := by
    have hh := (d.dilate c hpos).distance (β s) (H.map_target (hsub hs).2.1)
      (β u) (H.map_target (hsub hu).2.1)
    rw [H.right_inv (hsub hs).2.1, H.right_inv (hsub hu).2.1,
      hmetric s (hsub hs).1 u (hsub hu).1] at hh
    rw [hh, ENNReal.ofReal_toReal (g.edist_ne_top _ _)]
  have hβsmooth := (g.isGeodesicOn_and_contMDiffOn_of_edist_affine_segment hC hβmetric).2
  have hβsm := hβsmooth.contMDiffAt (isOpen_Ioo.mem_nhds ht')
  let ψ := fun s : ℝ => Q.symm (β s)
  have hψsm : ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞ ψ t :=
    (hQis.contMDiffAt (Q.open_target.mem_nhds hβQ)).comp t hβsm
  have hrnear : (fun s : ℝ => (ψ s).1) =ᶠ[𝓝 t] r := by
    filter_upwards [hnear] with s hs
    have hh := hQr (β s) hs.2.2
    have hcone : H (β s) = γ s := H.right_inv hs.2.1
    have hrad := congrArg (fun w => (asymptoticConeRadius hc w : ℝ)) hcone
    rw [d.dilate_apply, asymptoticConeRadius_dilation, NNReal.coe_mul] at hrad
    exact hh.trans hrad
  let q := fun w : d.Level => (d.levelHomeomorph w).1
  have hqsm : ContMDiff (𝓡 n) (𝓡 n) ∞ q :=
    (d.isLocalDiffeomorph_levelMap hc n hcover).contMDiff
  have hθnear : (fun s : ℝ => q (ψ s).2) =ᶠ[𝓝 t] θ := by
    filter_upwards [hnear] with s hs
    have hcone : H (β s) = γ s := H.right_inv hs.2.1
    have hrpositive : 0 < asymptoticConeRadius hc (γ s) := by
      rw [← hcone, d.dilate_apply, asymptoticConeRadius_dilation]
      have hp := (hQ (ψ s) (Q.map_target hs.2.2)).1
      have hh := hQr (β s) hs.2.2
      exact_mod_cast (show 0 < (c : ℝ) * (asymptoticConeRadius hc (d.ambientChart (β s)) : ℝ)
        from hh ▸ hp)
    apply Subtype.ext
    rw [asymptoticConeUnitDirection_val x hrpositive]
    change d.ambientChart (openLevelIncl d.potential d.source (1 / 2) (ψ s).2) = _
    rw [hQθ (β s) hs.2.2, ← hcone, d.dilate_apply, asymptoticConeRadius_dilation,
      asymptoticConeDilation_mul]
    congr 1
    rw [mul_inv, mul_right_comm, inv_mul_cancel₀ (show c ≠ 0 from hpos.ne'), one_mul]
  have hrsm : ContDiffAt ℝ ∞ r t :=
    contMDiffAt_iff_contDiffAt.mp (hψsm.fst.congr_of_eventuallyEq hrnear.symm)
  have hθsm : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n) ∞ θ t :=
    (hqsm.contMDiffAt.comp t hψsm.snd).congr_of_eventuallyEq hθnear.symm
  refine ⟨hrsm, hθsm, ?_⟩
  have hψdiff := hψsm.mdifferentiableAt (by simp)
  let v : ℝ × EuclideanSpace ℝ (Fin n) := mfderiv 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod (𝓡 n)) ψ t 1
  have henergy := hQtensor (ψ t) (Q.map_target hβQ) v.1 v.1 v.2 v.2
  have hback : (fun s : ℝ => Q (ψ s)) =ᶠ[𝓝 t] β := by
    filter_upwards [hnear] with s hs
    exact Q.right_inv hs.2.2
  have hβdiff := hβsm.mdifferentiableAt (by simp)
  have hQdiff := (hQs.contMDiffAt (Q.open_source.mem_nhds (Q.map_target hβQ))).mdifferentiableAt (by simp)
  have hdβ : mfderiv (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 (n + 1)) Q (ψ t) v = deriv β t := by
    have hh := congrArg (fun A : ℝ →L[ℝ] UnitSliceAmbient n => A 1)
      (hback.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := 𝓡 (n + 1)))
    change mfderiv 𝓘(ℝ, ℝ) (𝓡 (n + 1)) (Q ∘ ψ) t 1 =
      mfderiv 𝓘(ℝ, ℝ) (𝓡 (n + 1)) β t 1 at hh
    rw [mfderiv_comp t hQdiff hψdiff] at hh
    rw [mfderiv_eq_fderiv] at hh
    convert! hh using 1
  have hdr : v.1 = deriv r t := by
    have hh := congrArg (fun A : ℝ →L[ℝ] ℝ => A 1)
      (hrnear.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℝ)))
    erw [mfderiv_comp t mdifferentiableAt_fst hψdiff, mfderiv_fst] at hh
    rw [mfderiv_eq_fderiv] at hh
    convert! hh using 1
  have hdθ : mfderiv (𝓡 n) (𝓡 n) q (ψ t).2 v.2 = mfderiv 𝓘(ℝ, ℝ) (𝓡 n) θ t 1 := by
    have hh := congrArg (fun A : ℝ →L[ℝ] EuclideanSpace ℝ (Fin n) => A 1)
      (hθnear.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := 𝓡 n))
    erw [mfderiv_comp t (hqsm.mdifferentiable (by simp) _) hψdiff.snd,
      mfderiv_comp t mdifferentiableAt_snd hψdiff, mfderiv_snd] at hh
    convert! hh using 1
  have hlevel := unitSliceMetric_inner hcover d (ψ t).2 v.2 v.2
  change d.levelMetric.inner (ψ t).2 v.2 v.2 =
    (unitSliceMetric hcover).inner (q (ψ t).2)
      (mfderiv (𝓡 n) (𝓡 n) q (ψ t).2 v.2) (mfderiv (𝓡 n) (𝓡 n) q (ψ t).2 v.2) at hlevel
  rw [hdθ, hθnear.eq_of_nhds] at hlevel
  change g.inner (Q (ψ t)) _ _ = _ at henergy
  simp only [Prod.mk.eta] at henergy
  rw [hdβ, hback.eq_of_nhds, hdr, hrnear.eq_of_nhds, ← pow_two] at henergy
  change g.inner (β t) (deriv β t) (deriv β t) =
    (deriv r t) ^ 2 + (r t) ^ 2 * d.levelMetric.inner (ψ t).2 v.2 v.2 at henergy
  rw [hlevel] at henergy
  have hspeed := g.tangentNorm_deriv_of_edist_affine_segment hC hβmetric ht'
  have hsq := congrArg (fun u : ℝ => u ^ 2) hspeed
  have hnonneg : 0 ≤ g.inner (β t) (deriv β t) (deriv β t) := by
    by_cases hv : deriv β t = 0
    · simp [hv]
    · exact (g.pos _ _ hv).le
  rw [RiemannianMetric.tangentNorm, Real.sq_sqrt hnonneg] at hsq
  exact hsq.symm.trans henergy



theorem tangentNorm_unitDirection_of_metric_segment
    (hcover : ∀ x : AsymptoticConeUnitSlice p hc,
      ∃ (d : UnitSliceRadialChartData hc n) (z : d.Level), (d.levelHomeomorph z).1 = x)
    (x y : AsymptoticConeUnitSlice p hc) (hxy : dist x y < 2)
    (γ : ℝ → AsymptoticCone p hc) (hγ0 : γ 0 = x.1) (hγ1 : γ 1 = y.1)
    (hγ : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      dist (γ s) (γ t) = |s - t| * dist x y) :
    letI := unitSliceChartedSpace hc n hcover
    letI := unitSlice_isManifold hc n hcover
    let θ := fun s : ℝ => asymptoticConeUnitDirection hc x (γ s)
    ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ θ (Ioo (0 : ℝ) 1) ∧
      ∀ t ∈ Ioo (0 : ℝ) 1,
        (unitSliceMetric hcover).tangentNorm (θ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) θ t 1) =
          dist x y * Real.sqrt (1 - dist x y ^ 2 / 4) /
            (1 - t * (1 - t) * dist x y ^ 2) := by
  let := unitSliceChartedSpace hc n hcover
  let := unitSlice_isManifold hc n hcover
  let θ := fun s : ℝ => asymptoticConeUnitDirection hc x (γ s)
  let r := fun s : ℝ => (asymptoticConeRadius hc (γ s) : ℝ)
  let D := dist x y
  have hbound := asymptoticConeRadius_lower_bound_on_unit_segment hc x y hxy γ hγ0 hγ1 hγ
  have hpositive (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : 0 < r t :=
    hbound.1.trans_le (hbound.2 t ht).2
  have hmetric (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) 1) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      dist (γ s) (γ t) = D * |s - t| := by
    rw [hγ s ⟨hs.1.le, hs.2.le⟩ t ⟨ht.1.le, ht.2.le⟩, mul_comm]
  have hlocal (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :=
    radial_angular_energy_of_metric_arc hcover x γ (show 0 ≤ D from dist_nonneg)
      hmetric ht (hpositive t ⟨ht.1.le, ht.2.le⟩)
  refine ⟨fun t ht => (hlocal t ht).2.1.contMDiffWithinAt, ?_⟩
  intro t ht
  obtain ⟨hrs, _, he⟩ := hlocal t ht
  change D ^ 2 = (deriv r t) ^ 2 + (r t) ^ 2 *
    (unitSliceMetric hcover).inner (θ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) θ t 1)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) θ t 1) at he
  have hr := hpositive t ⟨ht.1.le, ht.2.le⟩
  have hr2 : (r t) ^ 2 = 1 - t * (1 - t) * D ^ 2 := (hbound.2 t ⟨ht.1.le, ht.2.le⟩).1
  have hnear : (fun s : ℝ => (r s) ^ 2) =ᶠ[𝓝 t] (fun s => 1 - s * (1 - s) * D ^ 2) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    exact (hbound.2 s ⟨hs.1.le, hs.2.le⟩).1
  have hdpoly : HasDerivAt (fun s : ℝ => 1 - s * (1 - s) * D ^ 2) ((2 * t - 1) * D ^ 2) t := by
    convert! (((hasDerivAt_id t).mul ((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t))).mul_const
      (D ^ 2)).const_sub 1 using 1
    simp only [Pi.sub_apply, id_eq]
    ring
  have hdr : 2 * r t * deriv r t = (2 * t - 1) * D ^ 2 := by
    have hd := (hrs.differentiableAt (by simp)).hasDerivAt.pow 2
    have hh := (hd.congr_of_eventuallyEq hnear.symm).unique hdpoly
    simpa only [Nat.cast_ofNat, Nat.reduceSub, pow_one] using hh
  let N := (unitSliceMetric hcover).tangentNorm (θ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) θ t 1)
  have hN : 0 ≤ N := Real.sqrt_nonneg _
  have hinner : (unitSliceMetric hcover).inner (θ t)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) θ t 1) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) θ t 1) = N ^ 2 := by
    dsimp only [N, RiemannianMetric.tangentNorm]
    rw [Real.sq_sqrt]
    by_cases hv : mfderiv 𝓘(ℝ, ℝ) (𝓡 n) θ t 1 = 0
    · simp [hv]
    · exact ((unitSliceMetric hcover).pos _ _ hv).le
  rw [hinner] at he
  have hcore : (r t) ^ 4 * N ^ 2 = D ^ 2 * (1 - D ^ 2 / 4) := by
    have he' := congrArg (fun u : ℝ => u * (r t) ^ 2) he
    have hd' := congrArg (fun u : ℝ => u ^ 2) hdr
    have hr' := congrArg (fun u : ℝ => u * D ^ 2) hr2
    nlinarith only [he', hd', hr']
  have hD : 0 ≤ D := dist_nonneg
  have hdisc : 0 ≤ 1 - D ^ 2 / 4 := by dsimp only [D]; nlinarith [dist_nonneg (x := x) (y := y)]
  have hroot := Real.sq_sqrt hdisc
  have hproduct : N * (r t) ^ 2 = D * Real.sqrt (1 - D ^ 2 / 4) := by
    have hroot' := congrArg (fun u : ℝ => u * D ^ 2) hroot
    have hleft : 0 ≤ N * (r t) ^ 2 := mul_nonneg hN (sq_nonneg _)
    have hright : 0 ≤ D * Real.sqrt (1 - D ^ 2 / 4) := mul_nonneg hD (Real.sqrt_nonneg _)
    nlinarith only [hcore, hroot', hleft, hright]
  change N = D * Real.sqrt (1 - D ^ 2 / 4) / (1 - t * (1 - t) * D ^ 2)
  rw [← hr2]
  exact (eq_div_iff (pow_ne_zero 2 hr.ne')).mpr hproduct

private theorem angular_denominator_pos {D : ℝ} (hD : 0 ≤ D) (hD2 : D < 2) (t : ℝ) :
    0 < 1 - t * (1 - t) * D ^ 2 := by
  have hdisc : 0 < 1 - D ^ 2 / 4 := by nlinarith
  nlinarith [sq_nonneg ((t - 1 / 2) * D)]

private theorem hasDerivAt_angular_parameter {D : ℝ} (hD : 0 ≤ D) (hD2 : D < 2) (t : ℝ) :
    HasDerivAt (fun s : ℝ => Real.arctan ((2 * s - 1) * D / (2 * Real.sqrt (1 - D ^ 2 / 4))))
      (D * Real.sqrt (1 - D ^ 2 / 4) / (1 - t * (1 - t) * D ^ 2)) t := by
  let k := Real.sqrt (1 - D ^ 2 / 4)
  have hk : 0 < k := Real.sqrt_pos.mpr (by nlinarith)
  have hk2 : k ^ 2 = 1 - D ^ 2 / 4 := Real.sq_sqrt (by nlinarith)
  have hden := angular_denominator_pos hD hD2 t
  have hd := ((((hasDerivAt_id t).const_mul 2).sub_const 1).mul_const D).div_const (2 * k)
  convert! hd.arctan using 1
  change D * k / (1 - t * (1 - t) * D ^ 2) =
    1 / (1 + ((2 * t - 1) * D / (2 * k)) ^ 2) * (2 * 1 * D / (2 * k))
  have hpos : 0 < 1 + ((2 * t - 1) * D / (2 * k)) ^ 2 := by positivity
  field_simp [hk.ne', hden.ne']
  field_simp [show 1 - D ^ 2 * t * (1 - t) ≠ 0 by nlinarith [hden]]
  nlinarith [congrArg (fun u : ℝ => u * D) hk2]

private theorem twice_arctan_eq_arccos_chord {D : ℝ} (hD : 0 ≤ D) (hD2 : D < 2) :
    2 * Real.arctan (D / (2 * Real.sqrt (1 - D ^ 2 / 4))) = Real.arccos (1 - D ^ 2 / 2) := by
  let k := Real.sqrt (1 - D ^ 2 / 4)
  have hk : 0 < k := Real.sqrt_pos.mpr (by nlinarith)
  have hk2 : k ^ 2 = 1 - D ^ 2 / 4 := Real.sq_sqrt (by nlinarith)
  have hcos : Real.cos (2 * Real.arctan (D / (2 * k))) = 1 - D ^ 2 / 2 := by
    rw [Real.cos_two_mul, Real.cos_sq_arctan]
    have hpos : 0 < 1 + (D / (2 * k)) ^ 2 := by positivity
    field_simp
    nlinarith [hk2]
  rw [← hcos, Real.arccos_cos]
  · exact mul_nonneg (by norm_num) (Real.arctan_nonneg.mpr (div_nonneg hD (by positivity)))
  · linarith [Real.arctan_lt_pi_div_two (D / (2 * k))]




theorem pathELength_unitDirection_of_metric_segment
    (hcover : ∀ x : AsymptoticConeUnitSlice p hc,
      ∃ (d : UnitSliceRadialChartData hc n) (z : d.Level), (d.levelHomeomorph z).1 = x)
    (x y : AsymptoticConeUnitSlice p hc) (hxy : dist x y < 2)
    (γ : ℝ → AsymptoticCone p hc) (hγ0 : γ 0 = x.1) (hγ1 : γ 1 = y.1)
    (hγ : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      dist (γ s) (γ t) = |s - t| * dist x y) :
    letI := unitSliceChartedSpace hc n hcover
    letI := unitSlice_isManifold hc n hcover
    (unitSliceMetric hcover).pathELength (fun s => asymptoticConeUnitDirection hc x (γ s)) 0 1 =
      ENNReal.ofReal (Real.arccos (1 - dist x y ^ 2 / 2)) := by
  let := unitSliceChartedSpace hc n hcover
  let := unitSlice_isManifold hc n hcover
  let θ := fun s : ℝ => asymptoticConeUnitDirection hc x (γ s)
  let D := dist x y
  let f := fun s : ℝ => D * Real.sqrt (1 - D ^ 2 / 4) / (1 - s * (1 - s) * D ^ 2)
  have hD : 0 ≤ D := dist_nonneg
  have hD2 : D < 2 := hxy
  have hf : Continuous f := by
    apply Continuous.div continuous_const
      (continuous_const.sub ((continuous_id.mul (continuous_const.sub continuous_id)).mul continuous_const))
    intro t
    exact (angular_denominator_pos hD hD2 t).ne'
  have hfpos (t : ℝ) : 0 ≤ f t :=
    div_nonneg (mul_nonneg hD (Real.sqrt_nonneg _)) (angular_denominator_pos hD hD2 t).le
  have hlength : (unitSliceMetric hcover).pathELength θ 0 1 =
      ∫⁻ t in Icc (0 : ℝ) 1, ENNReal.ofReal (f t) := by
    rw [(unitSliceMetric hcover).pathELength_eq_lintegral_tangentNorm,
      ← restrict_Ioo_eq_restrict_Icc]
    apply setLIntegral_congr_fun measurableSet_Ioo
    intro t ht
    exact congrArg ENNReal.ofReal
      ((tangentNorm_unitDirection_of_metric_segment hcover x y hxy γ hγ0 hγ1 hγ).2 t ht)
  rw [hlength, ← ofReal_integral_eq_lintegral_ofReal
    (hf.continuousOn.integrableOn_Icc) (Filter.Eventually.of_forall hfpos)]
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t (_ : t ∈ uIcc (0 : ℝ) 1) => hasDerivAt_angular_parameter hD hD2 t)
    (hf.intervalIntegrable 0 1)
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    ← integral_Icc_eq_integral_Ioc] at hFTC
  have hresult : (∫ t in Icc (0 : ℝ) 1, f t) = Real.arccos (1 - D ^ 2 / 2) := by
    calc
      _ = Real.arctan (D / (2 * Real.sqrt (1 - D ^ 2 / 4))) -
          Real.arctan (-(D / (2 * Real.sqrt (1 - D ^ 2 / 4)))) := by
        simpa only [mul_one, sub_self, zero_sub, mul_zero, sub_zero, neg_mul, neg_div,
          show (2 : ℝ) - 1 = 1 by norm_num, one_mul] using hFTC
      _ = 2 * Real.arctan (D / (2 * Real.sqrt (1 - D ^ 2 / 4))) := by rw [Real.arctan_neg]; ring
      _ = _ := twice_arctan_eq_arccos_chord hD hD2
  rw [hresult]




theorem unitSlice_metric_edist_le_angle_of_metric_segment
    (hcover : ∀ x : AsymptoticConeUnitSlice p hc,
      ∃ (d : UnitSliceRadialChartData hc n) (z : d.Level), (d.levelHomeomorph z).1 = x)
    (x y : AsymptoticConeUnitSlice p hc) (hxy : dist x y < 2)
    (γ : ℝ → AsymptoticCone p hc) (hγ0 : γ 0 = x.1) (hγ1 : γ 1 = y.1)
    (hγ : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      dist (γ s) (γ t) = |s - t| * dist x y) :
    letI := unitSliceChartedSpace hc n hcover
    letI := unitSlice_isManifold hc n hcover
    (unitSliceMetric hcover).edist x y ≤ ENNReal.ofReal (Real.arccos (1 - dist x y ^ 2 / 2)) := by
  let := unitSliceChartedSpace hc n hcover
  let := unitSlice_isManifold hc n hcover
  let θ := fun s : ℝ => asymptoticConeUnitDirection hc x (γ s)
  have hbound := asymptoticConeRadius_lower_bound_on_unit_segment hc x y hxy γ hγ0 hγ1 hγ
  have hpositive (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : 0 < asymptoticConeRadius hc (γ t) :=
    hbound.1.trans_le (hbound.2 t ht).2
  obtain ⟨P, hP⟩ := exists_normalized_path_of_metric_segment hc x y hxy γ hγ0 hγ1 hγ
  have hθP (t : unitInterval) : θ t = P t := by
    apply Subtype.ext
    exact (asymptoticConeUnitDirection_val x (hpositive t t.property)).trans (hP t).symm
  have hθcont : ContinuousOn θ (Icc (0 : ℝ) 1) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    exact P.continuous.congr (fun t => (hθP t).symm)
  have hθ0 : θ 0 = x := (hθP 0).trans P.source
  have hθ1 : θ 1 = y := (hθP 1).trans P.target
  have hθsmooth := (tangentNorm_unitDirection_of_metric_segment hcover x y hxy γ hγ0 hγ1 hγ).1
  have hlength := pathELength_unitDirection_of_metric_segment hcover x y hxy γ hγ0 hγ1 hγ
  let g := unitSliceMetric hcover
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : AsymptoticConeUnitSlice p hc → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : AsymptoticConeUnitSlice p hc → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace (AsymptoticConeUnitSlice p hc) := EMetricSpace.ofRiemannianMetric (𝓡 n) _
  let l := 𝓝[Ioo (0 : ℝ) (1 / 2)] 0
  have hl : NeBot l := by
    dsimp only [l]
    apply mem_closure_iff_nhdsWithin_neBot.mp
    rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1 / 2)]
    norm_num
  have hs : Tendsto (fun s : ℝ => s) l (𝓝[Icc (0 : ℝ) 1] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact ⟨hs.1.le, by linarith [hs.2]⟩
  have ht : Tendsto (fun s : ℝ => 1 - s) l (𝓝[Icc (0 : ℝ) 1] 1) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · have hc1 : Continuous (fun s : ℝ => 1 - s) := continuous_const.sub continuous_id
      have hh := (hc1.tendsto 0).mono_left
        (nhdsWithin_le_nhds (s := Ioo (0 : ℝ) (1 / 2)))
      simpa only [sub_zero] using hh
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have hlimit : Tendsto (fun s : ℝ => g.edist (θ s) (θ (1 - s))) l (𝓝 (g.edist x y)) := by
    have hh := ((hθcont 0 (by norm_num)).tendsto.comp hs).edist
      ((hθcont 1 (by norm_num)).tendsto.comp ht)
    rw [hθ0, hθ1] at hh
    convert! hh using 1
  apply le_of_tendsto hlimit
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hst : s ≤ 1 - s := by linarith [hs.2]
  have hsub : Icc s (1 - s) ⊆ Ioo (0 : ℝ) 1 := by
    intro u hu
    exact ⟨lt_of_lt_of_le hs.1 hu.1, by linarith [hu.2, hs.1]⟩
  have hdist : g.edist (θ s) (θ (1 - s)) ≤ g.pathELength θ s (1 - s) :=
    Manifold.riemannianEDist_le_pathELength ((hθsmooth.of_le (by simp)).mono hsub) rfl rfl hst
  exact hdist.trans ((Manifold.pathELength_mono hs.1.le (by linarith [hs.1])).trans_eq hlength)

end Poincare.AncientVolume.ScalarRatio

namespace PoincareConjecture.RiemannianMetric

open Poincare.AncientVolume.ScalarRatio



theorem unitSlice_metric_edist_le_angle_of_metricComplete
    {m n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M] [ConnectedSpace M]
    [NoncompactSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin m)) M] [IsManifold (𝓡 m) ∞ M]
    (g : RiemannianMetric m M) (D : LeviCivitaData g)
    (hcomplete : MetricComplete g) (hsec : D.NonnegativeSectionalCurvature) (p : M) :
    letI := g.toMetricSpace
    let hc := g.rayComparison_of_metricComplete D hcomplete hsec p
    ∀ hcover : ∀ x : AsymptoticConeUnitSlice p hc,
      ∃ (d : UnitSliceRadialChartData hc n) (z : d.Level), (d.levelHomeomorph z).1 = x,
    letI := unitSliceChartedSpace hc n hcover
    letI := unitSlice_isManifold hc n hcover
    ∀ x y : AsymptoticConeUnitSlice p hc, dist x y < 2 →
      (unitSliceMetric hcover).edist x y ≤ ENNReal.ofReal (Real.arccos (1 - dist x y ^ 2 / 2)) := by
  let := g.toMetricSpace
  dsimp only
  intro hcover
  let hc := g.rayComparison_of_metricComplete D hcomplete hsec p
  let := unitSliceChartedSpace hc n hcover
  let := unitSlice_isManifold hc n hcover
  intro x y hxy
  obtain ⟨γ, hγ0, hγ1, hγ⟩ := g.exists_asymptoticCone_metric_segment D hcomplete hsec p x.1 y.1
  exact unitSlice_metric_edist_le_angle_of_metric_segment hcover x y hxy γ hγ0 hγ1 hγ

end PoincareConjecture.RiemannianMetric
