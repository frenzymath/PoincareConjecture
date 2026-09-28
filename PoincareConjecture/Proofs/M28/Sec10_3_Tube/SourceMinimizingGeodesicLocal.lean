import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceMinimizingGeodesic
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.IntrinsicLocalPaths
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Polar.NoBranching











noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal Bundle

universe u

namespace PoincareConjecture.M28

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]

private theorem exists_minimizing_leg_with_speed
    (g : RiemannianMetric 3 M) (p q : M) {R d : ℝ}
    (hR : 0 < R) (hcompact : IsCompact (closure (g.ball p R)))
    (hd : 0 ≤ d) (hdR : d < R) (hpq : g.edist p q = ENNReal.ofReal d) :
    ∃ α : ℝ → M, ∃ v : EuclideanSpace ℝ (Fin 3),
      g.IsGeodesicOn α (Icc (0 : ℝ) 1) ∧ α 0 = p ∧ α 1 = q ∧
      HasDerivAt (fun t => extChartAt (𝓡 3) p (α t)) v 0 ∧
      g.tangentNorm p v = d ∧
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        g.edist (α s) (α t) ≤ ENNReal.ofReal (|s - t| * d) := by
  have hq : q ∈ g.ball p R := by
    change g.edist p q < ENNReal.ofReal R
    rw [hpq]
    exact (ENNReal.ofReal_lt_ofReal_iff hR).mpr hdR
  obtain ⟨ε, hε, α, hα, hα0, hα1, hseg⟩ :=
    g.exists_minimizing_geodesic_of_precompact_ball p q hR hcompact hq
  have hI : Icc (0 : ℝ) 1 ⊆ Ioo (-ε) (1 + ε) := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hv := (hα.hasDerivAt_chart_at (t := 0)
    (hI (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num)) p
    (by simpa only [hα0] using mem_extChartAt_source (I := 𝓡 3) p)).1
  have hnorm := hα.initial_tangentNorm_eq_of_edist_segment hε hα0 hv hseg
  rw [hpq] at hnorm
  have hnorm' := congrArg ENNReal.toReal hnorm
  have hspeed : g.tangentNorm p
      (deriv (fun t => extChartAt (𝓡 3) p (α t)) 0) = d := by
    have hvnonneg : 0 ≤ g.tangentNorm p
        (deriv (fun t => extChartAt (𝓡 3) p (α t)) 0) := Real.sqrt_nonneg _
    simpa only [ENNReal.toReal_ofReal hvnonneg,
      ENNReal.toReal_ofReal hd] using hnorm'
  refine ⟨α, _, fun t ht => hα t (hI ht), hα0, hα1, hv, hspeed, ?_⟩
  intro s hs t ht
  rw [hseg s hs t ht, hpq, ENNReal.ofReal_mul (abs_nonneg _)]

omit [T2Space M] in
private theorem tangentNorm_smul (g : RiemannianMetric 3 M)
    (p : M) (a : ℝ) (v : EuclideanSpace ℝ (Fin 3)) :
    g.tangentNorm p (a • v) = |a| * g.tangentNorm p v := by
  simp only [RiemannianMetric.tangentNorm, map_smul, smul_apply, smul_eq_mul]
  rw [← mul_assoc, ← pow_two, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq_eq_abs]




theorem exists_geodesic_eq_metric_segment_of_right_anchor
    (g : RiemannianMetric 3 M) {η : ℝ → M} {a b c R : ℝ}
    (hab : a < b) (hbc : b < c) (hR : 0 < R)
    (hcompact : IsCompact (closure (g.ball (η b) R)))
    (hleft : b - a < R) (hright : c - b < R)
    (hsegment : ∀ s ∈ Icc a c, ∀ t ∈ Icc a c,
      g.edist (η s) (η t) = ENNReal.ofReal |s - t|) :
    ∃ ξ : ℝ → M, g.IsGeodesicOn ξ (Icc a b) ∧ EqOn ξ η (Icc a b) ∧
      ∀ t ∈ Icc a b,
        g.tangentNorm (ξ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) ξ t 1) = 1 := by
  have ha : a ∈ Icc a c := ⟨le_rfl, (hab.trans hbc).le⟩
  have hb : b ∈ Icc a c := ⟨hab.le, hbc.le⟩
  have hc : c ∈ Icc a c := ⟨(hab.trans hbc).le, le_rfl⟩
  have hA : 0 < b - a := sub_pos.mpr hab
  have hB : 0 < c - b := sub_pos.mpr hbc
  obtain ⟨α, v, hα, hα0, hα1, hαv, hv, hαupper⟩ :=
    exists_minimizing_leg_with_speed g (η b) (η a) hR hcompact hA.le hleft
      (by simpa only [abs_of_pos hA] using hsegment b hb a ha)
  obtain ⟨β, w, hβ, hβ0, hβ1, hβv, hw, hβupper⟩ :=
    exists_minimizing_leg_with_speed g (η b) (η c) hR hcompact hB.le hright
      (by simpa only [abs_of_neg (sub_neg.mpr hbc), neg_sub] using hsegment b hb c hc)
  have hnorm : (c - b)⁻¹ • w = -((b - a)⁻¹ • v) := by
    have h := g.normalized_initial_eq_neg_of_minimizing_broken_geodesics (η b)
      hα hβ hα0 hβ0 hαv hβv (by simpa only [hv] using hA)
      (by simpa only [hw] using hB)
      (by simpa only [hv] using hαupper) (by simpa only [hw] using hβupper) ?_
    · simpa only [hv, hw] using h
    · rw [hα1, hβ1, hv, hw, hsegment a ha c hc,
        abs_of_neg (sub_neg.mpr (hab.trans hbc)), neg_sub]
      congr 1
      ring
  have hread : ∀ t ∈ Icc a b, α ((b - t) / (b - a)) = η t := by
    intro t ht
    rcases eq_or_lt_of_le ht.2 with rfl | htb
    · simpa only [sub_self, zero_div] using hα0
    have htac : t ∈ Icc a c := ⟨ht.1, ht.2.trans hbc.le⟩
    have hT : 0 < b - t := sub_pos.mpr htb
    have hTR : b - t < R := (sub_le_sub_left ht.1 b).trans_lt hleft
    obtain ⟨δ, z, hδ, hδ0, hδ1, hδv, hz, hδupper⟩ :=
      exists_minimizing_leg_with_speed g (η b) (η t) hR hcompact hT.le hTR
        (by simpa only [abs_of_pos hT] using hsegment b hb t htac)
    have hnorm' : (c - b)⁻¹ • w = -((b - t)⁻¹ • z) := by
      have h := g.normalized_initial_eq_neg_of_minimizing_broken_geodesics (η b)
        hδ hβ hδ0 hβ0 hδv hβv (by simpa only [hz] using hT)
        (by simpa only [hw] using hB)
        (by simpa only [hz] using hδupper) (by simpa only [hw] using hβupper) ?_
      · simpa only [hz, hw] using h
      · rw [hδ1, hβ1, hz, hw, hsegment t htac c hc,
          abs_of_neg (sub_neg.mpr (htb.trans hbc)), neg_sub]
        congr 1
        ring
    have hvz : ((b - t) / (b - a)) • v = z := by
      have hh := neg_injective (hnorm.symm.trans hnorm')
      have hh' := congrArg (fun u : EuclideanSpace ℝ (Fin 3) => (b - t) • u) hh
      simpa only [smul_smul, mul_inv_cancel₀ hT.ne', one_smul, div_eq_mul_inv] using hh'
    let k := (b - t) / (b - a)
    have hk : k ∈ Icc (0 : ℝ) 1 :=
      ⟨(div_pos hT hA).le, (div_le_one hA).mpr (sub_le_sub_left ht.1 b)⟩
    have hscaled : g.IsGeodesicOn (fun u => α (k * u)) (Icc (0 : ℝ) 1) := by
      intro u hu
      exact hα.comp_mul k u
        ⟨mul_nonneg hk.1 hu.1, mul_le_one₀ hk.2 hu.1 hu.2⟩
    have hscaledv : HasDerivAt (fun u => extChartAt (𝓡 3) (η b) (α (k * u))) z 0 := by
      have hd : HasDerivAt (fun u => extChartAt (𝓡 3) (η b) (α u)) v (k * 0) := by
        simpa only [mul_zero] using hαv
      have hkv : k • v = z := hvz
      simpa only [Function.comp_def, mul_one, hkv] using
        hd.scomp 0 ((hasDerivAt_id (0 : ℝ)).const_mul k)
    have heq := RiemannianMetric.geodesic_endpoint_eq_of_initial_data hscaled hδ
      (by simpa only [mul_zero] using hα0) hδ0 hscaledv hδv
    simpa only [mul_one, hδ1] using heq
  let ξ := fun t => α ((b - t) / (b - a))
  have hξ : g.IsGeodesicOn ξ (Icc a b) := by
    have heq (t : ℝ) : (b - t) / (b - a) = (-(b - a)⁻¹) * t + b / (b - a) := by
      simp only [div_eq_mul_inv]
      ring
    have hf : ξ = fun t => α ((-(b - a)⁻¹) * t + b / (b - a)) := by
      funext t
      rw [← heq]
    rw [hf]
    intro t ht
    apply hα.comp_affine (-(b - a)⁻¹) (b / (b - a)) t
    change -(b - a)⁻¹ * t + b / (b - a) ∈ Icc (0 : ℝ) 1
    rw [← heq]
    exact ⟨div_nonneg (sub_nonneg.mpr ht.2) hA.le,
      (div_le_one hA).mpr (sub_le_sub_left ht.1 b)⟩
  have hξb : ξ b = η b := hread b ⟨hab.le, le_rfl⟩
  have hξv : HasDerivAt (fun t => extChartAt (𝓡 3) (η b) (ξ t))
      (-(b - a)⁻¹ • v) b := by
    have hd : HasDerivAt (fun t => extChartAt (𝓡 3) (η b) (α t)) v
        ((b - b) / (b - a)) := by simpa only [sub_self, zero_div] using hαv
    simpa only [ξ, Function.comp_def, Function.comp_apply, Pi.sub_apply, id_eq,
      zero_sub, neg_div, one_div] using
      hd.scomp b (((hasDerivAt_const b b).sub (hasDerivAt_id b)).div_const (b - a))
  have hspeedb : g.tangentNorm (ξ b) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) ξ b 1) = 1 := by
    rw [← Poincare.VolumeComparison.tangentNorm_coordDeriv_eq g hξ
      (show b ∈ Icc a b from ⟨hab.le, le_rfl⟩) hξb hξv,
      tangentNorm_smul, abs_neg, abs_of_pos (inv_pos.mpr hA), hv,
      inv_mul_cancel₀ hA.ne']
  refine ⟨ξ, hξ, hread, ?_⟩
  intro t ht
  exact (Poincare.VolumeComparison.tangentNorm_eq_of_mem_Icc g hξ ht
    ⟨hab.le, le_rfl⟩).trans hspeedb

private theorem exists_geodesic_germ_of_metric_segment_lt
    (g : RiemannianMetric 3 M) {η : ℝ → M} {a b t : ℝ}
    (ht : t ∈ Ico a b)
    (hsegment : ∀ s ∈ Icc a b, ∀ r ∈ Icc a b,
      g.edist (η s) (η r) = ENNReal.ofReal |s - r|) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ ξ : ℝ → M,
      g.IsGeodesicOn ξ {t} ∧ EqOn ξ η (Icc a b ∩ Ioo (t - ρ) (t + ρ)) ∧
      g.tangentNorm (ξ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) ξ t 1) = 1 := by
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace
    (EuclideanSpace ℝ (Fin 3)) M
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
      (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 3) M
  obtain ⟨R, hR, hcompact, _⟩ := exists_precompact_ball_subset_open g
    isOpen_univ (mem_univ (η t))
  let δ := min ((b - t) / 4) (R / 8)
  have hδ : 0 < δ := lt_min (by linarith [ht.2]) (by positivity)
  have hδb : δ ≤ (b - t) / 4 := min_le_left _ _
  have hδR : δ ≤ R / 8 := min_le_right _ _
  let x := max a (t - δ)
  let y := t + δ
  let z := t + 2 * δ
  have hxt : x ≤ t := max_le ht.1 (by linarith)
  have hax : a ≤ x := le_max_left _ _
  have hxl : t - δ ≤ x := le_max_right _ _
  have hxy : x < y := by dsimp [y]; linarith
  have hyz : y < z := by dsimp [y, z]; linarith
  have hzb : z ≤ b := by dsimp [z]; linarith
  have hyab : y ∈ Icc a b := by
    constructor
    · exact hax.trans hxy.le
    · exact hyz.le.trans hzb
  have hsub : Icc x z ⊆ Icc a b := Icc_subset_Icc hax hzb
  have hty : g.edist (η t) (η y) = ENNReal.ofReal δ := by
    rw [hsegment t ⟨ht.1, ht.2.le⟩ y hyab]
    have hh : t - y = -δ := by dsimp [y]; ring
    rw [hh, abs_neg, abs_of_pos hδ]
  have hball : g.ball (η y) (R / 2) ⊆ g.ball (η t) R := by
    intro q hq
    change edist (η t) q < ENNReal.ofReal R
    have hq' : edist (η y) q < ENNReal.ofReal (R / 2) := hq
    calc
      edist (η t) q ≤ edist (η t) (η y) + edist (η y) q := edist_triangle _ _ _
      _ = ENNReal.ofReal δ + edist (η y) q := by
        change g.edist (η t) (η y) + edist (η y) q = _
        rw [hty]
      _ < ENNReal.ofReal δ + ENNReal.ofReal (R / 2) :=
        ENNReal.add_lt_add_left ENNReal.ofReal_ne_top hq'
      _ = ENNReal.ofReal (δ + R / 2) :=
        (ENNReal.ofReal_add hδ.le (by positivity)).symm
      _ < ENNReal.ofReal R := (ENNReal.ofReal_lt_ofReal_iff hR).mpr (by linarith)
  have hcompactY : IsCompact (closure (g.ball (η y) (R / 2))) :=
    hcompact.of_isClosed_subset isClosed_closure (closure_mono hball)
  obtain ⟨ξ, hξ, heq, hspeed⟩ := exists_geodesic_eq_metric_segment_of_right_anchor g
    hxy hyz (show 0 < R / 2 by positivity) hcompactY
    (show y - x < R / 2 by dsimp [y]; linarith)
    (show z - y < R / 2 by dsimp [y, z]; linarith)
    (fun s hs r hr => hsegment s (hsub hs) r (hsub hr))
  have htx : t ∈ Icc x y := ⟨hxt, by dsimp [y]; linarith⟩
  refine ⟨δ / 2, by positivity, ξ, ?_, ?_, hspeed t htx⟩
  · intro s hs
    simpa only [mem_singleton_iff.mp hs] using hξ t htx
  · intro s hs
    apply heq
    refine ⟨max_le hs.1.1 ?_, ?_⟩
    · linarith [hs.2.1]
    · dsimp [y]
      linarith [hs.2.2]




theorem exists_geodesic_germ_of_metric_segment
    (g : RiemannianMetric 3 M) {η : ℝ → M} {a b : ℝ} (hab : a < b)
    (hsegment : ∀ s ∈ Icc a b, ∀ r ∈ Icc a b,
      g.edist (η s) (η r) = ENNReal.ofReal |s - r|)
    {t : ℝ} (ht : t ∈ Icc a b) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ ξ : ℝ → M,
      g.IsGeodesicOn ξ {t} ∧ EqOn ξ η (Icc a b ∩ Ioo (t - ρ) (t + ρ)) ∧
      g.tangentNorm (ξ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) ξ t 1) = 1 := by
  rcases eq_or_lt_of_le ht.2 with htb | htb
  · subst t
    let ηr := fun s => η (a + b - s)
    have hrev (s : ℝ) (hs : s ∈ Icc a b) : a + b - s ∈ Icc a b := by
      constructor <;> linarith [hs.1, hs.2]
    have hsegmentr : ∀ s ∈ Icc a b, ∀ r ∈ Icc a b,
        g.edist (ηr s) (ηr r) = ENNReal.ofReal |s - r| := by
      intro s hs r hr
      rw [hsegment (a + b - s) (hrev s hs) (a + b - r) (hrev r hr)]
      congr 1
      rw [show a + b - s - (a + b - r) = -(s - r) by ring, abs_neg]
    obtain ⟨ρ, hρ, ξ, hξ, heq, hspeed⟩ := exists_geodesic_germ_of_metric_segment_lt g
      (η := ηr) (t := a) ⟨le_rfl, hab⟩ hsegmentr
    let ζ := fun s => ξ (a + b - s)
    have hζ : g.IsGeodesicOn ζ {b} := by
      have hf : ζ = fun s => ξ ((-1) * s + (a + b)) := by
        funext s
        dsimp only [ζ]
        congr 1
        ring
      rw [hf]
      intro s hs
      have hs' : s = b := mem_singleton_iff.mp hs
      subst s
      apply hξ.comp_affine (-1) (a + b) b
      change (-1) * b + (a + b) = a
      ring
    have hζb : ζ b = ξ a := by simp only [ζ, add_sub_cancel_right]
    have hd := (hξ.hasDerivAt_chart_at (by simp : a ∈ ({a} : Set ℝ)) (ξ a)
      (mem_extChartAt_source (ξ a))).1
    let v := deriv (fun s => extChartAt (𝓡 3) (ξ a) (ξ s)) a
    have hv : g.tangentNorm (ξ a) v = 1 :=
      (Poincare.VolumeComparison.tangentNorm_coordDeriv_eq g hξ (by simp) rfl hd).trans hspeed
    have hd' : HasDerivAt (fun s => extChartAt (𝓡 3) (ξ a) (ζ s)) (-v) b := by
      have hh : HasDerivAt (fun s => extChartAt (𝓡 3) (ξ a) (ξ s)) v (a + b - b) := by
        simpa only [add_sub_cancel_right] using hd
      simpa only [ζ, Function.comp_def, Function.comp_apply, Pi.sub_apply, id_eq,
        zero_sub, neg_one_smul] using
        hh.scomp b ((hasDerivAt_const b (a + b)).sub (hasDerivAt_id b))
    have hζspeed : g.tangentNorm (ζ b) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) ζ b 1) = 1 := by
      rw [← Poincare.VolumeComparison.tangentNorm_coordDeriv_eq g hζ
        (by simp : b ∈ ({b} : Set ℝ)) hζb hd']
      have hsmul := tangentNorm_smul g (ξ a) (-1) v
      simpa only [neg_one_smul, abs_neg, abs_one, one_mul, hv] using hsmul
    refine ⟨ρ, hρ, ζ, hζ, ?_, hζspeed⟩
    intro s hs
    have hr : a + b - s ∈ Icc a b ∩ Ioo (a - ρ) (a + ρ) :=
      ⟨hrev s hs.1, by constructor <;> linarith [hs.2.1, hs.2.2]⟩
    have hh := heq hr
    have hundo : a + b - (a + b - s) = s := by ring
    simpa only [ζ, ηr, hundo] using hh
  · exact exists_geodesic_germ_of_metric_segment_lt g ⟨ht.1, htb⟩ hsegment

end PoincareConjecture.M28
