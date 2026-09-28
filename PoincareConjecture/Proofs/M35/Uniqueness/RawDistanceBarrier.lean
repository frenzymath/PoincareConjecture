import PoincareConjecture.Proofs.M35.RawFlow.Completeness
import PoincareConjecture.Proofs.M09.RiemannianProper
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Distance.Basic
import PoincareConjecture.Proofs.M04.ShiNativeDistanceSupport
import PoincareConjecture.Proofs.M04.LocalMetricComparison












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.M35.Uniqueness



noncomputable def rawDistanceSquare {g₀ : StandardInitialMetric}
    (G : PartialStandardCapFlow g₀) (p : StandardCapSpace)
    (t : ℝ) (x : StandardCapSpace) : ℝ :=
  1 + ((G.flow.metric t).edist p x).toReal ^ 2



theorem raw_distance_comparison_of_curvature_bound
    {g₀ : StandardInitialMetric} (G : PartialStandardCapFlow g₀)
    {T K : ℝ} (hT : T < G.lifetime) (hK : 0 ≤ K)
    (hRm : ∀ t ∈ Icc 0 T, ∀ x : StandardCapSpace,
      (G.flow.connection t).curvatureTensorNorm x ≤ K)
    {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) (hst : s ≤ t)
    (p q : StandardCapSpace) :
    ((G.flow.metric s).edist p q).toReal ≤
      Real.exp (3 * K * (t - s)) * ((G.flow.metric t).edist p q).toReal := by
  have hnorm (x : StandardCapSpace) (v : TangentSpace (𝓡 3) x) :
      (G.flow.metric s).tangentNorm x v ≤
        Real.exp (3 * K * (t - s)) * (G.flow.metric t).tangentNorm x v := by
    have h := (M04.tangentNorm_comparison_at_of_curvature_bound G.flow
      ⟨hs.1, hs.2.trans_lt hT⟩ ⟨ht.1, ht.2.trans_lt hT⟩ hst hK x
      (fun τ hτ => hRm τ ⟨hs.1.trans hτ.1, hτ.2.trans ht.2⟩ x) v).1
    have he : Real.exp (3 * K * (t - s)) * Real.exp (-3 * K * (t - s)) = 1 := by
      rw [← Real.exp_add]
      convert Real.exp_zero using 1
      congr 1
      ring
    have hh := mul_le_mul_of_nonneg_left h (Real.exp_pos (3 * K * (t - s))).le
    simpa only [Nat.cast_ofNat, ← mul_assoc, he, one_mul] using hh
  have hdist := RiemannianMetric.edist_le_mul_edist_of_tangentNorm_le
    (G.flow.metric t) (G.flow.metric s) (Real.exp_pos (3 * K * (t - s))) hnorm p q
  have hfin := (G.flow.metric t).edist_ne_top p q
  have hreal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) hdist
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le] using hreal




theorem exists_raw_distance_square_supports
    (P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
    (G : PartialStandardCapFlow g₀) {T : ℝ} (hT : 0 ≤ T) (hTlt : T < G.lifetime) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ t ∈ Icc 0 T, ∀ p q : StandardCapSpace,
        0 < ((G.flow.metric t).edist p q).toReal → ∀ ε > 0,
        ∃ ψ : ℝ → StandardCapSpace → ℝ, ∃ v : ℝ,
          ContMDiffAt (𝓡 3) 𝓘(ℝ, ℝ) ∞ (ψ t) q ∧
          ψ t q = rawDistanceSquare G p t q ∧
          (∀ᶠ y in 𝓝 q, rawDistanceSquare G p t y ≤ ψ t y) ∧
          (∀ s ∈ Icc 0 t, rawDistanceSquare G p s q ≤ ψ s q) ∧
          HasDerivAt (fun s => ψ s q) v t ∧
          -(12 * K + 8) * rawDistanceSquare G p t q - ε ≤
            v - (G.flow.connection t).laplacian (ψ t) q := by
  obtain ⟨K, hK, hbound⟩ := G.curvature_locally_bounded T hT hTlt
  have hRm (t : ℝ) (ht : t ∈ Icc 0 T) (x : StandardCapSpace) :
      (G.flow.connection t).curvatureTensorNorm x ≤ K :=
    (le_abs_self _).trans (hbound t ht x)
  refine ⟨K, hK, ?_⟩
  intro t ht p q hd ε hε
  let d := ((G.flow.metric t).edist p q).toReal
  have hd' : 0 < d := hd
  have hfin := (G.flow.metric t).edist_ne_top p q
  have hq : q ∈ (G.flow.metric t).ball p (d + 1) := by
    change (G.flow.metric t).edist p q < ENNReal.ofReal (d + 1)
    rw [← ENNReal.ofReal_toReal hfin]
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith : 0 < d + 1)).mpr (by dsimp [d]; linarith)
  have hcompact := Proofs.M09.isCompact_closure_metric_ball
    (G.flow.metric t) (G.complete P ⟨ht.1, ht.2.trans_lt hTlt⟩) p (d + 1)
  obtain ⟨U, u, hU, hqU, hu, huq, hupper, hgrad, hlap⟩ :=
    M04.exists_shi_native_distance_upper_support (G.flow.connection t) p q (d + 1) K
      hcompact hq hd hK (fun y _ => hRm t ht y) (ε / (2 * d)) (by positivity)
  let ψ : ℝ → StandardCapSpace → ℝ := fun s y =>
    1 + (Real.exp (3 * K * (t - s)) * u y) ^ 2
  have hψt : ψ t = fun y => 1 + (u y) ^ 2 := by
    funext y
    simp [ψ]
  have husmooth := hu.contMDiffAt (hU.mem_nhds hqU)
  have hup : ∀ᶠ y in 𝓝 q, 0 < u y := husmooth.continuousAt.eventually
    (lt_mem_nhds (by simpa only [huq] using hd))
  have hspace : ∀ᶠ y in 𝓝 q, rawDistanceSquare G p t y ≤ ψ t y := by
    filter_upwards [hU.mem_nhds hqU, hup] with y hy hyp
    rw [hψt]
    have hh := ENNReal.toReal_le_of_le_ofReal hyp.le (hupper y hy)
    exact add_le_add (le_refl 1) (sq_le_sq₀ ENNReal.toReal_nonneg hyp.le |>.mpr hh)
  have htime : ∀ s ∈ Icc 0 t, rawDistanceSquare G p s q ≤ ψ s q := by
    intro s hs
    have hh := raw_distance_comparison_of_curvature_bound G hTlt hK hRm
      ⟨hs.1, hs.2.trans ht.2⟩ ht hs.2 p q
    have hnonneg : 0 ≤ Real.exp (3 * K * (t - s)) * u q := by rw [huq]; positivity
    change 1 + _ ^ 2 ≤ 1 + _ ^ 2
    apply add_le_add le_rfl
    apply (sq_le_sq₀ ENNReal.toReal_nonneg hnonneg).mpr
    simpa only [huq] using hh
  have he : HasDerivAt (fun s : ℝ => Real.exp (3 * K * (t - s))) (-3 * K) t := by
    convert! (((hasDerivAt_const t t).sub (hasDerivAt_id t)).const_mul (3 * K)).exp using 1
    simp
  have hderiv : HasDerivAt (fun s => ψ s q) (-6 * K * d ^ 2) t := by
    convert! ((he.mul_const (u q)).pow 2).const_add 1 using 1
    simp only [sub_self, mul_zero, Real.exp_zero, one_mul, huq]
    dsimp only [d]
    ring
  let φ : ℝ → ℝ := fun z => 1 + z ^ 2
  have hφ : ContDiff ℝ ∞ φ := contDiff_const.add (contDiff_id.pow 2)
  have hφd : deriv φ = fun z => 2 * z := by
    funext z
    have hh : HasDerivAt φ (2 * z) z := by
      convert! ((hasDerivAt_id z).pow 2).const_add 1 using 1
      simp
    exact hh.deriv
  have hφdd : deriv (deriv φ) (u q) = 2 := by rw [hφd]; simp
  have hlapψ : (G.flow.connection t).laplacian (ψ t) q =
      2 * d * (G.flow.connection t).laplacian u q +
        2 * M04.scalarGradientSq (G.flow.metric t) u q := by
    rw [hψt]
    change (G.flow.connection t).laplacian (fun y => φ (u y)) q = _
    rw [M04.laplacian_comp (G.flow.connection t) hU hu hφ hqU, hφdd, hφd, huq]
  have hεeq : 2 * d * (ε / (2 * d)) = ε :=
    mul_div_cancel₀ ε (mul_ne_zero two_ne_zero hd'.ne')
  have hlapbound : (G.flow.connection t).laplacian (ψ t) q ≤ 8 + 6 * K * d ^ 2 + ε := by
    rw [hlapψ]
    have hh := mul_le_mul_of_nonneg_left hlap (by positivity : 0 ≤ 2 * d)
    have hdeq : 2 * d * ((3 : ℝ) / d + 3 * K * d + ε / (2 * d)) =
        6 + 6 * K * d ^ 2 + ε := by
      rw [mul_add, mul_add, hεeq]
      field_simp [hd'.ne']
      ring
    change 2 * d * (G.flow.connection t).laplacian u q ≤
      2 * d * (3 / d + 3 * K * d + ε / (2 * d)) at hh
    rw [hdeq] at hh
    nlinarith [hgrad]
  refine ⟨ψ, -6 * K * d ^ 2, ?_, ?_, hspace, htime, hderiv, ?_⟩
  · rw [hψt]
    exact contMDiffAt_const.add (husmooth.pow 2)
  · simp only [hψt, huq, rawDistanceSquare]
  · change -(12 * K + 8) * (1 + d ^ 2) - ε ≤ _
    nlinarith [sq_nonneg d]

end PoincareConjecture.M35.Uniqueness
