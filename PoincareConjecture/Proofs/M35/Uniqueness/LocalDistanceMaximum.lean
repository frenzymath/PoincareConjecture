import PoincareConjecture.Proofs.M35.Uniqueness.CompleteScalarMaximum

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.M35.Uniqueness

theorem exists_raw_local_distance_comparison
    (P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
    (G : PartialStandardCapFlow g₀) {T B L : ℝ}
    (hT : 0 < T) (hTlt : T < G.lifetime) (hB : 0 ≤ B) (hL : 0 ≤ L) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ ε : ℝ, 0 < ε →
      ∀ C₀ : Set StandardCapSpace, IsCompact C₀ →
      ∃ S : Set StandardCapSpace, IsCompact S ∧ C₀ ⊆ S ∧
      ∀ f : ℝ → StandardCapSpace → ℝ,
        ContinuousOn (Function.uncurry f) (Icc 0 T ×ˢ S) →
        (∀ t ∈ Ioc 0 T, ∀ x ∈ S, ContMDiffAt (𝓡 3) 𝓘(ℝ, ℝ) ∞ (f t) x) →
        (∀ x ∈ S, 0 ≤ f 0 x) →
        (∀ t ∈ Icc 0 T, ∀ x ∈ S, -B ≤ f t x) →
        (∀ t ∈ Ioc 0 T, ∀ x ∈ S, ∃ v : ℝ,
          HasDerivWithinAt (fun s => f s x) v (Icc 0 T) t ∧
            (G.flow.connection t).laplacian (f t) x + L * f t x ≤ v) →
        ∀ t ∈ Icc 0 T, ∀ x ∈ C₀,
          0 ≤ f t x + ε * Real.exp (A * t) * rawDistanceSquare G 0 t x := by
  obtain ⟨C, hC, hsupp⟩ := exists_complete_distance_square_supports P G hT.le hTlt
  let A := C + L
  have hA : 0 ≤ A := add_nonneg hC hL
  refine ⟨A, hA, ?_⟩
  intro ε hε C₀ hC₀
  obtain ⟨E, hE, _, hexhaust⟩ := exists_raw_distance_square_compact_exhaustion
    P G hT.le hTlt (0 : StandardCapSpace) 0 (A := B / ε) (by positivity)
  let S := E ∪ C₀
  have hS : IsCompact S := hE.union hC₀
  have hCS : C₀ ⊆ S := subset_union_right
  refine ⟨S, hS, hCS, ?_⟩
  intro f hcont hsmooth hinit hbound hheat t ht x hx
  let μ := rawDistanceSquare G (0 : StandardCapSpace)
  have hμ (s : ℝ) (y : StandardCapSpace) : 0 < μ s y := by
    dsimp [μ, rawDistanceSquare]
    positivity
  have hμcont := continuousOn_rawDistanceSquare G hT hTlt (0 : StandardCapSpace)
  have hecont : Continuous (fun z : ℝ × StandardCapSpace => Real.exp (A * z.1)) := by
    fun_prop
  let w : ℝ → StandardCapSpace → ℝ := fun s y =>
    f s y + ε * Real.exp (A * s) * μ s y
  have hwinitial (y : StandardCapSpace) (hy : y ∈ S) : 0 ≤ w 0 y :=
    add_nonneg (hinit y hy) (mul_nonneg (by positivity) (hμ 0 y).le)
  have hwboundary (s : ℝ) (hs : s ∈ Icc 0 T) (y : StandardCapSpace)
      (hy : y ∈ S \ interior S) : 0 ≤ w s y := by
    have hm := hexhaust s hs y (fun hh => hy.2 (interior_mono subset_union_left hh))
    have he : 1 ≤ Real.exp (A * s) := Real.one_le_exp_iff.mpr (mul_nonneg hA hs.1)
    have hmul := mul_le_mul_of_nonneg_left hm hε.le
    rw [mul_div_cancel₀ B hε.ne'] at hmul
    have hmore : ε * μ s y ≤ ε * Real.exp (A * s) * μ s y :=
      mul_le_mul_of_nonneg_right
        (by nlinarith : ε ≤ ε * Real.exp (A * s)) (hμ s y).le
    have hlow := hbound s hs y hy.1
    change 0 ≤ f s y + ε * Real.exp (A * s) * μ s y
    linarith
  have hwcont : ContinuousOn (Function.uncurry w) (Icc 0 T ×ˢ S) :=
    hcont.add (((continuous_const.mul hecont).continuousOn.mul hμcont).mono
      (prod_mono Subset.rfl (subset_univ S)))
  have hwtest (s : ℝ) (hs : s ∈ Ioc 0 T) (y : StandardCapSpace)
      (hy : y ∈ interior S) (hmin : ∀ z ∈ S, w s y ≤ w s z) (_hneg : w s y < 0)
      (δ : ℝ) (hδ : 0 < δ) :
      ∃ χ : ℝ → ℝ, ∃ v : ℝ,
        χ s = w s y ∧ (∀ᶠ r in 𝓝[Icc 0 s] s, w r y ≤ χ r) ∧
        HasDerivWithinAt χ v (Icc 0 s) s ∧ -(-L) * w s y - δ ≤ v := by
    let c := ε * Real.exp (A * s)
    have hc : 0 < c := mul_pos hε (Real.exp_pos _)
    obtain ⟨ψ, vμ, hψsmooth, hψtouch, hψspace, hψtime, hψderiv, hψheat⟩ :=
      hsupp s ⟨hs.1.le, hs.2⟩ 0 y (δ / c) (by positivity)
    obtain ⟨vf, hfderiv, hfheat⟩ := hheat s hs y (interior_subset hy)
    let χ : ℝ → StandardCapSpace → ℝ := fun r z =>
      f r z + ε * Real.exp (A * r) * ψ r z
    have htouch : χ s y = w s y := by dsimp [χ, w]; rw [hψtouch]
    have hfspace := hsmooth s hs y (interior_subset hy)
    have hχsmooth : ContMDiffAt (𝓡 3) 𝓘(ℝ, ℝ) ∞ (χ s) y :=
      hfspace.add (contMDiffAt_const.mul hψsmooth)
    have hlocal : IsLocalMin (χ s) y := by
      filter_upwards [hψspace, mem_of_superset (isOpen_interior.mem_nhds hy) interior_subset]
        with z hz hzS
      calc
        χ s y = w s y := htouch
        _ ≤ w s z := hmin z hzS
        _ ≤ χ s z := add_le_add le_rfl (mul_le_mul_of_nonneg_left hz hc.le)
    have hlap := (G.flow.connection s).laplacian_nonneg_of_isLocalMin hχsmooth hlocal
    have hlapeq : (G.flow.connection s).laplacian (χ s) y =
        (G.flow.connection s).laplacian (f s) y +
          c * (G.flow.connection s).laplacian (ψ s) y := by
      have hcsmooth : ContMDiffAt (𝓡 3) 𝓘(ℝ, ℝ) ∞ (fun z => c * ψ s z) y :=
        contMDiffAt_const.mul hψsmooth
      rw [show χ s = fun z => f s z + c * ψ s z from rfl,
        laplacian_add_at _ hfspace hcsmooth, LeviCivitaData.laplacian_const_mul]
    rw [hlapeq] at hlap
    have htime : ∀ᶠ r in 𝓝[Icc 0 s] s, w r y ≤ χ r y := by
      filter_upwards [self_mem_nhdsWithin] with r hr
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (hψtime r hr) (by positivity))
    have hederiv : HasDerivAt (fun r => ε * Real.exp (A * r)) (c * A) s := by
      convert! (((hasDerivAt_id s).const_mul A).exp.const_mul ε) using 1
      dsimp [c]
      ring
    have hderiv : HasDerivWithinAt (fun r => χ r y)
        (vf + c * (A * ψ s y + vμ)) (Icc 0 s) s := by
      convert! (hfderiv.mono (Icc_subset_Icc le_rfl hs.2)).add
        (hederiv.mul hψderiv).hasDerivWithinAt using 1
      ring
    refine ⟨fun r => χ r y, vf + c * (A * ψ s y + vμ), htouch, htime, hderiv, ?_⟩
    have hδeq : c * (δ / c) = δ := mul_div_cancel₀ δ hc.ne'
    have hscaled := mul_le_mul_of_nonneg_left hψheat hc.le
    rw [mul_sub, hδeq] at hscaled
    rw [hψtouch]
    change -(-L) * (f s y + c * μ s y) - δ ≤ vf + c * (A * μ s y + vμ)
    dsimp only [A]
    change c * (-C * μ s y) - δ ≤
      c * (vμ - (G.flow.connection s).laplacian (ψ s) y) at hscaled
    nlinarith [hfheat]
  exact M04.compact_subset_min_velocity_nonnegative_of_upper_support hS hT w
    hwinitial hwboundary hwcont hwtest t ht x (hCS hx)

end PoincareConjecture.M35.Uniqueness
