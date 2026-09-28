import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Connection
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.Hom.Set
import Mathlib.Order.Interval.Set.OrderIso
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Tactic













set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff Bundle ENNReal

namespace PoincareConjecture.RicciFlowAnalysis



theorem exists_positive_speed_reparam {v : ℝ → ℝ}
    (hv : Continuous v) (hv0 : ∀ t, 0 ≤ v t) {δ : ℝ} (hδ : 0 < δ) :
    ∃ θ : ℝ ≃o ℝ, θ 0 = 0 ∧ θ 1 = 1 ∧ ContDiff ℝ 1 (θ : ℝ → ℝ) ∧
      ∀ u, HasDerivAt (θ : ℝ → ℝ)
        (((∫ s in (0 : ℝ)..1, v s) + δ) / (v (θ u) + δ)) u := by
  let A : ℝ := (∫ s in (0 : ℝ)..1, v s) + δ
  have hℓ : 0 ≤ ∫ s in (0 : ℝ)..1, v s :=
    intervalIntegral.integral_nonneg zero_le_one (fun s _ => hv0 s)
  have hA : 0 < A := by dsimp [A]; linarith
  have hw : Continuous (fun s => v s + δ) := hv.add continuous_const
  let τ : ℝ → ℝ := fun t => (∫ s in (0 : ℝ)..t, v s + δ) / A
  have hτder (t : ℝ) : HasDerivAt τ ((v t + δ) / A) t := by
    exact (intervalIntegral.integral_hasDerivAt_right
      (hw.intervalIntegrable 0 t)
      hw.aestronglyMeasurable.stronglyMeasurableAtFilter
      hw.continuousAt).div_const A
  have hτcont : Continuous τ :=
    continuous_iff_continuousAt.mpr (fun t => (hτder t).continuousAt)
  have hτpos (t : ℝ) : 0 < (v t + δ) / A :=
    div_pos (add_pos_of_nonneg_of_pos (hv0 t) hδ) hA
  have hτmono : StrictMono τ := strictMono_of_hasDerivAt_pos hτder hτpos
  have hτ0 : τ 0 = 0 := by simp [τ]
  have hτ1 : τ 1 = 1 := by
    have hi : (∫ s in (0 : ℝ)..1, v s + δ) = A := by
      rw [intervalIntegral.integral_add (hv.intervalIntegrable _ _)
        (continuous_const.intervalIntegrable _ _)]
      simp [A]
    dsimp only [τ]
    rw [hi, div_self hA.ne']
  have hτlower (t : ℝ) (ht : 0 ≤ t) : δ * t / A ≤ τ t := by
    have hi : δ * t ≤ ∫ s in (0 : ℝ)..t, v s + δ := by
      simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_comm]
        using intervalIntegral.integral_mono_on (μ := volume)
          (f := fun _ : ℝ => δ) (g := fun s => v s + δ) ht
          (continuous_const.intervalIntegrable 0 t) (hw.intervalIntegrable 0 t)
          (fun s _ => le_add_of_nonneg_left (hv0 s))
    exact div_le_div_of_nonneg_right hi hA.le
  have hτupper (t : ℝ) (ht : t ≤ 0) : τ t ≤ δ * t / A := by
    have hi : δ * (0 - t) ≤ ∫ s in t..(0 : ℝ), v s + δ := by
      simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_comm]
        using intervalIntegral.integral_mono_on (μ := volume)
          (f := fun _ : ℝ => δ) (g := fun s => v s + δ) ht
          (continuous_const.intervalIntegrable t 0) (hw.intervalIntegrable t 0)
          (fun s _ => le_add_of_nonneg_left (hv0 s))
    have hi' : (∫ s in (0 : ℝ)..t, v s + δ) ≤ δ * t := by
      rw [intervalIntegral.integral_symm]
      nlinarith
    exact div_le_div_of_nonneg_right hi' hA.le
  have hτsurj : Function.Surjective τ := by
    intro y
    let B : ℝ := A * (|y| + 1) / δ
    have hB : 0 < B := by dsimp [B]; positivity
    have hscale : δ * B / A = |y| + 1 := by
      dsimp [B]
      field_simp [hA.ne', hδ.ne']
    change y ∈ Set.range τ
    apply mem_range_of_exists_le_of_exists_ge hτcont
    · refine ⟨-B, (hτupper (-B) (neg_nonpos.mpr hB.le)).trans ?_⟩
      rw [mul_neg, neg_div, hscale]
      linarith [neg_abs_le y]
    · refine ⟨B, le_trans ?_ (hτlower B hB.le)⟩
      rw [hscale]
      linarith [le_abs_self y]
  let S : ℝ ≃o ℝ := StrictMono.orderIsoOfSurjective τ hτmono hτsurj
  let θ : ℝ ≃o ℝ := S.symm
  have hτθ (u : ℝ) : τ (θ u) = u := S.apply_symm_apply u
  have hθ0 : θ 0 = 0 := by
    apply S.injective
    change τ (θ 0) = τ 0
    rw [hτθ, hτ0]
  have hθ1 : θ 1 = 1 := by
    apply S.injective
    change τ (θ 1) = τ 1
    rw [hτθ, hτ1]
  have hθder (u : ℝ) : HasDerivAt (θ : ℝ → ℝ) (A / (v (θ u) + δ)) u := by
    have h := HasDerivAt.of_local_left_inverse θ.continuous.continuousAt
      (hτder (θ u)) (hτpos (θ u)).ne' (Eventually.of_forall hτθ)
    simpa only [inv_div] using h
  have hθsmooth : ContDiff ℝ 1 (θ : ℝ → ℝ) := by
    apply contDiff_one_iff_deriv.mpr
    refine ⟨fun u => (hθder u).differentiableAt, ?_⟩
    have hder : deriv (θ : ℝ → ℝ) = fun u => A / (v (θ u) + δ) :=
      funext (fun u => (hθder u).deriv)
    rw [hder]
    exact continuous_const.div ((hv.comp θ.continuous).add continuous_const)
      (fun u => (add_pos_of_nonneg_of_pos (hv0 (θ u)) hδ).ne')
  exact ⟨θ, hθ0, hθ1, hθsmooth, hθder⟩

private theorem sq_integral_unit_le_integral_sq {v : ℝ → ℝ} (hv : Continuous v) :
    (∫ t in (0 : ℝ)..1, v t) ^ 2 ≤ ∫ t in (0 : ℝ)..1, (v t) ^ 2 := by
  let ℓ : ℝ := ∫ t in (0 : ℝ)..1, v t
  have hnonneg : 0 ≤ ∫ t in (0 : ℝ)..1, (v t - ℓ) ^ 2 :=
    intervalIntegral.integral_nonneg zero_le_one (fun t _ => sq_nonneg _)
  have hid : (∫ t in (0 : ℝ)..1, (v t - ℓ) ^ 2) =
      (∫ t in (0 : ℝ)..1, (v t) ^ 2) - ℓ ^ 2 := by
    calc
      _ = ∫ t in (0 : ℝ)..1, (v t) ^ 2 - (2 * ℓ) * v t + ℓ ^ 2 :=
        intervalIntegral.integral_congr (fun t _ => by ring)
      _ = _ := by
        have hiSq : IntervalIntegrable (fun t => (v t) ^ 2) volume 0 1 :=
          (hv.pow 2).intervalIntegrable _ _
        have hiMul : IntervalIntegrable (fun t => (2 * ℓ) * v t) volume 0 1 :=
          (continuous_const.mul hv).intervalIntegrable _ _
        rw [intervalIntegral.integral_add
          (hiSq.sub hiMul)
          (continuous_const.intervalIntegrable _ _)]
        rw [intervalIntegral.integral_sub hiSq hiMul]
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
        change (∫ t in (0 : ℝ)..1, (v t) ^ 2) - (2 * ℓ) * ℓ +
          (1 - 0) * ℓ ^ 2 = _
        ring
  rw [hid] at hnonneg
  dsimp only [ℓ] at hnonneg
  linarith

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]


noncomputable def pathSpeed (g : RiemannianMetric n M) (γ : ℝ → M) (t : ℝ) : ℝ :=
  g.tangentNorm (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1)


noncomputable def pathEnergy (g : RiemannianMetric n M) (γ : ℝ → M) : ℝ :=
  ∫ t in (0 : ℝ)..1, g.inner (γ t)
    (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1)

theorem pathSpeed_nonneg (g : RiemannianMetric n M) (γ : ℝ → M) (t : ℝ) :
    0 ≤ pathSpeed g γ t := Real.sqrt_nonneg _

theorem pathEnergy_eq_integral_pathSpeed_sq
    (g : RiemannianMetric n M) (γ : ℝ → M) :
    pathEnergy g γ = ∫ t in (0 : ℝ)..1, (pathSpeed g γ t) ^ 2 := by
  apply intervalIntegral.integral_congr
  intro t _
  apply (Real.sq_sqrt ?_).symm
  by_cases hv : mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1 = 0
  · simp [hv]
  · exact (g.pos (γ t) _ hv).le

theorem continuous_pathSpeed (g : RiemannianMetric n M) {γ : ℝ → M}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 γ) : Continuous (pathSpeed g γ) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  have hinput : Continuous
      (fun t : ℝ => (⟨t, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) :=
    (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ)).symm.continuous.comp
      (continuous_id.prodMk continuous_const)
  have hvelocity : Continuous (fun t : ℝ =>
      (⟨γ t, mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1⟩ : TangentBundle (𝓡 n) M)) :=
    (hγ.continuous_tangentMap le_rfl).comp hinput
  exact (hvelocity.inner_bundle hvelocity).sqrt

theorem pathELength_eq_ofReal_integral_pathSpeed
    (g : RiemannianMetric n M) {γ : ℝ → M}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 γ) {a b : ℝ} (hab : a ≤ b) :
    g.pathELength γ a b = ENNReal.ofReal (∫ t in a..b, pathSpeed g γ t) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  change Manifold.pathELength (𝓡 n) γ a b = _
  rw [Manifold.pathELength_eq_lintegral_mfderiv_Icc]
  have hnorm (t : ℝ) : ‖mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1‖ₑ =
      ENNReal.ofReal (pathSpeed g γ t) := by
    rw [← ofReal_norm, norm_eq_sqrt_real_inner]
    rfl
  simp_rw [hnorm]
  rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
  exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
    (continuous_pathSpeed g hγ).continuousOn.integrableOn_Icc
    (Eventually.of_forall (pathSpeed_nonneg g γ))).symm

set_option backward.isDefEq.respectTransparency false in


theorem exists_path_energy_reparam
    (g : RiemannianMetric n M) {γ : ℝ → M}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 γ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ η : ℝ → M, η 0 = γ 0 ∧ η 1 = γ 1 ∧
      ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 η ∧
      η '' Icc (0 : ℝ) 1 = γ '' Icc (0 : ℝ) 1 ∧
      g.pathELength η 0 1 = g.pathELength γ 0 1 ∧
      (∀ t, pathSpeed g η t ≤ (∫ s in (0 : ℝ)..1, pathSpeed g γ s) + δ) ∧
      (∫ s in (0 : ℝ)..1, pathSpeed g γ s) ^ 2 ≤ pathEnergy g η ∧
      pathEnergy g η ≤ ((∫ s in (0 : ℝ)..1, pathSpeed g γ s) + δ) ^ 2 := by
  obtain ⟨θ, hθ0, hθ1, hθsmooth, hθder⟩ := exists_positive_speed_reparam
    (continuous_pathSpeed g hγ) (pathSpeed_nonneg g γ) hδ
  let η : ℝ → M := γ ∘ (θ : ℝ → ℝ)
  let ℓ : ℝ := ∫ s in (0 : ℝ)..1, pathSpeed g γ s
  let A : ℝ := ℓ + δ
  have hℓ : 0 ≤ ℓ := intervalIntegral.integral_nonneg zero_le_one
    (fun s _ => pathSpeed_nonneg g γ s)
  have hA : 0 < A := by dsimp only [A]; linarith
  have hηsmooth : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 η :=
    hγ.comp hθsmooth.contMDiff
  have hηimage : η '' Icc (0 : ℝ) 1 = γ '' Icc (0 : ℝ) 1 := by
    dsimp only [η]
    rw [Set.image_comp, θ.image_Icc, hθ0, hθ1]
  have hlength : g.pathELength η 0 1 = g.pathELength γ 0 1 := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    change Manifold.pathELength (𝓡 n) (γ ∘ (θ : ℝ → ℝ)) 0 1 =
      Manifold.pathELength (𝓡 n) γ 0 1
    simpa only [hθ0, hθ1] using
      Manifold.pathELength_comp_of_monotoneOn (I := 𝓡 n) (γ := γ)
        zero_le_one (θ.monotone.monotoneOn _)
        (hθsmooth.differentiable one_ne_zero).differentiableOn
        (hγ.mdifferentiable one_ne_zero).mdifferentiableOn
  have hspeed (t : ℝ) : pathSpeed g η t =
      (A / (pathSpeed g γ (θ t) + δ)) * pathSpeed g γ (θ t) := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    have hfactor : 0 ≤ A / (pathSpeed g γ (θ t) + δ) :=
      (div_pos hA (add_pos_of_nonneg_of_pos (pathSpeed_nonneg g γ _) hδ)).le
    have hθvalue : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (θ : ℝ → ℝ) t 1 =
        A / (pathSpeed g γ (θ t) + δ) := by
      simpa +instances only [mfderiv_eq_fderiv, fderiv_apply_one_eq_deriv] using!
        (hθder t).deriv
    have hvelocity : mfderiv 𝓘(ℝ, ℝ) (𝓡 n) η t 1 =
        (A / (pathSpeed g γ (θ t) + δ)) •
          mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ (θ t) 1 := by
      dsimp only [η]
      rw [mfderiv_comp_apply t (hγ.mdifferentiableAt one_ne_zero)
        (hθder t).differentiableAt.mdifferentiableAt, hθvalue]
      change mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ (θ t) (A / (pathSpeed g γ (θ t) + δ)) =
        (A / (pathSpeed g γ (θ t) + δ)) • mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ (θ t) 1
      simpa only [smul_eq_mul, mul_one] using!
        map_smul (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ (θ t))
          (A / (pathSpeed g γ (θ t) + δ)) (1 : ℝ)
    have hnorm (β : ℝ → M) (s : ℝ) : pathSpeed g β s =
        ‖mfderiv 𝓘(ℝ, ℝ) (𝓡 n) β s 1‖ := by
      rw [norm_eq_sqrt_real_inner]
      rfl
    rw [hnorm η t, hvelocity, norm_smul, Real.norm_of_nonneg hfactor, ← hnorm γ (θ t)]
  have hbound (t : ℝ) : pathSpeed g η t ≤ A := by
    rw [hspeed, div_mul_eq_mul_div]
    apply (div_le_iff₀
      (add_pos_of_nonneg_of_pos (pathSpeed_nonneg g γ _) hδ)).mpr
    nlinarith [mul_nonneg hA.le hδ.le]
  have hint : (∫ t in (0 : ℝ)..1, pathSpeed g η t) = ℓ := by
    rw [pathELength_eq_ofReal_integral_pathSpeed g hηsmooth zero_le_one,
      pathELength_eq_ofReal_integral_pathSpeed g hγ zero_le_one] at hlength
    exact (ENNReal.ofReal_eq_ofReal_iff
      (intervalIntegral.integral_nonneg zero_le_one
        (fun t _ => pathSpeed_nonneg g η t)) hℓ).mp hlength
  have hlower : ℓ ^ 2 ≤ pathEnergy g η := by
    rw [pathEnergy_eq_integral_pathSpeed_sq]
    simpa only [hint] using sq_integral_unit_le_integral_sq (continuous_pathSpeed g hηsmooth)
  have hupper : pathEnergy g η ≤ A ^ 2 := by
    rw [pathEnergy_eq_integral_pathSpeed_sq]
    calc
      _ ≤ ∫ _t in (0 : ℝ)..1, A ^ 2 :=
        intervalIntegral.integral_mono_on zero_le_one
          (((continuous_pathSpeed g hηsmooth).pow 2).intervalIntegrable _ _)
          (continuous_const.intervalIntegrable _ _)
          (fun t _ => by
            change (pathSpeed g η t) ^ 2 ≤ A ^ 2
            nlinarith [mul_nonneg (sub_nonneg.mpr (hbound t))
              (add_nonneg hA.le (pathSpeed_nonneg g η t))])
      _ = A ^ 2 := by simp
  exact ⟨η, by simp [η, hθ0], by simp [η, hθ1], hηsmooth,
    hηimage, hlength, hbound, hlower, hupper⟩



theorem exists_contMDiff_energy_path_sequence
    (g : RiemannianMetric n M) {p q : M} {R : ℝ}
    (hfinite : g.edist p q ≠ ⊤) (hR : (g.edist p q).toReal < R) :
    ∃ γ : ℕ → ℝ → M,
      (∀ j, γ j 0 = p ∧ γ j 1 = q ∧ ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 (γ j)) ∧
      (∀ j, MapsTo (γ j) (Icc (0 : ℝ) 1) (g.ball p R)) ∧
      (∀ j t, t ∈ Icc (0 : ℝ) 1 → pathSpeed g (γ j) t ≤ R) ∧
      (∀ j, (g.edist p q).toReal ^ 2 ≤ pathEnergy g (γ j) ∧
        pathEnergy g (γ j) ≤ R ^ 2) ∧
      Tendsto (fun j => pathEnergy g (γ j)) atTop (𝓝 ((g.edist p q).toReal ^ 2)) := by
  classical
  let d : ℝ := (g.edist p q).toReal
  have hd0 : 0 ≤ d := ENNReal.toReal_nonneg
  have hdR : d < R := hR
  have hRd : 0 < R - d := sub_pos.mpr hdR
  have hd : ENNReal.ofReal d = g.edist p q := ENNReal.ofReal_toReal hfinite
  let ε : ℕ → ℝ := fun j => ((R - d) / 4) * (1 / ((j : ℝ) + 1))
  have hεpos (j : ℕ) : 0 < ε j := by
    dsimp [ε]
    positivity
  have hεle (j : ℕ) : ε j ≤ (R - d) / 4 := by
    have hi : 1 / ((j : ℝ) + 1) ≤ 1 := by
      apply (div_le_iff₀ (by positivity : 0 < (j : ℝ) + 1)).mpr
      have := Nat.cast_nonneg (α := ℝ) j
      linarith
    exact mul_le_of_le_one_right (by positivity) hi
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    simpa only [ε, mul_zero] using
      (tendsto_const_nhds (x := (R - d) / 4)).mul
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hcap0 (j : ℕ) : 0 ≤ d + 2 * ε j := by
    have := hεpos j
    positivity
  have hcapR (j : ℕ) : d + 2 * ε j ≤ R := by
    have := hεle j
    linarith
  have hpaths (j : ℕ) : ∃ γ : ℝ → M,
      γ 0 = p ∧ γ 1 = q ∧ ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 γ ∧
      MapsTo γ (Icc (0 : ℝ) 1) (g.ball p R) ∧
      (∀ t, pathSpeed g γ t ≤ R) ∧
      d ^ 2 ≤ pathEnergy g γ ∧ pathEnergy g γ ≤ (d + 2 * ε j) ^ 2 := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    have hthreshold : g.edist p q < ENNReal.ofReal (d + ε j) := by
      rw [← hd]
      exact (ENNReal.ofReal_lt_ofReal_iff
        (add_pos_of_nonneg_of_pos hd0 (hεpos j))).mpr (by linarith [hεpos j])
    obtain ⟨β, hβ0, hβ1, hβsmooth, hβshort, _⟩ :=
      Manifold.exists_lt_locally_constant_of_riemannianEDist_lt
        (I := 𝓡 n) hthreshold zero_lt_one
    change g.pathELength β 0 1 < ENNReal.ofReal (d + ε j) at hβshort
    let ℓ : ℝ := ∫ s in (0 : ℝ)..1, pathSpeed g β s
    have hℓ0 : 0 ≤ ℓ := intervalIntegral.integral_nonneg zero_le_one
      (fun s _ => pathSpeed_nonneg g β s)
    have hβlen : g.pathELength β 0 1 = ENNReal.ofReal ℓ :=
      pathELength_eq_ofReal_integral_pathSpeed g hβsmooth zero_le_one
    have hdist : g.edist p q ≤ g.pathELength β 0 1 :=
      Manifold.riemannianEDist_le_pathELength hβsmooth.contMDiffOn hβ0 hβ1 zero_le_one
    have hdℓ : d ≤ ℓ := by
      rw [← hd, hβlen] at hdist
      exact (ENNReal.ofReal_le_ofReal_iff hℓ0).mp hdist
    have hℓlt : ℓ < d + ε j := by
      rw [hβlen] at hβshort
      exact (ENNReal.ofReal_lt_ofReal_iff
        (add_pos_of_nonneg_of_pos hd0 (hεpos j))).mp hβshort
    have hβR : g.pathELength β 0 1 < ENNReal.ofReal R :=
      hβshort.trans_le (ENNReal.ofReal_le_ofReal (by linarith [hcapR j, hεpos j]))
    have hβcarrier : MapsTo β (Icc (0 : ℝ) 1) (g.ball p R) := by
      intro t ht
      have hprefix : g.edist p (β t) ≤ g.pathELength β 0 t :=
        Manifold.riemannianEDist_le_pathELength hβsmooth.contMDiffOn hβ0 rfl ht.1
      have hmono : g.pathELength β 0 t ≤ g.pathELength β 0 1 :=
        Manifold.pathELength_mono le_rfl ht.2
      exact (hprefix.trans hmono).trans_lt hβR
    obtain ⟨γ, hγ0, hγ1, hγsmooth, hγimage, _hlength, hspeed, hElow, hEup⟩ :=
      exists_path_energy_reparam g hβsmooth (hεpos j)
    have hγcarrier : MapsTo γ (Icc (0 : ℝ) 1) (g.ball p R) := by
      rw [mapsTo_iff_image_subset, hγimage]
      exact mapsTo_iff_image_subset.mp hβcarrier
    have hγspeed (t : ℝ) : pathSpeed g γ t ≤ R :=
      (hspeed t).trans (by change ℓ + ε j ≤ R; linarith [hcapR j])
    have hElow' : d ^ 2 ≤ pathEnergy g γ := by
      have hsq : d ^ 2 ≤ ℓ ^ 2 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hdℓ) (add_nonneg hℓ0 hd0)]
      exact hsq.trans hElow
    have hEup' : pathEnergy g γ ≤ (d + 2 * ε j) ^ 2 := by
      apply hEup.trans
      change (ℓ + ε j) ^ 2 ≤ (d + 2 * ε j) ^ 2
      have := hεpos j
      nlinarith [mul_nonneg
        (show 0 ≤ d + 2 * ε j - (ℓ + ε j) by linarith)
        (show 0 ≤ d + 2 * ε j + (ℓ + ε j) by positivity)]
    exact ⟨γ, hγ0.trans hβ0, hγ1.trans hβ1, hγsmooth,
      hγcarrier, hγspeed, hElow', hEup'⟩
  choose γ hγ0 hγ1 hγsmooth hγcarrier hγspeed hElow hEup using hpaths
  have hupperlim : Tendsto (fun j => (d + 2 * ε j) ^ 2) atTop (𝓝 (d ^ 2)) := by
    simpa only [mul_zero, add_zero] using
      ((tendsto_const_nhds (x := d)).add
        ((tendsto_const_nhds (x := (2 : ℝ))).mul hεlim)).pow 2
  refine ⟨γ, fun j => ⟨hγ0 j, hγ1 j, hγsmooth j⟩, hγcarrier,
    fun j t _ => hγspeed j t, ?_, ?_⟩
  · intro j
    refine ⟨hElow j, (hEup j).trans ?_⟩
    nlinarith [mul_nonneg (sub_nonneg.mpr (hcapR j))
      (add_nonneg (le_trans hd0 hdR.le) (hcap0 j))]
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      hupperlim hElow hEup

end PoincareConjecture.RicciFlowAnalysis
