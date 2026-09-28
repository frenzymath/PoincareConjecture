import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Distance.Calabi
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.Cutoff.Support
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Extrema
import Mathlib.Analysis.Calculus.Deriv.Shift

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Bundle
open scoped Manifold ContDiff Topology Bundle

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

private lemma shifted_profile_operator_bounds (D : LeviCivitaData g)
    {ρ : M → ℝ} {U : Set M} (hU : IsOpen U) {x : M} (hx : x ∈ U)
    (hρ : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ ρ U)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hanti : Antitone χ)
    {A B C L δ d₀ : ℝ} (hδ : 0 < δ) (hL : 0 ≤ L)
    (hA : ∀ r, deriv χ r ^ 2 ≤ A * χ r)
    (hB : ∀ r, -B ≤ deriv (deriv χ) r) (hC : ∀ r, -C ≤ deriv χ r)
    (hgrad : g.inner x (D.gradient ρ x) (D.gradient ρ x) = 1)
    (hlap : D.laplacian ρ x ≤ L) :
    g.inner x (D.gradient (fun y => χ ((ρ y - d₀) / δ)) x)
        (D.gradient (fun y => χ ((ρ y - d₀) / δ)) x) ≤
          A / δ ^ 2 * χ ((ρ x - d₀) / δ) ∧
      -(B / δ ^ 2 + C * L / δ) ≤ D.laplacian (fun y => χ ((ρ y - d₀) / δ)) x := by
  obtain ⟨f, hf, heq⟩ := Poincare.Manifold.exists_contMDiff_eq_near hU hρ hx
  let η : ℝ → ℝ := fun r => χ (r - d₀ / δ)
  have hη : ContDiff ℝ ∞ η := hχ.comp (contDiff_id.sub contDiff_const)
  have hd (r : ℝ) : deriv η r = deriv χ (r - d₀ / δ) := deriv_comp_sub_const χ _ r
  have hd₂ (r : ℝ) : deriv (deriv η) r = deriv (deriv χ) (r - d₀ / δ) := by
    rw [show deriv η = fun r => deriv χ (r - d₀ / δ) from funext hd]
    exact deriv_comp_sub_const (deriv χ) _ r
  have hgf : D.gradient f x = D.gradient ρ x := by
    unfold gradient
    rw [Poincare.mvfderiv_eq_of_eventuallyEq heq]
  have hb := D.radial_profile_operator_bounds (x := x) hf hη
    (fun r s hrs => hanti (sub_le_sub_right hrs _)) hδ hL
    (fun r => by simpa only [hd, η] using hA (r - d₀ / δ))
    (fun r => by simpa only [hd₂] using hB (r - d₀ / δ))
    (fun r => by simpa only [hd] using hC (r - d₀ / δ))
    (by simpa only [hgf] using hgrad)
    (by simpa only [D.laplacian_eq_of_eventuallyEq heq] using hlap)
  have hcomp : (fun y => η (f y / δ)) =ᶠ[𝓝 x]
      (fun y => χ ((ρ y - d₀) / δ)) := by
    filter_upwards [heq] with y hy
    simp only [η, hy, sub_div]
  have hgc : D.gradient (fun y => η (f y / δ)) x =
      D.gradient (fun y => χ ((ρ y - d₀) / δ)) x := by
    unfold gradient
    rw [Poincare.mvfderiv_eq_of_eventuallyEq hcomp]
  simpa only [hgc, D.laplacian_eq_of_eventuallyEq hcomp, η, heq.self_of_nhds,
    sub_div] using hb

private lemma deriv_scaled_profile {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (d₀ δ r : ℝ) :
    deriv (fun z => χ ((z - d₀) / δ)) r = deriv χ ((r - d₀) / δ) / δ := by
  have h := ((hχ.differentiable (by simp) _).hasDerivAt).comp r
    (((hasDerivAt_id r).sub_const d₀).div_const δ)
  simpa only [Function.comp_def, id_eq, div_eq_mul_inv, one_mul] using h.deriv

private lemma laplacian_scaled_profile (D : LeviCivitaData g)
    {ρ : M → ℝ} {U : Set M} (hU : IsOpen U) {x : M} (hx : x ∈ U)
    (hρ : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ ρ U)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (d₀ δ : ℝ)
    (hgrad : g.inner x (D.gradient ρ x) (D.gradient ρ x) = 1) :
    D.laplacian (fun y => χ ((ρ y - d₀) / δ)) x =
      deriv χ ((ρ x - d₀) / δ) / δ * D.laplacian ρ x +
        deriv (deriv χ) ((ρ x - d₀) / δ) / δ ^ 2 := by
  obtain ⟨f, hf, heq⟩ := Poincare.Manifold.exists_contMDiff_eq_near hU hρ hx
  let η : ℝ → ℝ := fun r => χ ((r - d₀) / δ)
  have hη : ContDiff ℝ ∞ η :=
    hχ.comp ((contDiff_id.sub contDiff_const).div_const δ)
  have hd (r : ℝ) : deriv η r = deriv χ ((r - d₀) / δ) / δ :=
    deriv_scaled_profile hχ d₀ δ r
  have hd₂ (r : ℝ) : deriv (deriv η) r =
      deriv (deriv χ) ((r - d₀) / δ) / δ ^ 2 := by
    rw [show deriv η = fun r => deriv χ ((r - d₀) / δ) / δ from
      funext (deriv_scaled_profile hχ d₀ δ)]
    rw [deriv_div_const, deriv_scaled_profile (hχ.deriv' (n := ∞))]
    ring
  have hgf : D.gradient f x = D.gradient ρ x := by
    unfold gradient
    rw [Poincare.mvfderiv_eq_of_eventuallyEq heq]
  have hcomp : (η ∘ f) =ᶠ[𝓝 x] (fun y => χ ((ρ y - d₀) / δ)) := by
    filter_upwards [heq] with y hy
    simp only [Function.comp_apply, η, hy]
  have hl := D.laplacian_comp hf hη x
  simpa only [D.laplacian_eq_of_eventuallyEq hcomp,
    D.laplacian_eq_of_eventuallyEq heq, hgf, hgrad, mul_one,
    hd, hd₂, heq.self_of_nhds] using hl

theorem cutoff_heat_le_of_upper_support (D : LeviCivitaData g)
    {ρ : ℝ → M → ℝ} {t : ℝ} {U : Set M} (hU : IsOpen U) {x : M} (hx : x ∈ U)
    (hρ : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (ρ t) U)
    (htime : DifferentiableAt ℝ (fun s => ρ s x) t)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hanti : Antitone χ)
    {A B C H L δ d₀ : ℝ} (hδ : 0 < δ) (hH : 0 ≤ H) (hL : 0 ≤ L)
    (hA : ∀ r, deriv χ r ^ 2 ≤ A * χ r)
    (hB : ∀ r, -B ≤ deriv (deriv χ) r) (hC : ∀ r, -C ≤ deriv χ r)
    (hgrad : g.inner x (D.gradient (ρ t) x) (D.gradient (ρ t) x) = 1)
    (hlap : D.laplacian (ρ t) x ≤ L)
    (hderiv : -H ≤ deriv (fun s => ρ s x) t)
    (hpos : 0 < χ ((ρ t x - d₀) / δ)) :
    deriv (fun s => χ ((ρ s x - d₀) / δ)) t -
        D.laplacian (fun y => χ ((ρ t y - d₀) / δ)) x +
        2 * g.inner x (D.gradient (fun y => χ ((ρ t y - d₀) / δ)) x)
          (D.gradient (fun y => χ ((ρ t y - d₀) / δ)) x) / χ ((ρ t x - d₀) / δ) ≤
      C * H / δ + (B + 2 * A) / δ ^ 2 + C * L / δ := by
  obtain ⟨hg, hl⟩ := shifted_profile_operator_bounds D (d₀ := d₀) hU hx hρ hχ hanti hδ hL
    hA hB hC hgrad hlap
  have hd := ((hχ.differentiable (by simp) _).hasDerivAt).comp t
    ((htime.hasDerivAt.sub_const d₀).div_const δ)
  have hdeq : deriv (fun s => χ ((ρ s x - d₀) / δ)) t =
      deriv χ ((ρ t x - d₀) / δ) * (deriv (fun s => ρ s x) t / δ) := by
    simpa only [Function.comp_def] using hd.deriv
  have htbound : deriv (fun s => χ ((ρ s x - d₀) / δ)) t ≤ C * H / δ := by
    rw [hdeq]
    have h₁ := mul_le_mul_of_nonpos_left hderiv (hanti.deriv_nonpos (x := (ρ t x - d₀) / δ))
    have h₂ := mul_le_mul_of_nonneg_right (hC ((ρ t x - d₀) / δ)) hH
    have h₃ : deriv χ ((ρ t x - d₀) / δ) * deriv (fun s => ρ s x) t ≤ C * H := by
      nlinarith
    simpa only [Function.comp_def, mul_div_assoc] using
      div_le_div_of_nonneg_right h₃ hδ.le
  have hg' : 2 * g.inner x (D.gradient (fun y => χ ((ρ t y - d₀) / δ)) x)
      (D.gradient (fun y => χ ((ρ t y - d₀) / δ)) x) / χ ((ρ t x - d₀) / δ) ≤
      2 * A / δ ^ 2 := by
    apply (div_le_iff₀ hpos).mpr
    calc
      _ ≤ 2 * (A / δ ^ 2 * χ ((ρ t x - d₀) / δ)) :=
        mul_le_mul_of_nonneg_left hg (by norm_num)
      _ = _ := by ring
  calc
    _ ≤ C * H / δ + (B / δ ^ 2 + C * L / δ) + 2 * A / δ ^ 2 := by linarith
    _ = _ := by ring

private lemma deriv_eq_zero_of_flat {χ : ℝ → ℝ} (hanti : Antitone χ)
    (hflat : ∀ r, r ≤ 1 → χ r = 1) {r : ℝ} (hr : r ≤ 1) : deriv χ r = 0 := by
  have hm : IsLocalMax χ r := Filter.Eventually.of_forall (fun s => by
    rw [hflat r hr]
    by_cases hs : s ≤ 1
    · rw [hflat s hs]
    · exact (hanti (le_of_not_ge hs)).trans_eq (hflat 1 le_rfl))
  exact hm.deriv_eq_zero

theorem cutoff_heat_le_of_flat_upper_support (D : LeviCivitaData g)
    {ρ : ℝ → M → ℝ} {t : ℝ} {U : Set M} (hU : IsOpen U) {x : M} (hx : x ∈ U)
    (hρ : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (ρ t) U)
    (htime : DifferentiableAt ℝ (fun s => ρ s x) t)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hanti : Antitone χ)
    (hflat : ∀ r, r ≤ 1 → χ r = 1)
    {A B C H δ d₀ : ℝ} {m : ℕ} (hδ : 0 < δ) (hd₀ : 0 ≤ d₀) (hH : 0 ≤ H)
    (hA : ∀ r, deriv χ r ^ 2 ≤ A * χ r)
    (hB : ∀ r, -B ≤ deriv (deriv χ) r) (hC : ∀ r, -C ≤ deriv χ r)
    (hd : 0 < ρ t x)
    (hgrad : g.inner x (D.gradient (ρ t) x) (D.gradient (ρ t) x) = 1)
    (hlap : D.laplacian (ρ t) x ≤ 2 * (m : ℝ) / ρ t x)
    (hderiv : -H ≤ deriv (fun s => ρ s x) t)
    (hpos : 0 < χ ((ρ t x - d₀) / δ)) :
    deriv (fun s => χ ((ρ s x - d₀) / δ)) t -
        D.laplacian (fun y => χ ((ρ t y - d₀) / δ)) x +
        2 * g.inner x (D.gradient (fun y => χ ((ρ t y - d₀) / δ)) x)
          (D.gradient (fun y => χ ((ρ t y - d₀) / δ)) x) / χ ((ρ t x - d₀) / δ) ≤
      C * H / δ + (B + 2 * A + 2 * (m : ℝ) * C) / δ ^ 2 := by
  have hC₀ : 0 ≤ C := by
    have h₁ := hC ((ρ t x - d₀) / δ)
    have h₂ := hanti.deriv_nonpos (x := (ρ t x - d₀) / δ)
    linarith
  by_cases hsmall : (ρ t x - d₀) / δ ≤ 1
  · have hz := deriv_eq_zero_of_flat hanti hflat hsmall
    have hl := laplacian_scaled_profile D hU hx hρ hχ d₀ δ hgrad
    rw [hz, zero_div, zero_mul, zero_add] at hl
    have hg : g.inner x (D.gradient (fun y => χ ((ρ t y - d₀) / δ)) x)
        (D.gradient (fun y => χ ((ρ t y - d₀) / δ)) x) ≤
          A / δ ^ 2 * χ ((ρ t x - d₀) / δ) :=
      (shifted_profile_operator_bounds D hU hx hρ hχ hanti hδ
        (show 0 ≤ 2 * (m : ℝ) / ρ t x by positivity) hA hB hC hgrad hlap).1
    have hdtime := ((hχ.differentiable (by simp) _).hasDerivAt).comp t
      ((htime.hasDerivAt.sub_const d₀).div_const δ)
    have hdt : deriv (fun s => χ ((ρ s x - d₀) / δ)) t = 0 := by
      simpa only [Function.comp_def, hz, zero_mul] using hdtime.deriv
    have hg' : 2 * g.inner x (D.gradient (fun y => χ ((ρ t y - d₀) / δ)) x)
        (D.gradient (fun y => χ ((ρ t y - d₀) / δ)) x) / χ ((ρ t x - d₀) / δ) ≤
        2 * A / δ ^ 2 := by
      apply (div_le_iff₀ hpos).mpr
      calc
        _ ≤ 2 * (A / δ ^ 2 * χ ((ρ t x - d₀) / δ)) :=
          mul_le_mul_of_nonneg_left hg (by norm_num)
        _ = _ := by ring
    have hl' := div_le_div_of_nonneg_right (hB ((ρ t x - d₀) / δ)) (sq_nonneg δ)
    have hlbound : -(deriv (deriv χ) ((ρ t x - d₀) / δ) / δ ^ 2) ≤ B / δ ^ 2 := by
      simpa only [neg_div, neg_neg] using neg_le_neg hl'
    have hcH : 0 ≤ C * H / δ := by positivity
    have hcm : 0 ≤ 2 * (m : ℝ) * C / δ ^ 2 := by positivity
    rw [hdt, hl]
    calc
      _ ≤ B / δ ^ 2 + 2 * A / δ ^ 2 := by
        simpa only [zero_sub] using add_le_add hlbound hg'
      _ ≤ C * H / δ + (B / δ ^ 2 + 2 * A / δ ^ 2) + 2 * (m : ℝ) * C / δ ^ 2 := by
        linarith only [hcH, hcm]
      _ = _ := by ring
  · have hlarge : δ ≤ ρ t x := by
      have hh := (lt_div_iff₀ hδ).mp (lt_of_not_ge hsmall)
      linarith
    have h := D.cutoff_heat_le_of_upper_support hU hx hρ htime hχ hanti hδ hH
      (show 0 ≤ 2 * (m : ℝ) / ρ t x by positivity) hA hB hC hgrad hlap hderiv hpos
    apply h.trans
    have hdist := div_le_div_of_nonneg_left
      (show 0 ≤ 2 * (m : ℝ) * C by positivity) hδ hlarge
    have hdist' := div_le_div_of_nonneg_right hdist hδ.le
    have hterm : C * (2 * (m : ℝ) / ρ t x) / δ ≤ 2 * (m : ℝ) * C / δ ^ 2 := by
      calc
        _ = (2 * (m : ℝ) * C / ρ t x) / δ := by ring
        _ ≤ (2 * (m : ℝ) * C / δ) / δ := hdist'
        _ = _ := by ring
    calc
      _ ≤ C * H / δ + (B + 2 * A) / δ ^ 2 + 2 * (m : ℝ) * C / δ ^ 2 := by linarith
      _ = _ := by ring

end PoincareConjecture.LeviCivitaData

namespace PoincareConjecture.RicciFlow

variable {m : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M] [ConnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M]
  [IsManifold (𝓡 (m + 1)) ∞ M] {J : Set ℝ}

theorem exists_distance_cutoff_lower_support (F : RicciFlow (m + 1) M J)
    {t r Λ scale δ d₀ A B C : ℝ} (ht : t ∈ interior J) (hm : 0 < m)
    (hcomplete : MetricComplete (F.metric t))
    (hRic : ∀ y : M, ∀ v : TangentSpace (𝓡 (m + 1)) y,
      0 ≤ (F.connection t).ricci y v v)
    (hΛ : 0 ≤ Λ) (hscale : 0 < scale) (p x : M)
    (hx : x ∈ (F.metric t).ball p r) (hpx : p ≠ x)
    (hupper : ∀ y ∈ (F.metric t).ball p r, ∀ v : TangentSpace (𝓡 (m + 1)) y,
      (F.connection t).ricci y v v ≤ Λ * (F.metric t).inner y v v)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hanti : Antitone χ) (hδ : 0 < δ)
    (hA : ∀ z, deriv χ z ^ 2 ≤ A * χ z)
    (hB : ∀ z, -B ≤ deriv (deriv χ) z) (hC : ∀ z, -C ≤ deriv χ z)
    (hpos : 0 < χ ((((F.metric t).edist p x).toReal - d₀) / δ)) :
    ∃ (U : Set M) (φ : ℝ → M → ℝ), IsOpen U ∧ x ∈ U ∧
      ContMDiffOn (𝓡 (m + 1)) 𝓘(ℝ, ℝ) ∞ (φ t) U ∧
      φ t x = χ ((((F.metric t).edist p x).toReal - d₀) / δ) ∧
      (∀ s : ℝ, ∀ y ∈ U, φ s y ≤ χ ((((F.metric s).edist p y).toReal - d₀) / δ)) ∧
      DifferentiableAt ℝ (fun s => φ s x) t ∧
      deriv (fun s => φ s x) t - (F.connection t).laplacian (φ t) x +
        2 * (F.metric t).inner x ((F.connection t).gradient (φ t) x)
          ((F.connection t).gradient (φ t) x) / φ t x ≤
        C * (4 * ((m + 1 : ℕ) : ℝ) * scale + 8 * Λ / scale) / δ +
          (B + 2 * A) / δ ^ 2 +
          2 * (m : ℝ) * C / (δ * ((F.metric t).edist p x).toReal) := by
  obtain ⟨U, ρ, hU, hxU, hρ, heq, hle, hg, hl, htime, htbound⟩ :=
    F.exists_distance_spacetime_upper_support ht hm hcomplete hRic hΛ hscale p x hx hpx hupper
  have hd : 0 < ((F.metric t).edist p x).toReal := by
    let : RiemannianBundle (TangentSpace (𝓡 (m + 1)) : M → Type _) :=
      ⟨(F.metric t).toRiemannianMetric⟩
    let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 (m + 1)) M
    exact ENNReal.toReal_pos (edist_pos.mpr hpx).ne' ((F.metric t).edist_ne_top p x)
  let φ : ℝ → M → ℝ := fun s y => χ ((ρ s y - d₀) / δ)
  have hφtime : DifferentiableAt ℝ (fun s => φ s x) t :=
    (hχ.differentiable (by simp) _).comp t ((htime.sub_const d₀).div_const δ)
  refine ⟨U, φ, hU, hxU,
    hχ.contMDiff.comp_contMDiffOn ((hρ.sub contMDiffOn_const).div_const δ),
    by simp only [φ, heq], ?_, hφtime, ?_⟩
  · intro s y hy
    exact hanti (div_le_div_of_nonneg_right (sub_le_sub_right (hle s y hy) d₀) hδ.le)
  · have h := (F.connection t).cutoff_heat_le_of_upper_support hU hxU hρ htime
      hχ hanti hδ (by positivity)
      (show 0 ≤ 2 * (m : ℝ) / ((F.metric t).edist p x).toReal by positivity)
      hA hB hC hg hl htbound (by simpa only [heq] using hpos)
    convert h using 1
    ring

theorem exists_distance_cutoff_lower_support_of_flat (F : RicciFlow (m + 1) M J)
    {t r Λ scale δ d₀ A B C : ℝ} (ht : t ∈ interior J) (hm : 0 < m)
    (hcomplete : MetricComplete (F.metric t))
    (hRic : ∀ y : M, ∀ v : TangentSpace (𝓡 (m + 1)) y,
      0 ≤ (F.connection t).ricci y v v)
    (hΛ : 0 ≤ Λ) (hscale : 0 < scale) (p x : M)
    (hx : x ∈ (F.metric t).ball p r) (hpx : p ≠ x)
    (hupper : ∀ y ∈ (F.metric t).ball p r, ∀ v : TangentSpace (𝓡 (m + 1)) y,
      (F.connection t).ricci y v v ≤ Λ * (F.metric t).inner y v v)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hanti : Antitone χ) (hδ : 0 < δ)
    (hflat : ∀ z, z ≤ 1 → χ z = 1) (hd₀ : 0 ≤ d₀)
    (hA : ∀ z, deriv χ z ^ 2 ≤ A * χ z)
    (hB : ∀ z, -B ≤ deriv (deriv χ) z) (hC : ∀ z, -C ≤ deriv χ z)
    (hpos : 0 < χ ((((F.metric t).edist p x).toReal - d₀) / δ)) :
    ∃ (U : Set M) (φ : ℝ → M → ℝ), IsOpen U ∧ x ∈ U ∧
      ContMDiffOn (𝓡 (m + 1)) 𝓘(ℝ, ℝ) ∞ (φ t) U ∧
      φ t x = χ ((((F.metric t).edist p x).toReal - d₀) / δ) ∧
      (∀ s : ℝ, ∀ y ∈ U, φ s y ≤ χ ((((F.metric s).edist p y).toReal - d₀) / δ)) ∧
      DifferentiableAt ℝ (fun s => φ s x) t ∧
      deriv (fun s => φ s x) t - (F.connection t).laplacian (φ t) x +
        2 * (F.metric t).inner x ((F.connection t).gradient (φ t) x)
          ((F.connection t).gradient (φ t) x) / φ t x ≤
        C * (4 * ((m + 1 : ℕ) : ℝ) * scale + 8 * Λ / scale) / δ +
          (B + 2 * A + 2 * (m : ℝ) * C) / δ ^ 2 := by
  obtain ⟨U, ρ, hU, hxU, hρ, heq, hle, hg, hl, htime, htbound⟩ :=
    F.exists_distance_spacetime_upper_support ht hm hcomplete hRic hΛ hscale p x hx hpx hupper
  have hd : 0 < ((F.metric t).edist p x).toReal := by
    let : RiemannianBundle (TangentSpace (𝓡 (m + 1)) : M → Type _) :=
      ⟨(F.metric t).toRiemannianMetric⟩
    let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 (m + 1)) M
    exact ENNReal.toReal_pos (edist_pos.mpr hpx).ne' ((F.metric t).edist_ne_top p x)
  let φ : ℝ → M → ℝ := fun s y => χ ((ρ s y - d₀) / δ)
  have hφtime : DifferentiableAt ℝ (fun s => φ s x) t :=
    (hχ.differentiable (by simp) _).comp t ((htime.sub_const d₀).div_const δ)
  refine ⟨U, φ, hU, hxU,
    hχ.contMDiff.comp_contMDiffOn ((hρ.sub contMDiffOn_const).div_const δ),
    by simp only [φ, heq], ?_, hφtime, ?_⟩
  · intro s y hy
    exact hanti (div_le_div_of_nonneg_right (sub_le_sub_right (hle s y hy) d₀) hδ.le)
  · exact (F.connection t).cutoff_heat_le_of_flat_upper_support hU hxU hρ htime
      hχ hanti hflat hδ hd₀ (by positivity) hA hB hC
      (by simpa only [heq] using hd) hg (by simpa only [heq] using hl) htbound
      (by simpa only [heq] using hpos)

end PoincareConjecture.RicciFlow
