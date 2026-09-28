import PoincareConjecture.Proofs.M25.Topology3D.Space3.HorizontalBandField
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold InnerProductSpace Topology Matrix

namespace PoincareConjecture.M25.Topology3D

theorem saddle_native_projected_fields
    (u : UnitTwoSphere) (c rho delta e : ℝ)
    (hrho : 0 < rho) (hdelta : 0 < delta)
    (hsmall : delta ≤ rho ^ 2 / 128)
    (he : 0 < e) (heSmall : e < 1 / 512)
    (J2 : E2 ≃L[ℝ] (ℝ × ℝ))
    (hJ2 : ∀ x : E2, (J2 x).1 ^ 2 + (J2 x).2 ^ 2 = ‖x‖ ^ 2)
    (g : Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞)
    (X : Fin 2 → E3 → E3) (hX : ∀ j : Fin 2, ContDiff ℝ ∞ (X j))
    (S : Fin 2 → Set E3) (hS : ∀ j : Fin 2, IsCompact (S j))
    (hGraph : ∀ (j : Fin 2) (t : ℝ), |t| < 2 * delta →
      ∀ x : E2, ‖x‖ < 2 →
        ((heightPlaneCoordinates u).symm (g x, c + t) ∈ S j ↔
          t = rho ^ 2 * ((J2 x).1 ^ 2 - (J2 x).2 ^ 2))) :
    let L := heightPlaneCoordinates u
    let pi := horizontalBandProjection u
    let sx : Fin 4 → ℝ := ![1, -1, -1, 1]
    let sy : Fin 4 → ℝ := ![1, 1, -1, -1]
    let xi : Fin 4 → ℝ → ℝ → E2 := fun k t r => J2.symm
      (sx k * Real.sqrt ((r ^ 2 + t / rho ^ 2) / 2),
        sy k * Real.sqrt ((r ^ 2 - t / rho ^ 2) / 2))
    let Xi : Fin 4 → ℝ → ℝ → E3 := fun k t r =>
      L.symm (g (xi k t r), c + t)
    (∀ (j : Fin 2) (k : Fin 4) (r : ℝ),
      r ∈ Ioo (15 / 16 : ℝ) (17 / 16) →
      ∀ t : ℝ, |t| < 2 * delta →
        HasDerivAt (fun s : ℝ => Xi k s r) (X j (Xi k t r)) t) →
    let b : Fin 2 → ℝ × E2 → E2 := fun j p =>
      fderiv ℝ g.symm (g p.2) (pi (X j (L.symm (g p.2, c + p.1))))
    let P : Set E2 := g.symm '' (pi '' (S 0 ∪ S 1))
    let E : Fin 2 → ℝ → Set E2 := fun j t =>
      {x : E2 | L.symm (g x, c + t) ∈ S j ∧ 1 ≤ ‖x‖}
    (∀ j : Fin 2, ContDiff ℝ ∞ (b j)) ∧ IsCompact P ∧
      (∀ (j : Fin 2) (t : ℝ), |t| < 2 * delta →
        E j t ⊆ P ∩ {x : E2 | 1 ≤ ‖x‖}) ∧
      ∀ (j : Fin 2) (t : ℝ), |t| < 2 * delta →
        ∀ x ∈ E j t, ‖x‖ ≤ 1 + 3 * e →
          b 0 (t, x) = b j (t, x) ∧ ⟪x, b 0 (t, x)⟫_ℝ = 0 := by
  classical
  dsimp only
  let L := heightPlaneCoordinates u
  let pi := horizontalBandProjection u
  let sx : Fin 4 → ℝ := ![1, -1, -1, 1]
  let sy : Fin 4 → ℝ := ![1, 1, -1, -1]
  let xi : Fin 4 → ℝ → ℝ → E2 := fun k t r => J2.symm
    (sx k * Real.sqrt ((r ^ 2 + t / rho ^ 2) / 2),
      sy k * Real.sqrt ((r ^ 2 - t / rho ^ 2) / 2))
  let Xi : Fin 4 → ℝ → ℝ → E3 := fun k t r => L.symm (g (xi k t r), c + t)
  intro hTrack
  let b : Fin 2 → ℝ × E2 → E2 := fun j p =>
    fderiv ℝ g.symm (g p.2) (pi (X j (L.symm (g p.2, c + p.1))))
  let P : Set E2 := g.symm '' (pi '' (S 0 ∪ S 1))
  let E : Fin 2 → ℝ → Set E2 := fun j t =>
    {x : E2 | L.symm (g x, c + t) ∈ S j ∧ 1 ≤ ‖x‖}
  have hpi (x : E2) (t : ℝ) : pi (L.symm (x, t)) = x := by
    simp only [pi, L, horizontalBandProjection_apply, ContinuousLinearEquiv.apply_symm_apply]
  have hb (j : Fin 2) : ContDiff ℝ ∞ (b j) :=
    ((g.symm.contDiff.fderiv_right (by simp)).comp
      (g.contDiff.comp contDiff_snd)).clm_apply
        (pi.contDiff.comp ((hX j).comp (L.symm.contDiff.comp
          ((g.contDiff.comp contDiff_snd).prodMk (contDiff_const.add contDiff_fst)))))
  have hP : IsCompact P :=
    (((hS 0).union (hS 1)).image pi.continuous).image g.symm.continuous
  have hExterior (j : Fin 2) (t : ℝ) (_ht : |t| < 2 * delta) :
      E j t ⊆ P ∩ {x : E2 | 1 ≤ ‖x‖} := by
    intro x hx
    refine ⟨⟨g x, ⟨L.symm (g x, c + t), ?_, hpi _ _⟩,
      g.symm_apply_apply x⟩, hx.2⟩
    fin_cases j
    · exact Or.inl hx.1
    · exact Or.inr hx.1
  have hrho2 : 0 < rho ^ 2 := sq_pos_of_pos hrho
  have hRatio (t : ℝ) (ht : |t| < 2 * delta) : |t / rho ^ 2| < 1 / 64 := by
    rw [abs_div, abs_of_pos hrho2]
    exact (div_lt_iff₀ hrho2).mpr (by linarith only [ht, hsmall])
  have hSigns (k : Fin 4) : (sx k) ^ 2 = 1 ∧ (sy k) ^ 2 = 1 := by
    fin_cases k <;> norm_num [sx, sy]
  have hNorm (k : Fin 4) (r : ℝ) (hr : r ∈ Ioo (15 / 16 : ℝ) (17 / 16))
      (t : ℝ) (ht : |t| < 2 * delta) : ‖xi k t r‖ ^ 2 = r ^ 2 := by
    have ha := abs_lt.mp (hRatio t ht)
    have hplus : 0 ≤ (r ^ 2 + t / rho ^ 2) / 2 := by nlinarith only [hr.1, ha.1]
    have hminus : 0 ≤ (r ^ 2 - t / rho ^ 2) / 2 := by nlinarith only [hr.1, ha.2]
    have hh := (hJ2 (xi k t r)).symm
    dsimp only [xi] at hh
    rw [J2.apply_symm_apply] at hh
    simp only [mul_pow, (hSigns k).1, (hSigns k).2, one_mul,
      Real.sq_sqrt hplus, Real.sq_sqrt hminus] at hh
    linarith only [hh]
  have hDerivative (j : Fin 2) (k : Fin 4) (r : ℝ)
      (hr : r ∈ Ioo (15 / 16 : ℝ) (17 / 16))
      (t : ℝ) (ht : |t| < 2 * delta) :
      HasDerivAt (fun s : ℝ => xi k s r) (b j (t, xi k t r)) t := by
    have hn : HasDerivAt (fun s : ℝ => Xi k s r) (X j (Xi k t r)) t :=
      hTrack j k r hr t ht
    have hp := pi.hasFDerivAt.comp_hasDerivAt t hn
    have hg := (g.symm.contDiff.differentiable (by simp)
      (pi (Xi k t r))).hasFDerivAt.comp_hasDerivAt t hp
    simpa only [Function.comp_def, Xi, hpi, g.symm_apply_apply, b] using hg
  have hTangent (k : Fin 4) (r : ℝ)
      (hr : r ∈ Ioo (15 / 16 : ℝ) (17 / 16))
      (t : ℝ) (ht : |t| < 2 * delta) : ⟪xi k t r, b 0 (t, xi k t r)⟫_ℝ = 0 := by
    let eps := min e (min delta (2 * delta - |t|)) / 4
    have heps : 0 < eps := div_pos (lt_min he (lt_min hdelta (by linarith only [ht])))
      (by norm_num)
    have hepsBound : eps ≤ (2 * delta - |t|) / 4 :=
      div_le_div_of_nonneg_right ((min_le_right _ _).trans (min_le_right _ _)) (by norm_num)
    have hnear : (fun s : ℝ => ‖xi k s r‖ ^ 2) =ᶠ[𝓝 t] fun _ => r ^ 2 := by
      filter_upwards [Metric.ball_mem_nhds t heps] with s hs
      have hdist : |s - t| < eps := by simpa only [mem_ball, Real.dist_eq] using hs
      have habs : |s| ≤ |s - t| + |t| := by
        simpa only [sub_add_cancel] using abs_add_le (s - t) t
      exact hNorm k r hr s (by linarith only [ht, hdist, habs, hepsBound])
    have hc : HasDerivAt (fun s : ℝ => ‖xi k s r‖ ^ 2) 0 t :=
      (hasDerivAt_const t (r ^ 2)).congr_of_eventuallyEq hnear
    have hz := (hDerivative 0 k r hr t ht).norm_sq.unique hc
    linarith only [hz]
  refine ⟨hb, hP, hExterior, ?_⟩
  intro j t ht x hx hxUpper
  have hr : ‖x‖ ∈ Ioo (15 / 16 : ℝ) (17 / 16) :=
    ⟨by linarith only [hx.2], by linarith only [hxUpper, heSmall]⟩
  have hgraph := (hGraph j t ht x (by linarith only [hr.2])).mp hx.1
  have hratio : t / rho ^ 2 = (J2 x).1 ^ 2 - (J2 x).2 ^ 2 :=
    (div_eq_iff hrho2.ne').mpr (by nlinarith only [hgraph])
  have hplus : (‖x‖ ^ 2 + t / rho ^ 2) / 2 = (J2 x).1 ^ 2 := by
    linarith only [hJ2 x, hratio]
  have hminus : (‖x‖ ^ 2 - t / rho ^ 2) / 2 = (J2 x).2 ^ 2 := by
    linarith only [hJ2 x, hratio]
  have hCover : ∃ k : Fin 4, xi k t ‖x‖ = x := by
    rcases le_total 0 (J2 x).1 with ha | ha <;>
      rcases le_total 0 (J2 x).2 with hd | hd
    · refine ⟨0, J2.injective ?_⟩
      simp only [xi, J2.apply_symm_apply, hplus, hminus, Real.sqrt_sq_eq_abs]
      simp [sx, sy, abs_of_nonneg ha, abs_of_nonneg hd]
    · refine ⟨3, J2.injective ?_⟩
      simp only [xi, J2.apply_symm_apply, hplus, hminus, Real.sqrt_sq_eq_abs]
      simp [sx, sy, abs_of_nonneg ha, abs_of_nonpos hd]
    · refine ⟨1, J2.injective ?_⟩
      simp only [xi, J2.apply_symm_apply, hplus, hminus, Real.sqrt_sq_eq_abs]
      simp [sx, sy, abs_of_nonpos ha, abs_of_nonneg hd]
    · refine ⟨2, J2.injective ?_⟩
      simp only [xi, J2.apply_symm_apply, hplus, hminus, Real.sqrt_sq_eq_abs]
      simp [sx, sy, abs_of_nonpos ha, abs_of_nonpos hd]
  obtain ⟨k, hk⟩ := hCover
  exact ⟨hk ▸ (hDerivative 0 k ‖x‖ hr t ht).unique (hDerivative j k ‖x‖ hr t ht),
    hk ▸ hTangent k ‖x‖ hr t ht⟩

end PoincareConjecture.M25.Topology3D
