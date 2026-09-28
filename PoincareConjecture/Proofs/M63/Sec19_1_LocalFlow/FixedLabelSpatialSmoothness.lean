import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.FixedLabelSpatialRecurrences
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.FixedLabelC2Transport
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.C2SpeedPrimitive
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.PullbackRicciRegularity
import PoincareConjecture.Proofs.M63.Mathlib.NormalizedSpatialPathBootstrap
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle intervalIntegral

universe u v

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {ι : Type v} [Fintype ι] {a b : ℝ}

local notation "W" => EuclideanSpace ℝ ι

theorem fixedLabel_embedded_path_smooth_of_constant_speed
    (F : RicciFlow n M (Icc a b)) {c : ℝ → ℝ → M} {J : Set ℝ}
    (hc : M63C2ShrinkingCurveOn F c J) (hi : M63IntrinsicRegularityOn F c J)
    {tau s : ℝ} (hat : a < tau) (hts : tau < s) (hslab : Icc tau s ⊆ J)
    {psi : ℝ → ℝ} (hpsi : ContDiff ℝ 2 psi) (hpos : ∀ x, 0 < deriv psi x)
    (hshift : ∀ x, psi (x + curvePeriod) = psi x + curvePeriod)
    {v0 : ℝ} (hanchor : ∀ x, curveSpeed F (fun y t => c (psi y) t) tau x = v0)
    {e : M → W} (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e)
    {U : Set W} (hU : IsOpen U) (heU : range e ⊆ U) {ρ : W → M}
    (hρ : ContMDiffOn 𝓘(ℝ, W) (𝓡 n) ∞ ρ U) (hρe : ∀ p, ρ (e p) = p) :
    ∃ Q : ℝ → C(Icc tau s, W),
      (∀ x (t : Icc tau s), Q x t = e (c (psi x) t)) ∧
      ContDiff ℝ ∞ Q ∧
      (∀ t ∈ Icc tau s, ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) ∞ (fun x => c (psi x) t)) ∧
      ∀ k : ℕ, ContinuousOn
        (fun z : ℝ × ℝ => iteratedDeriv k (fun x => e (c (psi x) z.2)) z.1)
        (univ ×ˢ Icc tau s) := by
  let d := fun x t => c (psi x) t
  let q := fun x t => e (d x t)
  let v := fun x t => curveSpeed F d t x
  let K := fun (i : ℕ) (t x : ℝ) => match i with
    | 0 => spatialUnitTangent F c t x
    | i + 1 => m63CurvatureJet F c i t x
  let R : ℕ → ℝ → ℝ → W :=
    fun i x t => mfderiv (𝓡 n) 𝓘(ℝ, W) e (d x t) (K i t (psi x))
  let A : (ℝ × W) × (W × W) → ℝ := fun z =>
    (F.connection z.1.1).ricci (ρ z.1.2)
        (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z.1.2 z.2.1)
        (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z.1.2 z.2.1) +
      (F.metric z.1.1).inner (ρ z.1.2)
        (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z.1.2 z.2.2)
        (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z.1.2 z.2.2)
  let B : (ℝ × W) × (W × W) → W := fun z =>
    coordinateHessian (F.connection z.1.1) e (ρ z.1.2)
      (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z.1.2 z.2.1)
      (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z.1.2 z.2.2)
  have htime : Icc tau s ⊆ Icc a b := hslab.trans hc.domain_subset
  have hric := flow_pullback_ricci_contDiffOn F hU hρ
  have hmetric := (flow_pullback_metric_hessian_contDiffOn F hU hρ
    (contMDiff_const (c := (0 : ℝ)))).1
  have hfirstMap : ContDiff ℝ ∞
      (fun z : (ℝ × W) × (W × W) => (z.1, z.2.1)) := by fun_prop
  have hsecondMap : ContDiff ℝ ∞
      (fun z : (ℝ × W) × (W × W) => (z.1, z.2.2)) := by fun_prop
  have hAfst := hric.comp (s := (Icc tau s ×ˢ U) ×ˢ univ)
    hfirstMap.contDiffOn
    (fun z hz => ⟨⟨htime hz.1.1, hz.1.2⟩, mem_univ _⟩)
  have hAsnd := hmetric.comp (s := (Icc tau s ×ˢ U) ×ˢ univ)
    hsecondMap.contDiffOn
    (fun z hz => ⟨⟨htime hz.1.1, hz.1.2⟩, mem_univ _⟩)
  have hA : ContDiffOn ℝ ∞ A ((Icc tau s ×ˢ U) ×ˢ univ) := hAfst.add hAsnd
  have hB : ContDiffOn ℝ ∞ B ((Icc tau s ×ˢ U) ×ˢ univ) :=
    (flow_coordinateHessian_mixed_pullback_contDiffOn F he hU hρ).mono
      (fun z hz => ⟨⟨htime hz.1.1, hz.1.2⟩, hz.2⟩)
  have hrec := fixedLabel_embedded_closed_spatial_recurrences F hc hi hat hts hslab
    hpsi hpos he hU heU hρ hρe
  change ContinuousOn (fun z : ℝ × ℝ => q z.1 z.2) (univ ×ˢ Icc tau s) ∧
    ContinuousOn (fun z : ℝ × ℝ => v z.1 z.2) (univ ×ˢ Icc tau s) ∧
    (∀ i, ContinuousOn (fun z : ℝ × ℝ => R i z.1 z.2) (univ ×ˢ Icc tau s)) ∧
    (∀ t ∈ Icc tau s, ∀ x, HasDerivAt (fun y => q y t) (v x t • R 0 x t) x) ∧
    (∀ i, ∀ t ∈ Icc tau s, ∀ x, HasDerivAt (fun y => R i y t)
      (v x t • (B ((t, q x t), (R 0 x t, R i x t)) + R (i + 1) x t)) x) at hrec
  obtain ⟨hq, _hv, hR, hqder, hRder⟩ := hrec
  have hd : M63C2ShrinkingCurveOn F d J :=
    c2ShrinkingCurve_fixedLabel_comp F hc hpsi hpos hshift
  have hH := c2ShrinkingCurve_fixedLabel_curvature_contMDiffOn F hc hpsi hpos
    (hi.interior_jets 0)
  have hleft := (smooth_retraction_differentials he hU heU hρ hρe).2.2
  have hAvalue (t : ℝ) (ht : t ∈ Icc tau s) (x : ℝ) :
      A ((t, q x t), (R 0 x t, R 1 x t)) =
        m62TangentRicci F d t x + m62CurvatureSquared F d t x := by
    have hS := spatialUnitTangent_comp F c
      ((hc.spatial_regular t (hslab ht)).mdifferentiable (by norm_num) (psi x))
      ((hpsi.differentiable (by norm_num) x).hasDerivAt) (hpos x)
    have hcurv := curvatureVector_comp F c
      ((hc.spatial_regular t (hslab ht)).mdifferentiable (by norm_num))
      (hpsi.differentiable (by norm_num)) hpos
      ((unitTangent_contMDiff_of_c2 F c (hc.spatial_regular t (hslab ht))
        (hc.immersed t (hslab ht)) (psi x)).mdifferentiableAt (by norm_num))
    dsimp only [A, q, R]
    erw [hleft (d x t) (K 0 t (psi x)), hleft (d x t) (K 1 t (psi x)), hρe (d x t)]
    change (F.connection t).ricci (d x t)
        (spatialUnitTangent F c t (psi x)) (spatialUnitTangent F c t (psi x)) +
      (F.metric t).inner (d x t)
        (m62CurvatureVector F c t (psi x)) (m62CurvatureVector F c t (psi x)) = _
    rw [← hS, ← hcurv]
    rfl
  have hvformula (x : ℝ) (t : ℝ) (ht : t ∈ Icc tau s) :
      v x t = v0 * Real.exp (-∫ u in tau..t, A ((u, q x u), (R 0 x u, R 1 x u))) := by
    have hsub : Icc tau t ⊆ J := fun u hu => hslab ⟨hu.1, hu.2.trans ht.2⟩
    have hp := c2ShrinkingCurve_speed_eq_exp_integral F hd hH ht.1 hsub x
    have hInt : (∫ u in tau..t, A ((u, q x u), (R 0 x u, R 1 x u))) =
        ∫ u in tau..t, m62TangentRicci F d u x + m62CurvatureSquared F d u x := by
      apply intervalIntegral.integral_congr
      intro u hu
      have hut : u ∈ Icc tau t := by simpa only [uIcc_of_le ht.1] using hu
      exact hAvalue u ⟨hut.1, hut.2.trans ht.2⟩ x
    rw [hInt, ← hanchor x]
    exact hp
  obtain ⟨Q, V, Rpath, hQvalue, _hVvalue, _hRvalue, hQ, _hV, _hRp⟩ :=
    exists_contDiff_pathFamily_of_normalized_spatial_recurrences hts hU A B hA hB
      q v R v0 hq hR (fun x t _ => heU (mem_range_self (d x t))) hvformula hqder hRder
  have hslice (t : Icc tau s) : ContDiff ℝ ∞ (fun x => q x t) := by
    let ev : C(Icc tau s, W) →L[ℝ] W := ContinuousMap.evalCLM ℝ t
    have heval := ev.contDiff.comp hQ
    change ContDiff ℝ ∞ (fun x => Q x t) at heval
    have heq : (fun x => Q x t) = fun x => q x t := funext fun x => hQvalue x t
    rwa [heq] at heval
  have hmanifold (t : ℝ) (ht : t ∈ Icc tau s) :
      ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) ∞ (fun x => d x t) := by
    have hcomp := hρ.comp_contMDiff (hslice ⟨t, ht⟩).contMDiff
      (fun x => heU (mem_range_self (d x t)))
    exact hcomp.congr (fun x => (hρe (d x t)).symm)
  have hjet (k : ℕ) (t : Icc tau s) :
      iteratedDeriv k (fun x => q x t) = fun x => iteratedDeriv k Q x t := by
    induction k with
    | zero =>
      simp only [iteratedDeriv_zero]
      exact funext (fun x => (hQvalue x t).symm)
    | succ k ih =>
      rw [iteratedDeriv_succ, iteratedDeriv_succ, ih]
      funext x
      have hqd := (hQ.differentiable_iteratedDeriv k
        (ENat.natCast_lt_of_coe_top_le_withTop le_rfl k) x).hasDerivAt
      exact ((ContinuousMap.evalCLM ℝ t).hasFDerivAt.comp_hasDerivAt x hqd).deriv
  refine ⟨Q, hQvalue, hQ, hmanifold, ?_⟩
  intro k
  have hpaths : Continuous (fun z : ℝ × ℝ => iteratedDeriv k Q z.1) :=
    (hQ.continuous_iteratedDeriv k
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl k)).comp continuous_fst
  have hclamp : Continuous (fun z : ℝ × ℝ => projIcc tau s hts.le z.2) :=
    continuous_projIcc.comp continuous_snd
  have hcont := continuous_eval.comp (hpaths.prodMk hclamp)
  apply hcont.continuousOn.congr
  intro z hz
  change iteratedDeriv k (fun x => q x z.2) z.1 =
    iteratedDeriv k Q z.1 (projIcc tau s hts.le z.2)
  rw [projIcc_of_mem _ hz.2]
  exact congrFun (hjet k ⟨z.2, hz.2⟩) z.1

end PoincareConjecture.M63
