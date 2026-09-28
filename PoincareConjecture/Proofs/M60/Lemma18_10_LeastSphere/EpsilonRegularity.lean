import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.EpsilonRegularityMeanValue

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped ContDiff Topology Manifold

namespace PoincareConjecture.M60

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem suAlphaPrincipalQuadratic_uniform
    (G : E →L[ℝ] E →L[ℝ] ℝ) (a b : E) {rho alpha : ℝ}
    (hG : ∀ v : E, 0 ≤ G v v) (hsym : ∀ v w : E, G v w = G w v)
    (hrho : 0 < rho) (halpha : 1 ≤ alpha) (halpha' : alpha ≤ 3 / 2)
    (x y : ℝ) :
    x ^ 2 + y ^ 2 ≤ suAlphaPrincipalQuadratic G a b rho (alpha - 1) x y ∧
      suAlphaPrincipalQuadratic G a b rho (alpha - 1) x y ≤ 2 * (x ^ 2 + y ^ 2) := by
  obtain ⟨hl, hu⟩ := suAlphaPrincipalQuadratic_bounds G a b hG hsym hrho
    (sub_nonneg.mpr halpha) x y
  refine ⟨hl, hu.trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ (add_nonneg (sq_nonneg x) (sq_nonneg y))
  linarith

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

private def conformalAlphaFlux (G : P → E →L[ℝ] E →L[ℝ] ℝ) (u : P → E)
    (q lambda : P → ℝ) (rho c : ℝ) (d e v p : P) : ℝ :=
  fderiv ℝ q p v + 2 * c / (lambda p * (rho ^ 2 + q p)) *
    G p (fderiv ℝ q p d • fderiv ℝ u p d + fderiv ℝ q p e • fderiv ℝ u p e)
      (fderiv ℝ u p v)

private theorem conformalAlphaFlux_contDiffAt
    {G : P → E →L[ℝ] E →L[ℝ] ℝ} {u : P → E} {q lambda : P → ℝ}
    {rho c : ℝ} {p : P} (d e v : P)
    (hG : ContDiffAt ℝ ∞ G p) (hu : ContDiffAt ℝ ∞ u p)
    (hq : ContDiffAt ℝ ∞ q p) (hl : ContDiffAt ℝ ∞ lambda p)
    (hden : lambda p * (rho ^ 2 + q p) ≠ 0) :
    ContDiffAt ℝ ∞ (conformalAlphaFlux G u q lambda rho c d e v) p := by
  have hdu (w : P) : ContDiffAt ℝ ∞ (fun r => fderiv ℝ u r w) p :=
    (hu.fderiv_right (by simp)).clm_apply contDiffAt_const
  have hdq (w : P) : ContDiffAt ℝ ∞ (fun r => fderiv ℝ q r w) p :=
    (hq.fderiv_right (by simp)).clm_apply contDiffAt_const
  have hW := ((hdq d).smul (hdu d)).add ((hdq e).smul (hdu e))
  exact (hdq v).add ((contDiffAt_const.div
    (hl.mul (contDiffAt_const.add hq)) hden).mul
      ((hG.clm_apply hW).clm_apply (hdu v)))

private theorem conformalAlphaFlux_divergence_lower
    {Γ : E → E →L[ℝ] E →L[ℝ] E} {u : P → E}
    {G : P → E →L[ℝ] E →L[ℝ] ℝ} {q lambda : P → ℝ}
    {O : Set P} {p : P} (hO : IsOpen O) (hp : p ∈ O) (d e : P)
    (hu : ContDiffOn ℝ ∞ u O) (hG : ContDiffOn ℝ ∞ G O)
    (hq : ContDiffOn ℝ ∞ q O) (hl : ContDiffOn ℝ ∞ lambda O)
    (hΓ : ∀ r ∈ O, ContDiffAt ℝ ∞ Γ (u r))
    (hcompat : ∀ r ∈ O, ∀ v : P, ∀ b c : E,
      fderiv ℝ (fun s => G s b c) r v =
        G r (Γ (u r) (fderiv ℝ u r v) b) c +
          G r b (Γ (u r) (fderiv ℝ u r v) c))
    (hsym : ∀ b c : E, G p b c = G p c b) (hpos : ∀ b : E, 0 ≤ G p b b)
    (hΓsym : ∀ r ∈ O, ∀ b c, Γ (u r) b c = Γ (u r) c b)
    (henergy : ∀ r ∈ O, suLocalSquaredDifferential G u d e r = lambda r * q r)
    (hql : ∀ r ∈ O, 0 ≤ q r ∧ 1 / 4 ≤ lambda r ∧ lambda r ≤ 4)
    (hlgrad : (fderiv ℝ lambda p d) ^ 2 + (fderiv ℝ lambda p e) ^ 2 ≤ 256)
    (hllap : fderiv ℝ (fun r => fderiv ℝ lambda r d) p d +
      fderiv ℝ (fun r => fderiv ℝ lambda r e) p e ≤ 64)
    {rho c K : ℝ} (hrho : 0 < rho) (hc : 0 ≤ c) (hc' : c ≤ 1 / 32) (hK : 0 ≤ K)
    (heq : ∀ r ∈ O,
      ConnectionVariation.covDerivAlong Γ u
        (fun s => (rho ^ 2 + q s) ^ c • fderiv ℝ u s d) d r +
      ConnectionVariation.covDerivAlong Γ u
        (fun s => (rho ^ 2 + q s) ^ c • fderiv ℝ u s e) e r = 0)
    (hcurv : -K * (lambda p * q p) ^ 2 ≤
      2 * (G p (ConnectionVariation.christoffelCurvature Γ (u p)
          (fderiv ℝ u p e) (fderiv ℝ u p d) (fderiv ℝ u p e)) (fderiv ℝ u p d) +
        G p (ConnectionVariation.christoffelCurvature Γ (u p)
          (fderiv ℝ u p d) (fderiv ℝ u p e) (fderiv ℝ u p d)) (fderiv ℝ u p e))) :
    -(4 * K) * (q p) ^ 2 - 164256 * q p ≤
      fderiv ℝ (conformalAlphaFlux G u q lambda rho c d e d) p d +
        fderiv ℝ (conformalAlphaFlux G u q lambda rho c d e e) p e := by
  let a := fderiv ℝ u p d
  let b := fderiv ℝ u p e
  let H := fun v w => ConnectionVariation.covDerivAlong Γ u
    (fun r => fderiv ℝ u r v) w p
  let T := H d d + H e e
  let S := G p (H d d) (H d d) + G p (H d e) (H d e) +
    G p (H e d) (H e d) + G p (H e e) (H e e)
  let X := fderiv ℝ (suLocalSquaredDifferential G u d e) p d
  let Y := fderiv ℝ (suLocalSquaredDifferential G u d e) p e
  have hup := hu.contDiffAt (hO.mem_nhds hp)
  have hgp := hG.contDiffAt (hO.mem_nhds hp)
  have hqp := hq.contDiffAt (hO.mem_nhds hp)
  have hlp := hl.contDiffAt (hO.mem_nhds hp)
  have hden (r : P) (hr : r ∈ O) : 0 < rho ^ 2 + q r := by
    have hqr := (hql r hr).1
    positivity
  have hlpos (r : P) (hr : r ∈ O) : 0 < lambda r := by linarith [(hql r hr).2.1]
  have hde (r : P) (hr : r ∈ O) (v : P) :
      fderiv ℝ (suLocalSquaredDifferential G u d e) r v =
        lambda r * fderiv ℝ q r v + q r * fderiv ℝ lambda r v := by
    have hev : suLocalSquaredDifferential G u d e =ᶠ[𝓝 r]
        (fun s => lambda s * q s) :=
      Filter.Eventually.mono (hO.mem_nhds hr) fun s hs => henergy s hs
    rw [hev.fderiv_eq, fderiv_fun_mul
      ((hl.contDiffAt (hO.mem_nhds hr)).differentiableAt (by simp))
      ((hq.contDiffAt (hO.mem_nhds hr)).differentiableAt (by simp))]
    simp only [add_apply, smul_apply, smul_eq_mul]
  have ht (r : P) (hr : r ∈ O) := suAlphaEquation_tension Γ u d e
    ((hq.contDiffAt (hO.mem_nhds hr)).differentiableAt (by simp))
    ((hu.contDiffAt (hO.mem_nhds hr)).of_le (WithTop.coe_le_coe.mpr le_top))
    (hden r hr) (heq r hr)
  have hfeq (v : P) : suLocalEnergyFlux Γ G u d e v =ᶠ[𝓝 p]
      (fun r => lambda r * conformalAlphaFlux G u q lambda rho c d e v r +
        q r * fderiv ℝ lambda r v) := by
    filter_upwards [hO.mem_nhds hp] with r hr
    change fderiv ℝ (suLocalSquaredDifferential G u d e) r v -
      2 * G r (ConnectionVariation.covDerivAlong Γ u
        (fun s => fderiv ℝ u s d) d r + ConnectionVariation.covDerivAlong Γ u
        (fun s => fderiv ℝ u s e) e r) (fderiv ℝ u r v) = _
    rw [hde r hr v, ht r hr]
    simp only [conformalAlphaFlux, map_smul, smul_apply, smul_eq_mul]
    field_simp [(hlpos r hr).ne', (hden r hr).ne']
    ring
  have hfd (v : P) : fderiv ℝ (suLocalEnergyFlux Γ G u d e v) p v =
      lambda p * fderiv ℝ (conformalAlphaFlux G u q lambda rho c d e v) p v +
      fderiv ℝ lambda p v * conformalAlphaFlux G u q lambda rho c d e v p +
      q p * fderiv ℝ (fun r => fderiv ℝ lambda r v) p v +
      fderiv ℝ q p v * fderiv ℝ lambda p v := by
    have hld := hlp.differentiableAt (by simp)
    have hqd := hqp.differentiableAt (by simp)
    have hdd := ((hlp.fderiv_right (m := ∞) (by simp)).clm_apply
      (contDiffAt_const (c := v))).differentiableAt (by simp)
    have hF := (conformalAlphaFlux_contDiffAt (c := c) d e v hgp hup hqp hlp
      (mul_ne_zero (hlpos p hp).ne' (hden p hp).ne')).differentiableAt (by simp)
    rw [(hfeq v).fderiv_eq]
    change fderiv ℝ ((lambda * conformalAlphaFlux G u q lambda rho c d e v) +
      (q * fun r => fderiv ℝ lambda r v)) p v = _
    rw [fderiv_add (hld.mul hF) (hqd.mul hdd), fderiv_mul hld hF, fderiv_mul hqd hdd]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  have hS : 0 ≤ S :=
    add_nonneg (add_nonneg (add_nonneg (hpos _) (hpos _)) (hpos _)) (hpos _)
  have hX := suLocalSquaredDifferential_fderiv d e d hup
    (hgp.differentiableAt (by simp)) (hcompat p hp) hsym
  have hY := suLocalSquaredDifferential_fderiv d e e hup
    (hgp.differentiableAt (by simp)) (hcompat p hp) hsym
  have htrace : G p a a + G p b b = lambda p * q p := henergy p hp
  have hgrad : X ^ 2 + Y ^ 2 ≤ 4 * lambda p * q p * S := by
    have h0 := suMetricPair_cauchy_schwarz (G p) hpos hsym a b (H d d) (H e d)
    have h1 := suMetricPair_cauchy_schwarz (G p) hpos hsym a b (H d e) (H e e)
    rw [show 4 * lambda p * q p * S = 4 * (lambda p * q p) * S by ring, ← htrace]
    dsimp only [X, Y, S, a, b, H] at h0 h1 ⊢
    rw [hX, hY]
    nlinarith only [h0, h1]
  have habs := suConformalAlpha_absorption (G p) a b T hpos hsym
    (x := fderiv ℝ q p d) (y := fderiv ℝ q p e)
    (hql p hp).2.1 (hql p hp).2.2 (hql p hp).1 hS htrace hgrad
    (by dsimp only [X]; linarith only [hde p hp d])
    (by dsimp only [Y]; linarith only [hde p hp e]) hlgrad hrho hc hc'
    (by exact ht p hp)
  have hb := suLocalEnergyFlux_divergence hO hp d e hu hG hΓ hcompat hsym hΓsym
  dsimp only at hb
  rw [hfd d, hfd e] at hb
  have hcross :
      fderiv ℝ lambda p d * conformalAlphaFlux G u q lambda rho c d e d p +
      fderiv ℝ lambda p e * conformalAlphaFlux G u q lambda rho c d e e p +
      fderiv ℝ q p d * fderiv ℝ lambda p d +
      fderiv ℝ q p e * fderiv ℝ lambda p e =
      2 * (fderiv ℝ lambda p d * fderiv ℝ q p d +
        fderiv ℝ lambda p e * fderiv ℝ q p e) +
      2 * c / (lambda p * (rho ^ 2 + q p)) * G p
        (fderiv ℝ lambda p d • a + fderiv ℝ lambda p e • b)
        (fderiv ℝ q p d • a + fderiv ℝ q p e • b) := by
    simp only [conformalAlphaFlux, a, b, map_add, map_smul, add_apply, smul_apply,
      smul_eq_mul]
    rw [hsym (fderiv ℝ u p e) (fderiv ℝ u p d)]
    ring
  have hlow : -(K * lambda p ^ 2 * (q p) ^ 2) - 41064 * q p ≤
      lambda p * (fderiv ℝ (conformalAlphaFlux G u q lambda rho c d e d) p d +
        fderiv ℝ (conformalAlphaFlux G u q lambda rho c d e e) p e) := by
    have hlap := mul_le_mul_of_nonneg_left hllap (hql p hp).1
    change _ = 2 * S + _ - 2 * G p T T at hb
    nlinarith only [hb, habs, hcross, hcurv, hlap]
  apply (mul_le_mul_iff_right₀ (hlpos p hp)).mp
  apply le_trans _ hlow
  have h0 := mul_le_mul_of_nonneg_right (hql p hp).2.2
    (mul_nonneg (mul_nonneg hK (hlpos p hp).le) (sq_nonneg (q p)))
  have h1 := mul_le_mul_of_nonneg_right (hql p hp).2.1 (hql p hp).1
  nlinarith only [h0, h1]

private theorem euclideanGradient_basis
    (D : LeviCivitaData (RiemannianMetric.euclideanMetric 2)) (q : LoopPlane → ℝ)
    (p : LoopPlane) :
    D.gradient q p = ∑ i : Fin 2, fderiv ℝ q p (EuclideanSpace.basisFun (Fin 2) ℝ i) •
      EuclideanSpace.basisFun (Fin 2) ℝ i := by
  have h := (EuclideanSpace.basisFun (Fin 2) ℝ).sum_repr (D.gradient q p)
  have hc (i : Fin 2) : (EuclideanSpace.basisFun (Fin 2) ℝ).repr
      (D.gradient q p) i = fderiv ℝ q p (EuclideanSpace.basisFun (Fin 2) ℝ i) := by
    rw [OrthonormalBasis.repr_apply_apply, real_inner_comm]
    change (RiemannianMetric.euclideanMetric 2).inner p (D.gradient q p)
      (EuclideanSpace.basisFun (Fin 2) ℝ i) = _
    rw [D.inner_gradient]
    simp +instances only [mvfderiv, mfderiv_eq_fderiv, NormedSpace.fromTangentSpace]
    rfl
  simpa only [hc] using h.symm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

private theorem planePullback_contDiff (g : RiemannianMetric n M)
    {φ : LoopPlane → M} (hφ : ContMDiff (𝓡 2) (𝓡 n) ∞ φ) :
    ContDiff (F := LoopPlane →L[ℝ] LoopPlane →L[ℝ] ℝ) ℝ ∞
      (fun z : LoopPlane => metricPullbackForm (n := 2) g φ z) := by
  refine (contDiff_clm_apply_iff (E := LoopPlane) (F := LoopPlane →L[ℝ] ℝ)
    (f := fun z : LoopPlane => metricPullbackForm (n := 2) g φ z)).mpr ?_
  intro v
  refine (contDiff_clm_apply_iff (E := LoopPlane) (F := ℝ)
    (f := fun z : LoopPlane => metricPullbackForm (n := 2) g φ z v)).mpr ?_
  intro w
  let b := EuclideanSpace.basisFun (Fin 2) ℝ
  have heq : (fun z => metricPullbackForm g φ z v w) =
      (fun z => ∑ i : Fin 2, ∑ j : Fin 2,
        (b.repr v i) * (b.repr w j) * m60AreaGram g φ z i j) := by
    funext z
    conv_lhs => rw [← b.sum_repr v, ← b.sum_repr w]
    simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul]
    simp only [metricPullbackForm_apply, m60AreaGram, b]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  erw [heq]
  exact ContDiff.sum fun i _ => ContDiff.sum fun j _ =>
    contDiff_const.mul (m60AreaGram_entry_contDiff g hφ i j)

private def alphaCoefficient
    (T : LoopPlane → LoopPlane →L[ℝ] LoopPlane →L[ℝ] ℝ)
    (q lambda : LoopPlane → ℝ) (rho c : ℝ) (z : LoopPlane) :
    LoopPlane →L[ℝ] LoopPlane →L[ℝ] ℝ :=
  let I : LoopPlane →L[ℝ] LoopPlane →L[ℝ] ℝ := innerSL ℝ
  I + (2 * c / (lambda z * (rho ^ 2 + q z))) • T z

private theorem alphaCoefficient_elliptic
    (T : LoopPlane → LoopPlane →L[ℝ] LoopPlane →L[ℝ] ℝ)
    (q lambda : LoopPlane → ℝ) {rho c : ℝ} (z v : LoopPlane)
    (hT : ∀ w, 0 ≤ T z w w) (hsym : ∀ w y, T z w y = T z y w)
    (hl : 0 < lambda z) (hrho : 0 < rho) (hc : 0 ≤ c) (hc' : c ≤ 1 / 2)
    (htrace : T z (EuclideanSpace.basisFun (Fin 2) ℝ 0)
      (EuclideanSpace.basisFun (Fin 2) ℝ 0) +
      T z (EuclideanSpace.basisFun (Fin 2) ℝ 1) (EuclideanSpace.basisFun (Fin 2) ℝ 1) =
      lambda z * q z) :
    ‖v‖ ^ 2 ≤ alphaCoefficient T q lambda rho c z v v ∧
      alphaCoefficient T q lambda rho c z v v ≤ 2 * ‖v‖ ^ 2 := by
  let b := EuclideanSpace.basisFun (Fin 2) ℝ
  have hscale : 0 < lambda z * rho ^ 2 := mul_pos hl (sq_pos_of_pos hrho)
  obtain ⟨hlo, hhi⟩ := suAlphaPrincipalQuadratic_bounds (T z) (b 0) (b 1)
    hT hsym (Real.sqrt_pos.mpr hscale) hc (b.repr v 0) (b.repr v 1)
  have hv : b.repr v 0 • b 0 + b.repr v 1 • b 1 = v := by
    simpa only [Fin.sum_univ_two] using b.sum_repr v
  have hn : (b.repr v 0) ^ 2 + (b.repr v 1) ^ 2 = ‖v‖ ^ 2 := by
    simpa only [OrthonormalBasis.repr_apply_apply, Real.norm_eq_abs, sq_abs, Fin.sum_univ_two]
      using b.sum_sq_norm_inner_right v
  have heq : suAlphaPrincipalQuadratic (T z) (b 0) (b 1)
      (Real.sqrt (lambda z * rho ^ 2)) c (b.repr v 0) (b.repr v 1) =
      alphaCoefficient T q lambda rho c z v v := by
    rw [suAlphaPrincipalQuadratic, Real.sq_sqrt hscale.le, hv, hn]
    change ‖v‖ ^ 2 + 2 * c / (lambda z * rho ^ 2 + T z (b 0) (b 0) +
      T z (b 1) (b 1)) * T z v v = inner ℝ v v +
        2 * c / (lambda z * (rho ^ 2 + q z)) * T z v v
    rw [real_inner_self_eq_norm_sq, add_assoc, htrace]
    congr 3; ring
  rw [heq, hn] at hlo hhi
  refine ⟨hlo, hhi.trans ?_⟩
  exact mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg ‖v‖)

private theorem mapAlpha_divergence_lower
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    {B : ℝ} (hB : 0 ≤ B)
    (hcurv : ∀ x (v w : TangentSpace (𝓡 n) x),
      -B * g.inner x v v * g.inner x w w ≤ D.curvatureTensor x v w w v)
    {φ : LoopPlane → M} {q lambda : LoopPlane → ℝ} {O : Set LoopPlane}
    {p : LoopPlane} (hO : IsOpen O) (hp : p ∈ O)
    (hφ : ContMDiff (𝓡 2) (𝓡 n) ∞ φ) (hq : ContDiff ℝ ∞ q)
    (hl : ContDiff ℝ ∞ lambda)
    (henergy : ∀ r ∈ O, 2 * m60EnergyDensity g φ r = lambda r * q r)
    (hql : ∀ r ∈ O, 0 ≤ q r ∧ 1 / 4 ≤ lambda r ∧ lambda r ≤ 4)
    (hlgrad : (fderiv ℝ lambda p (EuclideanSpace.basisFun (Fin 2) ℝ 0)) ^ 2 +
      (fderiv ℝ lambda p (EuclideanSpace.basisFun (Fin 2) ℝ 1)) ^ 2 ≤ 256)
    (hllap : ∑ i : Fin 2, fderiv ℝ (fun r =>
      fderiv ℝ lambda r (EuclideanSpace.basisFun (Fin 2) ℝ i)) p
        (EuclideanSpace.basisFun (Fin 2) ℝ i) ≤ 64)
    {rho c : ℝ} (hrho : 0 < rho) (hc : 0 ≤ c) (hc' : c ≤ 1 / 32)
    (heq : ∀ b : M, ∀ r ∈ O, φ r ∈ (extChartAt (𝓡 n) b).source →
      let u := extChartAt (𝓡 n) b ∘ φ
      let Γ := CoordinateExponential.christoffelBilinear
        (g.pullbackCoefficients (extChartAt (𝓡 n) b).symm)
      ∑ i : Fin 2, ConnectionVariation.covDerivAlong Γ u
        (fun s => (rho ^ 2 + q s) ^ c •
          fderiv ℝ u s (EuclideanSpace.basisFun (Fin 2) ℝ i))
            (EuclideanSpace.basisFun (Fin 2) ℝ i) r = 0) :
    let T : LoopPlane → LoopPlane →L[ℝ] LoopPlane →L[ℝ] ℝ :=
      fun r => metricPullbackForm (n := 2) g φ r
    let D₀ := (RiemannianMetric.euclideanMetric 2).euclideanLeviCivitaData;
    -(4 * B) * (q p) ^ 2 - 164256 * q p ≤ ∑ i : Fin 2,
      fderiv ℝ (fun r => alphaCoefficient T q lambda rho c r (D₀.gradient q r)
        (EuclideanSpace.basisFun (Fin 2) ℝ i)) p
          (EuclideanSpace.basisFun (Fin 2) ℝ i) := by
  dsimp only
  let b := EuclideanSpace.basisFun (Fin 2) ℝ
  let c₀ := extChartAt (𝓡 n) (φ p)
  let u := c₀ ∘ φ
  let G := g.pullbackCoefficients c₀.symm
  let Γ := CoordinateExponential.christoffelBilinear G
  let U := O ∩ φ ⁻¹' c₀.source
  let T : LoopPlane → LoopPlane →L[ℝ] LoopPlane →L[ℝ] ℝ :=
    fun r => metricPullbackForm (n := 2) g φ r
  let D₀ := (RiemannianMetric.euclideanMetric 2).euclideanLeviCivitaData
  have hU : IsOpen U := hO.inter
    (hφ.continuous.isOpen_preimage _ (isOpen_extChartAt_source _))
  have hpU : p ∈ U := ⟨hp, mem_extChartAt_source _⟩
  have hchart (r : LoopPlane) (hr : r ∈ U) :
      ContMDiffAt (𝓡 n) (𝓡 n) ∞ c₀ (φ r) :=
    contMDiffAt_extChartAt' (by simpa only [Set.mem_preimage, c₀, extChartAt_source] using hr.2)
  have hu : ContDiffOn ℝ ∞ u U := fun r hr =>
    (contMDiffAt_iff_contDiffAt.mp ((hchart r hr).comp r (hφ r))).contDiffWithinAt
  have hdu (r : LoopPlane) (hr : r ∈ U) (v : LoopPlane) :
      fderiv ℝ u r v = mfderiv (𝓡 n) (𝓡 n) c₀ (φ r)
        (mfderiv (𝓡 2) (𝓡 n) φ r v) := by
    have h := mfderiv_comp r ((hchart r hr).mdifferentiableAt (by simp))
      ((hφ r).mdifferentiableAt (by simp))
    rw [mfderiv_eq_fderiv] at h
    exact congrArg (fun L => L v) h
  have hpair (r : LoopPlane) (hr : r ∈ U) (v w : LoopPlane) :
      G (u r) (fderiv ℝ u r v) (fderiv ℝ u r w) = T r v w := by
    rw [hdu r hr v, hdu r hr w]
    exact ConjugateVariation.chartCoefficients_apply g (φ p) hr.2 _ _
  have hG (r : LoopPlane) (hr : r ∈ U) : ContDiffAt ℝ ∞ G (u r) :=
    (g.contDiffOn_chartCoefficients (φ p)).contDiffAt
      ((isOpen_extChartAt_target (φ p)).mem_nhds (c₀.map_source hr.2))
  have hΓ (r : LoopPlane) (hr : r ∈ U) : ContDiffAt ℝ ∞ Γ (u r) :=
    CoordinateExponential.contDiffAt_christoffelBilinear (hG r hr)
      (g.isInvertible_chartCoefficients (φ p) (c₀.map_source hr.2))
  have hGu : ContDiffOn ℝ ∞ (fun r => G (u r)) U := fun r hr =>
    ((hG r hr).comp r (hu.contDiffAt (hU.mem_nhds hr))).contDiffWithinAt
  have hcompat (r : LoopPlane) (hr : r ∈ U) (v : LoopPlane)
      (y z : EuclideanSpace ℝ (Fin n)) :
      fderiv ℝ (fun s => G (u s) y z) r v =
        G (u r) (Γ (u r) (fderiv ℝ u r v) y) z +
          G (u r) y (Γ (u r) (fderiv ℝ u r v) z) := by
    have hd₀ := ((hG r hr).differentiableAt (by simp)).hasFDerivAt.comp r
      ((hu.contDiffAt (hU.mem_nhds hr)).differentiableAt (by simp)).hasFDerivAt
    have hd := (hd₀.clm_apply (hasFDerivAt_const y r)).clm_apply (hasFDerivAt_const z r)
    dsimp only [Function.comp_def] at hd
    rw [hd.fderiv]
    simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
      zero_apply, map_zero, zero_add]
    exact ConjugateVariation.isMetricCompatibleAt_chartCoefficients g (φ p)
      (c₀.map_source hr.2) _ _ _
  have hnonneg (w : EuclideanSpace ℝ (Fin n)) : 0 ≤ G (u p) w w := by
    change 0 ≤ g.inner _ (mfderiv (𝓡 n) (𝓡 n) c₀.symm (u p) w)
      (mfderiv (𝓡 n) (𝓡 n) c₀.symm (u p) w)
    by_cases hw : mfderiv (𝓡 n) (𝓡 n) c₀.symm (u p) w = 0
    · simp [hw]
    · exact (g.pos _ _ hw).le
  have htrace (r : LoopPlane) (hr : r ∈ U) :
      suLocalSquaredDifferential (fun s => G (u s)) u (b 0) (b 1) r = lambda r * q r := by
    rw [suLocalSquaredDifferential, hpair r hr, hpair r hr, ← henergy r hr.1]
    simp only [m60EnergyDensity, Matrix.trace_fin_two, m60AreaGram, T, b]
    change g.inner _ (mfderiv (𝓡 2) (𝓡 n) φ r (b 0))
      (mfderiv (𝓡 2) (𝓡 n) φ r (b 0)) +
      g.inner _ (mfderiv (𝓡 2) (𝓡 n) φ r (b 1))
        (mfderiv (𝓡 2) (𝓡 n) φ r (b 1)) = _
    ring
  have hR (v w : LoopPlane) : G (u p)
      (ConnectionVariation.christoffelCurvature Γ (u p) (fderiv ℝ u p v)
        (fderiv ℝ u p w) (fderiv ℝ u p v)) (fderiv ℝ u p w) =
      D.curvatureTensor (φ p) (mfderiv (𝓡 2) (𝓡 n) φ p v)
        (mfderiv (𝓡 2) (𝓡 n) φ p w) (mfderiv (𝓡 2) (𝓡 n) φ p w)
        (mfderiv (𝓡 2) (𝓡 n) φ p v) := by
    rw [← CoordinateExponential.coordinateCurvature_eq_christoffelCurvature
      ((hΓ p hpU).differentiableAt (by simp)), hdu p hpU v, hdu p hpU w]
    erw [ConnectionVariation.coordinateCurvature_in_chart g D (φ p) hpU.2]
    exact ConjugateVariation.chartCoefficients_apply g (φ p) hpU.2 _ _
  have hcb : -B * (lambda p * q p) ^ 2 ≤
      2 * (G (u p) (ConnectionVariation.christoffelCurvature Γ (u p)
          (fderiv ℝ u p (b 1)) (fderiv ℝ u p (b 0)) (fderiv ℝ u p (b 1)))
          (fderiv ℝ u p (b 0)) +
        G (u p) (ConnectionVariation.christoffelCurvature Γ (u p)
          (fderiv ℝ u p (b 0)) (fderiv ℝ u p (b 1)) (fderiv ℝ u p (b 0)))
          (fderiv ℝ u p (b 1))) := by
    rw [hR, hR, ← htrace p hpU, suLocalSquaredDifferential, hpair p hpU, hpair p hpU]
    have h0 := hcurv (φ p) (mfderiv (𝓡 2) (𝓡 n) φ p (b 1))
      (mfderiv (𝓡 2) (𝓡 n) φ p (b 0))
    have h1 := hcurv (φ p) (mfderiv (𝓡 2) (𝓡 n) φ p (b 0))
      (mfderiv (𝓡 2) (𝓡 n) φ p (b 1))
    have hs := mul_nonneg hB (sq_nonneg (T p (b 0) (b 0) - T p (b 1) (b 1)))
    change -B * (T p (b 1) (b 1)) * (T p (b 0) (b 0)) ≤ _ at h0
    change -B * (T p (b 0) (b 0)) * (T p (b 1) (b 1)) ≤ _ at h1
    nlinarith only [h0, h1, hs]
  have hlow := conformalAlphaFlux_divergence_lower hU hpU (b 0) (b 1) hu hGu
    hq.contDiffOn hl.contDiffOn hΓ hcompat (fun _ _ => g.symm _ _ _) hnonneg
    (fun r _ => ConjugateVariation.christoffelBilinear_chart_symm g (φ p) (u r))
    htrace (fun r hr => hql r hr.1) hlgrad
    (by simpa only [Fin.sum_univ_two] using hllap) hrho hc hc' hB
    (fun r hr => by simpa only [Fin.sum_univ_two] using heq (φ p) r hr.1 hr.2) hcb
  have hflux (v : LoopPlane) :
      (fun r => alphaCoefficient T q lambda rho c r (D₀.gradient q r) v) =ᶠ[𝓝 p]
      conformalAlphaFlux (fun r => G (u r)) u q lambda rho c (b 0) (b 1) v := by
    filter_upwards [hU.mem_nhds hpU] with r hr
    have hi : inner (E := LoopPlane) ℝ (D₀.gradient q r) v = fderiv ℝ q r v := by
      have h := D₀.inner_gradient q r v
      simp +instances only [RiemannianMetric.euclideanMetric_inner,
        mvfderiv, mfderiv_eq_fderiv, NormedSpace.fromTangentSpace] at h
      exact h
    change inner (E := LoopPlane) ℝ (D₀.gradient q r) v +
      (2 * c / (lambda r * (rho ^ 2 + q r))) * T r (D₀.gradient q r) v = _
    erw [hi, ← hpair r hr (D₀.gradient q r) v, euclideanGradient_basis]
    simp only [Fin.sum_univ_two, map_add, map_smul, conformalAlphaFlux, b]
  change _ ≤ ∑ i : Fin 2, fderiv ℝ
    (fun r => alphaCoefficient T q lambda rho c r (D₀.gradient q r) (b i)) p (b i)
  rw [Fin.sum_univ_two, (hflux (b 0)).fderiv_eq, (hflux (b 1)).fderiv_eq]
  exact hlow

theorem exists_divergence_heinz :
    ∃ B : ℝ, 0 < B ∧ ∀ (K L R : ℝ), 0 ≤ K → 0 ≤ L → 0 < R → R ≤ 1 →
      ∀ D : LeviCivitaData (RiemannianMetric.euclideanMetric 2),
      ∀ A : LoopPlane → LoopPlane →L[ℝ] LoopPlane →L[ℝ] ℝ,
      Continuous A → (∀ x v w, A x v w = A x w v) →
      (∀ x v, ‖v‖ ^ 2 ≤ A x v v ∧ A x v v ≤ 2 * ‖v‖ ^ 2) →
      ∀ u : LoopPlane → ℝ, ContDiff ℝ ∞ u → (∀ x, 0 ≤ u x) →
      (∀ φ : LoopPlane → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
        tsupport φ ⊆ Metric.ball 0 R → (∀ x, 0 ≤ φ x) →
        (∫ x, A x (D.gradient u x) (D.gradient φ x)) ≤
          K * (∫ x, (u x) ^ 2 * φ x) + L * (∫ x, u x * φ x)) →
      B * K * (∫ x in Metric.closedBall 0 R, u x) ≤ 1 →
      R ^ 2 * u 0 ≤ B * (1 + L) * (∫ x in Metric.closedBall 0 R, u x) := by
  obtain ⟨B, hB, hest⟩ := exists_positive_divergence_heinz
  refine ⟨2 * B, by positivity, fun K L R hK hL hR hR1 D A hA hs hell u hu hp hw he => ?_⟩
  let S := Metric.closedBall (0 : LoopPlane) R
  let E : ℝ := ∫ x in S, u x
  let V : ℝ := volume.real S
  have hE : 0 ≤ E := integral_nonneg hp
  have hiu : IntegrableOn u S volume :=
    hu.continuous.continuousOn.integrableOn_compact (isCompact_closedBall _ _)
  have hint (d : ℝ) : (∫ x in S, u x + d) = E + V * d := by
    have hic : IntegrableOn (fun _ : LoopPlane => d) S volume :=
      continuousOn_const.integrableOn_compact (isCompact_closedBall _ _)
    rw [integral_add hiu hic, setIntegral_const, smul_eq_mul]
  have he0 : B * K * (E + V * 0) < 1 := by
    change 2 * B * K * E ≤ 1 at he
    simp only [mul_zero, add_zero]; nlinarith only [he]
  have hcont : Continuous (fun d : ℝ => B * K * (E + V * d)) := by fun_prop
  have hev : ∀ᶠ d : ℝ in 𝓝[>] 0, B * K * (E + V * d) < 1 :=
    (hcont.continuousAt.eventually (gt_mem_nhds he0)).filter_mono nhdsWithin_le_nhds
  have hb : ∀ᶠ d : ℝ in 𝓝[>] 0,
      R ^ 2 * (u 0 + d) ≤ B * (1 + L) * (E + V * d) := by
    filter_upwards [hev, self_mem_nhdsWithin] with d hed hdp
    have hd : 0 < d := hdp
    have hud : ContDiff ℝ ∞ (fun x => u x + d) := hu.add contDiff_const
    have hgrad (x : LoopPlane) : D.gradient (fun y => u y + d) x = D.gradient u x := by
      rw [euclideanGradient_basis, euclideanGradient_basis]
      simp only [fderiv_add_const]
    have hw' : ∀ φ : LoopPlane → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
        tsupport φ ⊆ Metric.ball 0 R → (∀ x, 0 ≤ φ x) →
        (∫ x, A x (D.gradient (fun y => u y + d) x) (D.gradient φ x)) ≤
          K * (∫ x, (u x + d) ^ 2 * φ x) + L * (∫ x, (u x + d) * φ x) := by
      intro φ hφ hφc hφs hφp
      simp only [hgrad]
      apply (hw φ hφ hφc hφs hφp).trans (add_le_add
        (mul_le_mul_of_nonneg_left ?_ hK) (mul_le_mul_of_nonneg_left ?_ hL))
      · apply integral_mono
          (((hu.continuous.pow 2).mul hφ.continuous).integrable_of_hasCompactSupport hφc.mul_left)
          (((hud.continuous.pow 2).mul hφ.continuous).integrable_of_hasCompactSupport hφc.mul_left)
        intro x
        change (u x) ^ 2 * φ x ≤ (u x + d) ^ 2 * φ x
        exact mul_le_mul_of_nonneg_right (by nlinarith [hp x]) (hφp x)
      · apply integral_mono
          ((hu.continuous.mul hφ.continuous).integrable_of_hasCompactSupport hφc.mul_left)
          ((hud.continuous.mul hφ.continuous).integrable_of_hasCompactSupport hφc.mul_left)
        intro x
        change u x * φ x ≤ (u x + d) * φ x
        exact mul_le_mul_of_nonneg_right (by linarith) (hφp x)
    have hm := hest K L R hK hL hR hR1 D A hA hs hell (fun x => u x + d) hud
      (fun x => by linarith [hp x]) hw' (by
        rw [show Metric.closedBall (0 : LoopPlane) R = S from rfl, hint]; exact hed.le)
    rw [show Metric.closedBall (0 : LoopPlane) R = S from rfl, hint] at hm
    exact hm
  have hleft : Tendsto (fun d : ℝ => R ^ 2 * (u 0 + d)) (𝓝[>] 0)
      (𝓝 (R ^ 2 * u 0)) := by
    have ht : Continuous (fun d : ℝ => R ^ 2 * (u 0 + d)) := by fun_prop
    simpa only [add_zero] using ht.continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds (s := Ioi 0) (a := (0 : ℝ)))
  have hright : Tendsto (fun d : ℝ => B * (1 + L) * (E + V * d)) (𝓝[>] 0)
      (𝓝 (B * (1 + L) * E)) := by
    have ht : Continuous (fun d : ℝ => B * (1 + L) * (E + V * d)) := by fun_prop
    simpa only [mul_zero, add_zero] using ht.continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds (s := Ioi 0) (a := (0 : ℝ)))
  have hle := le_of_tendsto_of_tendsto hleft hright hb
  change R ^ 2 * u 0 ≤ 2 * B * (1 + L) * E
  nlinarith only [hle, mul_nonneg (mul_nonneg hB.le (by linarith : 0 ≤ 1 + L)) hE]

private theorem divergence_to_weak
    (D : LeviCivitaData (RiemannianMetric.euclideanMetric 2))
    {A : LoopPlane → LoopPlane →L[ℝ] LoopPlane →L[ℝ] ℝ} {u : LoopPlane → ℝ}
    (hA : ContDiff ℝ ∞ A) (hu : ContDiff ℝ ∞ u) {K L R : ℝ}
    (hlow : ∀ p ∈ Metric.ball 0 R, -K * (u p) ^ 2 - L * u p ≤ ∑ i : Fin 2,
      fderiv ℝ (fun x => A x (D.gradient u x) (EuclideanSpace.basisFun (Fin 2) ℝ i))
        p (EuclideanSpace.basisFun (Fin 2) ℝ i))
    {φ : LoopPlane → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ Metric.ball 0 R) (hp : ∀ x, 0 ≤ φ x) :
    (∫ x, A x (D.gradient u x) (D.gradient φ x)) ≤
      K * (∫ x, (u x) ^ 2 * φ x) + L * (∫ x, u x * φ x) := by
  let b := EuclideanSpace.basisFun (Fin 2) ℝ
  let V : Fin 2 → LoopPlane → ℝ := fun i x => A x (D.gradient u x) (b i)
  have hgrad : ContDiff ℝ ∞ (D.gradient u) :=
    contMDiff_vectorSpace_iff_contDiff.mp (D.contMDiff_gradient (contMDiff_iff_contDiff.mpr hu))
  have hV (i : Fin 2) : ContDiff ℝ ∞ (V i) :=
    (hA.clm_apply hgrad).clm_apply contDiff_const
  have hdiv : Continuous (fun x => ∑ i : Fin 2, fderiv ℝ (V i) x (b i)) :=
    continuous_finsetSum _ fun i _ =>
      ((hV i).continuous_fderiv (by simp)).clm_apply continuous_const
  have hi := (hφ.continuous.mul hdiv).integrable_of_hasCompactSupport (μ := volume) hc.mul_right
  have hi1 := ((hu.continuous.pow 2).mul hφ.continuous).integrable_of_hasCompactSupport
    (μ := volume) hc.mul_left
  have hi2 := (hu.continuous.mul hφ.continuous).integrable_of_hasCompactSupport
    (μ := volume) hc.mul_left
  have hparts := Poincare.integral_mul_coordinate_divergence (hφ.of_le (by simp)) hc
    (fun i x _ => (hV i).contDiffAt.of_le (by simp))
  have hsum : (fun x => ∑ i : Fin 2, fderiv ℝ φ x (b i) * V i x) =
      (fun x => A x (D.gradient u x) (D.gradient φ x)) := by
    funext x
    rw [euclideanGradient_basis D φ x]
    simp only [map_sum, map_smul, smul_eq_mul, V, b]
  change (∫ x, φ x * ∑ i : Fin 2, fderiv ℝ (V i) x (b i)) =
    -(∫ x, ∑ i : Fin 2, fderiv ℝ φ x (b i) * V i x) at hparts
  rw [hsum] at hparts
  have hm := integral_mono hi.neg ((hi1.const_mul K).add (hi2.const_mul L))
    (show ∀ x, -(φ x * ∑ i : Fin 2, fderiv ℝ (V i) x (b i)) ≤
      K * ((u x) ^ 2 * φ x) + L * (u x * φ x) from by
        intro x
        by_cases hx : x ∈ tsupport φ
        · have h := mul_le_mul_of_nonneg_left (hlow x (hs hx)) (hp x)
          change φ x * (-K * (u x) ^ 2 - L * u x) ≤
            φ x * ∑ i : Fin 2, fderiv ℝ (V i) x (b i) at h
          nlinarith only [h]
        · simp only [image_eq_zero_of_notMem_tsupport hx, zero_mul, mul_zero,
            neg_zero, add_zero, le_refl])
  simp only [Pi.neg_apply, Pi.mul_apply, Pi.add_apply] at hm
  rw [integral_neg, hparts] at hm
  erw [integral_add (hi1.const_mul K) (hi2.const_mul L)] at hm
  simp only [neg_neg, integral_const_mul] at hm
  exact hm

theorem m60AlphaMap_small_energy [CompactSpace M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧ ∀ (rho alpha R : ℝ),
      0 < rho → 1 ≤ alpha → alpha ≤ 33 / 32 → 0 < R → R ≤ 1 →
      ∀ φ : LoopPlane → M, ContMDiff (𝓡 2) (𝓡 n) ∞ φ →
      ∀ lambda : LoopPlane → ℝ, ContDiff ℝ ∞ lambda → (∀ x, 0 < lambda x) →
      let q := fun x => 2 * m60EnergyDensity g φ x / lambda x
      (∀ p ∈ Metric.ball 0 R, 1 / 4 ≤ lambda p ∧ lambda p ≤ 4 ∧
        (fderiv ℝ lambda p (EuclideanSpace.basisFun (Fin 2) ℝ 0)) ^ 2 +
          (fderiv ℝ lambda p (EuclideanSpace.basisFun (Fin 2) ℝ 1)) ^ 2 ≤ 256 ∧
        (∑ i : Fin 2, fderiv ℝ (fun x => fderiv ℝ lambda x
          (EuclideanSpace.basisFun (Fin 2) ℝ i)) p
            (EuclideanSpace.basisFun (Fin 2) ℝ i)) ≤ 64) →
      (∀ b : M, ∀ x ∈ Metric.ball 0 R, φ x ∈ (extChartAt (𝓡 n) b).source →
        let u := extChartAt (𝓡 n) b ∘ φ
        let Γ := CoordinateExponential.christoffelBilinear
          (g.pullbackCoefficients (extChartAt (𝓡 n) b).symm)
        ∑ i : Fin 2, ConnectionVariation.covDerivAlong Γ u
          (fun y => (rho ^ 2 + q y) ^ (alpha - 1) •
            fderiv ℝ u y (EuclideanSpace.basisFun (Fin 2) ℝ i))
              (EuclideanSpace.basisFun (Fin 2) ℝ i) x = 0) →
      (∫ x in Metric.closedBall 0 R, q x) ≤ ε →
      R ^ 2 * q 0 ≤ C * (∫ x in Metric.closedBall 0 R, q x) := by
  obtain ⟨B, hB, hcurv⟩ := m01_riemannEvaluation_uniform_bound D
  obtain ⟨H, hH, hest⟩ := exists_divergence_heinz
  refine ⟨1 / (H * (4 * B)), H * (1 + 164256), by positivity, by positivity,
    fun rho alpha R hrho halpha halpha' hR hR1 φ hφ lambda hl hlpos => ?_⟩
  let q := fun x => 2 * m60EnergyDensity g φ x / lambda x
  change (∀ p ∈ Metric.ball 0 R, _) → _
  intro hlbound heq hsmall
  let T : LoopPlane → LoopPlane →L[ℝ] LoopPlane →L[ℝ] ℝ :=
    fun x => metricPullbackForm (n := 2) g φ x
  let A := alphaCoefficient T q lambda rho (alpha - 1)
  let D₀ := (RiemannianMetric.euclideanMetric 2).euclideanLeviCivitaData
  have hpos (x : M) (v : TangentSpace (𝓡 n) x) : 0 ≤ g.inner x v v := by
    by_cases hv : v = 0
    · simp [hv]
    · exact (g.pos x v hv).le
  have hcb (x : M) (v w : TangentSpace (𝓡 n) x) :
      -B * g.inner x v v * g.inner x w w ≤ D.curvatureTensor x v w w v := by
    have h := hcurv x ![v, w, w, v]
    simp only [LeviCivitaData.riemannEvaluation, Fin.prod_univ_succ, Fin.prod_univ_zero,
      Matrix.cons_val_zero, Matrix.cons_val_succ, mul_one, RiemannianMetric.tangentNorm] at h
    have ht : Real.sqrt (g.inner x v v) * (Real.sqrt (g.inner x w w) *
        (Real.sqrt (g.inner x w w) * Real.sqrt (g.inner x v v))) =
        g.inner x v v * g.inner x w w := by
      calc
        _ = (Real.sqrt (g.inner x v v)) ^ 2 * (Real.sqrt (g.inner x w w)) ^ 2 := by ring
        _ = _ := by rw [Real.sq_sqrt (hpos x v), Real.sq_sqrt (hpos x w)]
    rw [ht] at h
    change |D.curvatureTensor x v w w v| ≤ B * (g.inner x v v * g.inner x w w) at h
    nlinarith only [(abs_le.mp h).1]
  have henergy (x : LoopPlane) : 2 * m60EnergyDensity g φ x = lambda x * q x := by
    dsimp only [q]; field_simp [(hlpos x).ne']
  have hqp (x : LoopPlane) : 0 ≤ q x :=
    div_nonneg (mul_nonneg (by norm_num) (m60EnergyDensity_nonneg g φ x)) (hlpos x).le
  have hq : ContDiff ℝ ∞ q := by
    dsimp only [q, m60EnergyDensity]
    simp only [Matrix.trace_fin_two]
    exact (contDiff_const.mul (contDiff_const.mul
      ((m60AreaGram_entry_contDiff g hφ 0 0).add
        (m60AreaGram_entry_contDiff g hφ 1 1)))).div hl (fun x => (hlpos x).ne')
  have hT : ContDiff ℝ ∞ T := planePullback_contDiff g hφ
  have hcoef : ContDiff ℝ ∞ (fun x => 2 * (alpha - 1) / (lambda x * (rho ^ 2 + q x))) :=
    contDiff_const.div (hl.mul (contDiff_const.add hq))
      (fun x => mul_ne_zero (hlpos x).ne' (by have := hqp x; positivity))
  have hA : ContDiff ℝ ∞ A := by
    apply (contDiff_clm_apply_iff (E := LoopPlane) (F := LoopPlane →L[ℝ] ℝ)).mpr
    intro v
    apply (contDiff_clm_apply_iff (E := LoopPlane) (F := ℝ)).mpr
    intro w
    exact contDiff_const.add (hcoef.mul ((hT.clm_apply contDiff_const).clm_apply contDiff_const))
  have hsym (x v w : LoopPlane) : A x v w = A x w v := by
    change inner ℝ v w + _ * T x v w = inner ℝ w v + _ * T x w v
    rw [real_inner_comm]
    congr 1
    exact congrArg (fun z : ℝ => (2 * (alpha - 1) / (lambda x * (rho ^ 2 + q x))) * z)
      (g.symm _ _ _)
  have hell (x v : LoopPlane) : ‖v‖ ^ 2 ≤ A x v v ∧ A x v v ≤ 2 * ‖v‖ ^ 2 := by
    apply alphaCoefficient_elliptic T q lambda x v
      (fun w => hpos _ _) (fun w y => g.symm _ _ _) (hlpos x) hrho
      (by linarith) (by linarith)
    rw [← henergy]
    change m60AreaGram g φ x 0 0 + m60AreaGram g φ x 1 1 = 2 * m60EnergyDensity g φ x
    simp only [m60EnergyDensity, Matrix.trace_fin_two]
    ring
  apply hest (4 * B) 164256 R (by positivity) (by norm_num) hR hR1 D₀ A hA.continuous
    hsym hell q hq hqp ?_ ?_
  · intro ψ hψ hψc hψs hψp
    apply divergence_to_weak D₀ hA hq (fun p hp => ?_) hψ hψc hψs hψp
    exact mapAlpha_divergence_lower D hB.le hcb Metric.isOpen_ball hp hφ hq hl
      (fun x _ => henergy x) (fun x hx => ⟨hqp x, (hlbound x hx).1, (hlbound x hx).2.1⟩)
      (hlbound p hp).2.2.1 (hlbound p hp).2.2.2 hrho (by linarith) (by linarith) heq
  · have ht := (le_div_iff₀ (show 0 < H * (4 * B) by positivity)).mp hsmall
    nlinarith only [ht]

end PoincareConjecture.M60
