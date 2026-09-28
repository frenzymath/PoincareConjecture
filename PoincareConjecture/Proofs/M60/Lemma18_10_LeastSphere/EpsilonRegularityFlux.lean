import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.SUHarmonicEnergyGap
import PoincareConjecture.Proofs.M60.Mathlib.MapMetricBochner
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Euclidean
import Mathlib.Algebra.QuadraticDiscriminant

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped ContDiff Topology Manifold
namespace PoincareConjecture.M60
open ConnectionVariation
variable {P E : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
private theorem covDerivAlong_scalar_mul
    (Γ : E → E →L[ℝ] E →L[ℝ] E) (u Y : P → E) (w : P → ℝ)
    {p : P} (hw : DifferentiableAt ℝ w p) (hY : DifferentiableAt ℝ Y p)
    (d : P) :
    covDerivAlong Γ u (fun q => w q • Y q) d p =
      fderiv ℝ w p d • Y p + w p • covDerivAlong Γ u Y d p := by
  rw [covDerivAlong, fderiv_fun_smul hw hY]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, map_smul,
    covDerivAlong, smul_add]
  abel

theorem suAlphaWeight_fderiv {e : P → ℝ} {p : P} {rho c : ℝ}
    (he : DifferentiableAt ℝ e p) (hpos : 0 < rho ^ 2 + e p) (d : P) :
    fderiv ℝ (fun q => (rho ^ 2 + e q) ^ c) p d =
      (rho ^ 2 + e p) ^ c * (c / (rho ^ 2 + e p)) * fderiv ℝ e p d := by
  have hd := ((hasFDerivAt_const (rho ^ 2) p).add he.hasFDerivAt).rpow_const
    (p := c) (Or.inl hpos.ne')
  change HasFDerivAt (fun q => (rho ^ 2 + e q) ^ c)
    ((c * (rho ^ 2 + e p) ^ (c - 1)) • (0 + fderiv ℝ e p)) p at hd
  rw [hd.fderiv]
  simp only [zero_add, smul_apply, smul_eq_mul]
  rw [Real.rpow_sub hpos]
  simp only [Real.rpow_one]
  ring

theorem suAlphaEquation_tension
    (Γ : E → E →L[ℝ] E →L[ℝ] E) (u : P → E)
    {e : P → ℝ} {p : P} {rho c : ℝ} (d₀ d₁ : P)
    (he : DifferentiableAt ℝ e p) (hu : ContDiffAt ℝ 2 u p)
    (hpos : 0 < rho ^ 2 + e p)
    (heq :
      covDerivAlong Γ u
        (fun q => (rho ^ 2 + e q) ^ c • fderiv ℝ u q d₀) d₀ p +
      covDerivAlong Γ u
        (fun q => (rho ^ 2 + e q) ^ c • fderiv ℝ u q d₁) d₁ p = 0) :
    covDerivAlong Γ u (fun q => fderiv ℝ u q d₀) d₀ p +
      covDerivAlong Γ u (fun q => fderiv ℝ u q d₁) d₁ p =
        -(c / (rho ^ 2 + e p)) •
          (fderiv ℝ e p d₀ • fderiv ℝ u p d₀ +
            fderiv ℝ e p d₁ • fderiv ℝ u p d₁) := by
  have hw : DifferentiableAt ℝ (fun q => (rho ^ 2 + e q) ^ c) p :=
    (differentiableAt_const (rho ^ 2) |>.add he).rpow_const (Or.inl hpos.ne')
  have hdu (d : P) : DifferentiableAt ℝ (fun q => fderiv ℝ u q d) p :=
    ((hu.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt
      (by norm_num)
  rw [covDerivAlong_scalar_mul Γ u _ _ hw (hdu d₀),
    covDerivAlong_scalar_mul Γ u _ _ hw (hdu d₁),
    suAlphaWeight_fderiv he hpos, suAlphaWeight_fderiv he hpos] at heq
  have hwpos : 0 < (rho ^ 2 + e p) ^ c := Real.rpow_pos_of_pos hpos c
  apply smul_right_injective E hwpos.ne'
  dsimp only
  rw [smul_add]
  have hleft :
      (rho ^ 2 + e p) ^ c •
        covDerivAlong Γ u (fun q => fderiv ℝ u q d₀) d₀ p +
      (rho ^ 2 + e p) ^ c •
        covDerivAlong Γ u (fun q => fderiv ℝ u q d₁) d₁ p =
      -(((rho ^ 2 + e p) ^ c * (c / (rho ^ 2 + e p)) * fderiv ℝ e p d₀) •
          fderiv ℝ u p d₀ +
        ((rho ^ 2 + e p) ^ c * (c / (rho ^ 2 + e p)) * fderiv ℝ e p d₁) •
          fderiv ℝ u p d₁) := by
    apply eq_neg_iff_add_eq_zero.mpr
    convert heq using 1
    abel
  rw [hleft]; module

def suAlphaPrincipalQuadratic (G : E →L[ℝ] E →L[ℝ] ℝ)
    (a b : E) (rho c x y : ℝ) : ℝ :=
  x ^ 2 + y ^ 2 + 2 * c / (rho ^ 2 + G a a + G b b) *
    G (x • a + y • b) (x • a + y • b)

theorem suAlphaPrincipalQuadratic_bounds
    (G : E →L[ℝ] E →L[ℝ] ℝ) (a b : E) {rho c : ℝ}
    (hG : ∀ v : E, 0 ≤ G v v) (hsym : ∀ v w : E, G v w = G w v)
    (hrho : 0 < rho) (hc : 0 ≤ c) (x y : ℝ) :
    x ^ 2 + y ^ 2 ≤ suAlphaPrincipalQuadratic G a b rho c x y ∧
      suAlphaPrincipalQuadratic G a b rho c x y ≤ (1 + 2 * c) * (x ^ 2 + y ^ 2) := by
  have hden : 0 < rho ^ 2 + G a a + G b b := by
    have ha := hG a; have hb := hG b; positivity
  have hquad : G (x • a + y • b) (x • a + y • b) ≤
      (G a a + G b b) * (x ^ 2 + y ^ 2) := by
    have hnonneg := hG (y • a - x • b)
    simp only [map_add, map_sub, map_smul, add_apply, sub_apply, smul_apply,
      smul_eq_mul] at hnonneg ⊢
    rw [hsym b a] at hnonneg ⊢
    nlinarith only [hnonneg]
  have hquot : G (x • a + y • b) (x • a + y • b) /
      (rho ^ 2 + G a a + G b b) ≤ x ^ 2 + y ^ 2 := by
    apply (div_le_iff₀ hden).mpr
    nlinarith [mul_nonneg (sq_nonneg rho) (add_nonneg (sq_nonneg x) (sq_nonneg y))]
  have hm := mul_le_mul_of_nonneg_left hquot
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hc)
  unfold suAlphaPrincipalQuadratic
  constructor
  · exact le_add_of_nonneg_right (mul_nonneg (div_nonneg (by positivity) hden.le) (hG _))
  · calc
      _ = x ^ 2 + y ^ 2 + 2 * c *
          (G (x • a + y • b) (x • a + y • b) /
            (rho ^ 2 + G a a + G b b)) := by ring
      _ ≤ x ^ 2 + y ^ 2 + 2 * c * (x ^ 2 + y ^ 2) := add_le_add le_rfl hm
      _ = _ := by ring
private def localTension (Γ : E → E →L[ℝ] E →L[ℝ] E) (u : P → E)
    (d e : P) (p : P) : E :=
  covDerivAlong Γ u (fun q => fderiv ℝ u q d) d p +
    covDerivAlong Γ u (fun q => fderiv ℝ u q e) e p
private theorem contDiffAt_localTension
    {Γ : E → E →L[ℝ] E →L[ℝ] E} {u : P → E} {p : P}
    (hΓ : ContDiffAt ℝ ∞ Γ (u p)) (hu : ContDiffAt ℝ ∞ u p) (d e : P) :
    ContDiffAt ℝ ∞ (localTension Γ u d e) p :=
  (contDiffAt_covDerivAlong hΓ hu
    ((hu.fderiv_right (by simp)).clm_apply contDiffAt_const) d).add
  (contDiffAt_covDerivAlong hΓ hu
    ((hu.fderiv_right (by simp)).clm_apply contDiffAt_const) e)
private theorem covDerivAlong_tension_trace
    {Γ : E → E →L[ℝ] E →L[ℝ] E} {u : P → E} {p : P} (d e : P)
    (hu : ContDiffAt ℝ ∞ u p) (hΓ : ContDiffAt ℝ ∞ Γ (u p))
    (hsymm : ∀ᶠ q in 𝓝 p, ∀ a b, Γ (u q) a b = Γ (u q) b a) :
    covDerivAlong Γ u (covDerivAlong Γ u (fun r => fderiv ℝ u r d) d) d p +
      covDerivAlong Γ u (covDerivAlong Γ u (fun r => fderiv ℝ u r d) e) e p =
      covDerivAlong Γ u (localTension Γ u d e) d p +
      christoffelCurvature Γ (u p) (fderiv ℝ u p e) (fderiv ℝ u p d)
        (fderiv ℝ u p e) := by
  have hu2 : ContDiffAt ℝ 2 u p := hu.of_le (WithTop.coe_le_coe.mpr le_top)
  have hdu (v : P) : ContDiffAt ℝ ∞ (fun r => fderiv ℝ u r v) p :=
    (hu.fderiv_right (by simp)).clm_apply contDiffAt_const
  have hH (v w : P) : ContDiffAt ℝ ∞
      (covDerivAlong Γ u (fun r => fderiv ℝ u r v) w) p :=
    contDiffAt_covDerivAlong hΓ hu (hdu v) w
  have hswap : covDerivAlong Γ u (fun r => fderiv ℝ u r d) e =ᶠ[𝓝 p]
      covDerivAlong Γ u (fun r => fderiv ℝ u r e) d := by
    filter_upwards [hu2.eventually (by norm_num), hsymm] with q hq hsq
    exact covDerivAlong_fderiv_symm hq hsq e d
  have hcomm := covDerivAlong_comm hu2 ((hdu e).of_le (WithTop.coe_le_coe.mpr le_top))
    (hΓ.differentiableAt (by simp)) e d
  rw [covDerivAlong_congr Γ u hswap e]
  unfold localTension
  rw [covDerivAlong_add Γ u ((hH d d).differentiableAt (by simp))
    ((hH e e).differentiableAt (by simp))]
  rw [sub_eq_iff_eq_add.mp hcomm]
  abel

def suLocalSquaredDifferential (G : P → E →L[ℝ] E →L[ℝ] ℝ)
    (u : P → E) (d e p : P) : ℝ :=
  G p (fderiv ℝ u p d) (fderiv ℝ u p d) +
    G p (fderiv ℝ u p e) (fderiv ℝ u p e)

def suLocalEnergyFlux (Γ : E → E →L[ℝ] E →L[ℝ] E)
    (G : P → E →L[ℝ] E →L[ℝ] ℝ) (u : P → E) (d e v p : P) : ℝ :=
  fderiv ℝ (suLocalSquaredDifferential G u d e) p v -
    2 * G p (localTension Γ u d e p) (fderiv ℝ u p v)
private theorem metric_column_laplacian
    {Γ : E → E →L[ℝ] E →L[ℝ] E} {u : P → E}
    {G : P → E →L[ℝ] E →L[ℝ] ℝ} {O : Set P} {p : P}
    (hO : IsOpen O) (hp : p ∈ O) (d e : P)
    (hu : ContDiffOn ℝ ∞ u O) (hG : ContDiffOn ℝ ∞ G O)
    (hΓ : ∀ q ∈ O, ContDiffAt ℝ ∞ Γ (u q))
    (hcompat : ∀ q ∈ O, ∀ v : P, ∀ b c : E,
      fderiv ℝ (fun r => G r b c) q v =
        G q (Γ (u q) (fderiv ℝ u q v) b) c +
          G q b (Γ (u q) (fderiv ℝ u q v) c))
    (hGsymm : ∀ b c : E, G p b c = G p c b)
    (hΓsymm : ∀ q ∈ O, ∀ b c, Γ (u q) b c = Γ (u q) c b) :
    (fderiv ℝ (fun q => fderiv ℝ
      (fun r => G r (fderiv ℝ u r d) (fderiv ℝ u r d)) q d) p d +
    fderiv ℝ (fun q => fderiv ℝ
      (fun r => G r (fderiv ℝ u r d) (fderiv ℝ u r d)) q e) p e) =
      2 * (G p (covDerivAlong Γ u (fun r => fderiv ℝ u r d) d p)
          (covDerivAlong Γ u (fun r => fderiv ℝ u r d) d p) +
        G p (covDerivAlong Γ u (fun r => fderiv ℝ u r d) e p)
          (covDerivAlong Γ u (fun r => fderiv ℝ u r d) e p)) +
      2 * G p (covDerivAlong Γ u (localTension Γ u d e) d p) (fderiv ℝ u p d) +
      2 * G p (christoffelCurvature Γ (u p) (fderiv ℝ u p e)
        (fderiv ℝ u p d) (fderiv ℝ u p e)) (fderiv ℝ u p d) := by
  have hA : ContDiffOn ℝ ∞ (mapConnectionCoefficients Γ u) O := by
    intro q hq
    exact (contDiffAt_mapConnectionCoefficients (hΓ q hq)
      (hu.contDiffAt (hO.mem_nhds hq))).contDiffWithinAt
  have hY : ContDiffOn ℝ ∞ (fun q => fderiv ℝ u q d) O :=
    (hu.fderiv_of_isOpen hO (by simp)).clm_apply contDiffOn_const
  have hsecond (v : P) := second_fderiv_metric_self hO hp hA hG hY hcompat hGsymm v
  have ht := covDerivAlong_tension_trace d e (hu.contDiffAt (hO.mem_nhds hp))
    (hΓ p hp) (Filter.Eventually.mono (hO.mem_nhds hp) fun q hq => hΓsymm q hq)
  have hpair := congrArg (fun v => G p v (fderiv ℝ u p d)) ht
  simp only [map_add, add_apply] at hpair
  change ∀ v : P,
    fderiv ℝ (fun q => fderiv ℝ
      (fun r => G r (fderiv ℝ u r d) (fderiv ℝ u r d)) q v) p v =
    2 * G p (covDerivAlong Γ u
      (covDerivAlong Γ u (fun r => fderiv ℝ u r d) v) v p) (fderiv ℝ u p d) +
    2 * G p (covDerivAlong Γ u (fun r => fderiv ℝ u r d) v p)
      (covDerivAlong Γ u (fun r => fderiv ℝ u r d) v p) at hsecond
  rw [hsecond d, hsecond e]
  linarith only [hpair]

theorem suLocalEnergyFlux_divergence
    {Γ : E → E →L[ℝ] E →L[ℝ] E} {u : P → E}
    {G : P → E →L[ℝ] E →L[ℝ] ℝ} {O : Set P} {p : P}
    (hO : IsOpen O) (hp : p ∈ O) (d e : P)
    (hu : ContDiffOn ℝ ∞ u O) (hG : ContDiffOn ℝ ∞ G O)
    (hΓ : ∀ q ∈ O, ContDiffAt ℝ ∞ Γ (u q))
    (hcompat : ∀ q ∈ O, ∀ v : P, ∀ b c : E,
      fderiv ℝ (fun r => G r b c) q v =
        G q (Γ (u q) (fderiv ℝ u q v) b) c +
          G q b (Γ (u q) (fderiv ℝ u q v) c))
    (hGsymm : ∀ b c : E, G p b c = G p c b)
    (hΓsymm : ∀ q ∈ O, ∀ b c, Γ (u q) b c = Γ (u q) c b) :
    let H := fun v w => covDerivAlong Γ u (fun r => fderiv ℝ u r v) w p
    let τ := localTension Γ u d e p
    fderiv ℝ (suLocalEnergyFlux Γ G u d e d) p d +
      fderiv ℝ (suLocalEnergyFlux Γ G u d e e) p e =
      2 * (G p (H d d) (H d d) + G p (H d e) (H d e) +
        G p (H e d) (H e d) + G p (H e e) (H e e)) +
      2 * (G p (christoffelCurvature Γ (u p) (fderiv ℝ u p e)
          (fderiv ℝ u p d) (fderiv ℝ u p e)) (fderiv ℝ u p d) +
        G p (christoffelCurvature Γ (u p) (fderiv ℝ u p d)
          (fderiv ℝ u p e) (fderiv ℝ u p d)) (fderiv ℝ u p e)) -
      2 * G p τ τ := by
  dsimp only
  let N : P → P → ℝ := fun v q => G q (fderiv ℝ u q v) (fderiv ℝ u q v)
  have hdu (v : P) {q : P} (hq : q ∈ O) :
      ContDiffAt ℝ ∞ (fun r => fderiv ℝ u r v) q :=
    ((hu.contDiffAt (hO.mem_nhds hq)).fderiv_right (by simp)).clm_apply contDiffAt_const
  have hN (v : P) {q : P} (hq : q ∈ O) : ContDiffAt ℝ ∞ (N v) q :=
    ((hG.contDiffAt (hO.mem_nhds hq)).clm_apply (hdu v hq)).clm_apply (hdu v hq)
  have henergy {q : P} (hq : q ∈ O) :
      ContDiffAt ℝ ∞ (suLocalSquaredDifferential G u d e) q := (hN d hq).add (hN e hq)
  have hsecond (v : P) :
      fderiv ℝ (fun q => fderiv ℝ (suLocalSquaredDifferential G u d e) q v) p v =
      fderiv ℝ (fun q => fderiv ℝ (N d) q v) p v +
        fderiv ℝ (fun q => fderiv ℝ (N e) q v) p v := by
    have heq : (fun q => fderiv ℝ (suLocalSquaredDifferential G u d e) q v) =ᶠ[𝓝 p]
        (fun q => fderiv ℝ (N d) q v + fderiv ℝ (N e) q v) := by
      filter_upwards [hO.mem_nhds hp] with q hq
      exact congrArg (fun L => L v)
        (fderiv_fun_add ((hN d hq).differentiableAt (by simp))
          ((hN e hq).differentiableAt (by simp)))
    have hdn (w : P) : DifferentiableAt ℝ (fun q => fderiv ℝ (N w) q v) p :=
      (((hN w hp).fderiv_right (m := ∞) (by simp)).clm_apply
        (contDiffAt_const (c := v))).differentiableAt (by simp)
    rw [heq.fderiv_eq, fderiv_fun_add (hdn d) (hdn e)]
    rfl
  have hτ := contDiffAt_localTension (hΓ p hp) (hu.contDiffAt (hO.mem_nhds hp)) d e
  have hpair (v : P) :
      fderiv ℝ (fun q => G q (localTension Γ u d e q) (fderiv ℝ u q v)) p v =
      G p (covDerivAlong Γ u (localTension Γ u d e) v p) (fderiv ℝ u p v) +
        G p (localTension Γ u d e p)
          (covDerivAlong Γ u (fun q => fderiv ℝ u q v) v p) := by
    exact Poincare.Riemannian.RadialTransport.fderiv_metric_pairing
      (Γ := mapConnectionCoefficients Γ u)
      ((hG.contDiffAt (hO.mem_nhds hp)).differentiableAt (by simp))
      (hτ.differentiableAt (by simp)) ((hdu v hp).differentiableAt (by simp))
      (hcompat p hp) v
  have hflux (v : P) : fderiv ℝ (suLocalEnergyFlux Γ G u d e v) p v =
      fderiv ℝ (fun q => fderiv ℝ (N d) q v) p v +
      fderiv ℝ (fun q => fderiv ℝ (N e) q v) p v -
      2 * (G p (covDerivAlong Γ u (localTension Γ u d e) v p) (fderiv ℝ u p v) +
        G p (localTension Γ u d e p)
          (covDerivAlong Γ u (fun q => fderiv ℝ u q v) v p)) := by
    have hs := (((henergy hp).fderiv_right (m := ∞) (by simp)).clm_apply
      (contDiffAt_const (c := v))).differentiableAt (by simp)
    have ht := (((hG.contDiffAt (hO.mem_nhds hp)).clm_apply hτ).clm_apply
      (hdu v hp)).differentiableAt (by simp)
    have htt : DifferentiableAt ℝ
        (fun q => 2 * G q (localTension Γ u d e q) (fderiv ℝ u q v)) p :=
      (differentiableAt_const (2 : ℝ)).mul ht
    unfold suLocalEnergyFlux
    rw [fderiv_fun_sub hs htt, fderiv_const_mul ht]
    simp only [sub_apply, smul_apply, smul_eq_mul]
    rw [hsecond, hpair]
  have hswap : localTension Γ u e d = localTension Γ u d e := by
    funext q
    simp only [localTension, add_comm]
  have hcd := metric_column_laplacian hO hp d e hu hG hΓ hcompat hGsymm hΓsymm
  have hce := metric_column_laplacian hO hp e d hu hG hΓ hcompat hGsymm hΓsymm
  rw [hswap] at hce
  have hsum :
      G p (localTension Γ u d e p)
        (covDerivAlong Γ u (fun q => fderiv ℝ u q d) d p) +
      G p (localTension Γ u d e p)
        (covDerivAlong Γ u (fun q => fderiv ℝ u q e) e p) =
      G p (localTension Γ u d e p) (localTension Γ u d e p) := by
    rw [← map_add]
    rfl
  rw [hflux d, hflux e]
  dsimp only [N]
  linarith only [hcd, hce, hsum]

theorem suMetricPair_cauchy_schwarz
    (G : E →L[ℝ] E →L[ℝ] ℝ)
    (hG : ∀ v : E, 0 ≤ G v v) (hsym : ∀ v w : E, G v w = G w v)
    (a b v w : E) :
    (G a v + G b w) ^ 2 ≤ (G a a + G b b) * (G v v + G w w) := by
  have hpoly (t : ℝ) : 0 ≤ (G a a + G b b) * (t * t) +
      (2 * (G a v + G b w)) * t + (G v v + G w w) := by
    have h := add_nonneg (hG (t • a + v)) (hG (t • b + w))
    simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul] at h
    rw [hsym v a, hsym w b] at h
    nlinarith only [h]
  have h := discrim_le_zero hpoly
  unfold discrim at h
  nlinarith only [h]

theorem suLocalSquaredDifferential_fderiv
    {Γ : E → E →L[ℝ] E →L[ℝ] E} {u : P → E}
    {G : P → E →L[ℝ] E →L[ℝ] ℝ} {p : P} (d e v : P)
    (hu : ContDiffAt ℝ ∞ u p) (hG : DifferentiableAt ℝ G p)
    (hcompat : ∀ w : P, ∀ b c : E,
      fderiv ℝ (fun r => G r b c) p w =
        G p (Γ (u p) (fderiv ℝ u p w) b) c +
          G p b (Γ (u p) (fderiv ℝ u p w) c))
    (hsym : ∀ b c : E, G p b c = G p c b) :
    fderiv ℝ (suLocalSquaredDifferential G u d e) p v =
      2 * (G p (fderiv ℝ u p d)
        (covDerivAlong Γ u (fun q => fderiv ℝ u q d) v p) +
        G p (fderiv ℝ u p e)
          (covDerivAlong Γ u (fun q => fderiv ℝ u q e) v p)) := by
  have hdu (w : P) : DifferentiableAt ℝ (fun q => fderiv ℝ u q w) p :=
    ((hu.fderiv_right (m := ∞) (by simp)).clm_apply
      (contDiffAt_const (c := w))).differentiableAt (by simp)
  have hcol (w : P) := Poincare.Riemannian.RadialTransport.fderiv_metric_pairing
    (Γ := mapConnectionCoefficients Γ u) hG (hdu w) (hdu w) hcompat v
  unfold suLocalSquaredDifferential
  rw [fderiv_fun_add ((hG.clm_apply (hdu d)).clm_apply (hdu d))
    ((hG.clm_apply (hdu e)).clm_apply (hdu e))]
  simp only [add_apply]
  rw [hcol d, hcol e]
  change G p (covDerivAlong Γ u (fun q => fderiv ℝ u q d) v p) (fderiv ℝ u p d) +
      G p (fderiv ℝ u p d) (covDerivAlong Γ u (fun q => fderiv ℝ u q d) v p) +
      (G p (covDerivAlong Γ u (fun q => fderiv ℝ u q e) v p) (fderiv ℝ u p e) +
      G p (fderiv ℝ u p e) (covDerivAlong Γ u (fun q => fderiv ℝ u q e) v p)) = _
  rw [hsym (covDerivAlong Γ u (fun q => fderiv ℝ u q d) v p),
    hsym (covDerivAlong Γ u (fun q => fderiv ℝ u q e) v p)]
  ring

theorem suConformalAlpha_absorption
    (G : E →L[ℝ] E →L[ℝ] ℝ) (a b τ : E)
    (hG : ∀ v : E, 0 ≤ G v v) (hsym : ∀ v w : E, G v w = G w v)
    {lambda q H X Y x y l₀ l₁ rho c : ℝ}
    (hlambda : 1 / 4 ≤ lambda) (hlambda' : lambda ≤ 4) (hq : 0 ≤ q) (hH : 0 ≤ H)
    (htrace : G a a + G b b = lambda * q)
    (hgrad : X ^ 2 + Y ^ 2 ≤ 4 * lambda * q * H)
    (hx : lambda * x = X - q * l₀) (hy : lambda * y = Y - q * l₁)
    (hl : l₀ ^ 2 + l₁ ^ 2 ≤ 256) (hrho : 0 < rho)
    (hc : 0 ≤ c) (hc' : c ≤ 1 / 32)
    (hτ : τ = -(c / (rho ^ 2 + q)) • (x • a + y • b)) :
    2 * G τ τ + (2 * (l₀ * x + l₁ * y) +
      2 * c / (lambda * (rho ^ 2 + q)) *
        G (l₀ • a + l₁ • b) (x • a + y • b)) ≤ 2 * H + 41000 * q := by
  let s := rho ^ 2 + q
  let V := x ^ 2 + y ^ 2
  let L := l₀ ^ 2 + l₁ ^ 2
  have hlambdap : 0 < lambda := by linarith
  have hs : 0 < s := by dsimp only [s]; positivity
  have hqs : q ≤ s := by dsimp only [s]; nlinarith only [sq_nonneg rho]
  have hVs : 0 ≤ V := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hLs : 0 ≤ L := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hc2 : c ^ 2 ≤ 1 / 1024 := by nlinarith only [hc, hc']
  have hv : V ≤ 32 * q * H + 8192 * q ^ 2 := by
    have hx2 := congrArg (fun t : ℝ => t ^ 2) hx
    have hy2 := congrArg (fun t : ℝ => t ^ 2) hy
    have hfirst : lambda ^ 2 * V ≤ 2 * (X ^ 2 + Y ^ 2) + 2 * q ^ 2 * L := by
      dsimp only [V, L]
      nlinarith only [hx2, hy2, sq_nonneg (X + q * l₀), sq_nonneg (Y + q * l₁)]
    have hsecond := mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ 2 * q ^ 2)
    have hthird := mul_le_mul_of_nonneg_right
      (show 8 * lambda ≤ 32 * lambda ^ 2 by nlinarith only [hlambda]) (mul_nonneg hq hH)
    have hfourth := mul_le_mul_of_nonneg_right
      (show (512 : ℝ) ≤ 8192 * lambda ^ 2 by nlinarith only [hlambda]) (sq_nonneg q)
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hlambdap)).mp
    dsimp only [L] at hfirst
    nlinarith only [hfirst, hsecond, hthird, hfourth, hgrad]
  have hgram (v w : ℝ) : G (v • a + w • b) (v • a + w • b) ≤
      lambda * q * (v ^ 2 + w ^ 2) := by
    have h := hG (w • a - v • b)
    rw [← htrace]
    simp only [map_add, map_sub, map_smul, add_apply, sub_apply, smul_apply,
      smul_eq_mul] at h ⊢
    rw [hsym b a] at h ⊢
    nlinarith only [h]
  have hτeq : s ^ 2 * G τ τ = c ^ 2 * G (x • a + y • b) (x • a + y • b) := by
    rw [hτ]
    simp only [map_smul, smul_apply, smul_eq_mul]
    change s ^ 2 * (-(c / s) * (-(c / s) * _)) = _
    field_simp
  have hτbound : G τ τ ≤ H / 8 + 32 * q := by
    have h0 := mul_le_mul_of_nonneg_left (hgram x y) (sq_nonneg c)
    have h1 := mul_le_mul_of_nonneg_left hv
      (mul_nonneg (sq_nonneg c) (mul_nonneg hlambdap.le hq))
    have hsq := mul_self_le_mul_self hq hqs
    have h2 := mul_le_mul_of_nonneg_right hsq
      (mul_nonneg (mul_nonneg (sq_nonneg c) hlambdap.le) (by positivity : 0 ≤ 32 * H + 8192 * q))
    have h3 := mul_le_mul_of_nonneg_left hlambda'
      (mul_nonneg (sq_nonneg c) (mul_nonneg (sq_nonneg s)
        (by positivity : 0 ≤ 32 * H + 8192 * q)))
    have h4 := mul_le_mul_of_nonneg_right hc2
      (by positivity : 0 ≤ 4 * s ^ 2 * (32 * H + 8192 * q))
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hs)).mp
    dsimp only [V] at h1
    nlinarith only [hτeq, h0, h1, h2, h3, h4]
  let z := 2 * c / (lambda * s) * G (l₀ • a + l₁ • b) (x • a + y • b)
  have hz : z ^ 2 ≤ L * V := by
    have hcs := suMetricPair_cauchy_schwarz G hG hsym
      (l₀ • a + l₁ • b) 0 (x • a + y • b) 0
    simp only [map_zero, add_zero] at hcs
    have hprod := mul_le_mul (hgram l₀ l₁) (hgram x y) (hG _)
      (mul_nonneg (mul_nonneg hlambdap.le hq) hLs)
    have h := mul_le_mul_of_nonneg_left (hcs.trans hprod)
      (sq_nonneg (2 * c / (lambda * s)))
    have heq : (2 * c / (lambda * s)) ^ 2 *
        ((lambda * q * L) * (lambda * q * V)) = (4 * c ^ 2 * q ^ 2 / s ^ 2) * (L * V) := by
      field_simp; ring
    have hfactor : 4 * c ^ 2 * q ^ 2 / s ^ 2 ≤ 1 := by
      apply (div_le_iff₀ (sq_pos_of_pos hs)).mpr
      have hsq := mul_self_le_mul_self hq hqs
      have hh := mul_le_mul_of_nonneg_right
        (show 4 * c ^ 2 ≤ 1 by linarith only [hc2]) (sq_nonneg q)
      nlinarith only [hsq, hh]
    have hlast := mul_le_mul_of_nonneg_right hfactor (mul_nonneg hLs hVs)
    change _ ≤ (2 * c / (lambda * s)) ^ 2 * ((lambda * q * L) * (lambda * q * V)) at h
    rw [heq] at h
    dsimp only [z]
    nlinarith only [h, hlast]
  have hdot : (l₀ * x + l₁ * y) ^ 2 ≤ L * V := by
    dsimp only [L, V]
    nlinarith only [sq_nonneg (l₀ * y - l₁ * x)]
  have hcross : 2 * (l₀ * x + l₁ * y) + z ≤ H + 40000 * q := by
    have hsq : (2 * (l₀ * x + l₁ * y) + z) ^ 2 ≤ 9 * L * V := by
      nlinarith only [hdot, hz, sq_nonneg (l₀ * x + l₁ * y - z)]
    have hL := mul_le_mul_of_nonneg_right hl (by positivity : 0 ≤ 9 * V)
    have hV := mul_le_mul_of_nonneg_left hv (by norm_num : (0 : ℝ) ≤ 2304)
    have hqH := mul_nonneg hq hH
    have hbound : (2 * (l₀ * x + l₁ * y) + z) ^ 2 ≤ (H + 40000 * q) ^ 2 := by
      dsimp only [L] at hsq
      nlinarith only [hsq, hL, hV, hqH, sq_nonneg H, sq_nonneg q]
    exact le_of_sq_le_sq hbound (by positivity)
  change 2 * G τ τ + (2 * (l₀ * x + l₁ * y) + z) ≤ _
  nlinarith only [hτbound, hcross, hH, hq]

end PoincareConjecture.M60
