import Mathlib.Geometry.Manifold.Diffeomorph
import PoincareConjecture.Definitions.Ch01.RiemannianMetric

set_option autoImplicit false

open scoped Manifold ContDiff

noncomputable section

universe u

namespace PoincareConjecture.ConjugatingFlowNative

variable {n : ℕ} {M : Type u}
  [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

local notation "I" => 𝓡 n

def diffeomorphOfSmoothInverse
    {f g : M → M}
    (hf : ContMDiff I I ∞ f) (hg : ContMDiff I I ∞ g)
    (hgf : ∀ x, g (f x) = x) (hfg : ∀ x, f (g x) = x) :
    Diffeomorph I I M M ∞ where
  toEquiv :=
    { toFun := f
      invFun := g
      left_inv := hgf
      right_inv := hfg }
  contMDiff_toFun := hf
  contMDiff_invFun := hg

@[simp] theorem diffeomorphOfSmoothInverse_apply
    {f g : M → M}
    (hf : ContMDiff I I ∞ f) (hg : ContMDiff I I ∞ g)
    (hgf : ∀ x, g (f x) = x) (hfg : ∀ x, f (g x) = x) (x : M) :
    diffeomorphOfSmoothInverse hf hg hgf hfg x = f x := rfl

@[simp] theorem diffeomorphOfSmoothInverse_symm_apply
    {f g : M → M}
    (hf : ContMDiff I I ∞ f) (hg : ContMDiff I I ∞ g)
    (hgf : ∀ x, g (f x) = x) (hfg : ∀ x, f (g x) = x) (x : M) :
    (diffeomorphOfSmoothInverse hf hg hgf hfg).symm x = g x := rfl

private theorem smooth_slice
    {F : ℝ → M → M}
    (hF : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞
      (fun p : ℝ × M => F p.1 p.2)) (t : ℝ) :
    ContMDiff I I ∞ (F t) := by
  intro x
  have hpair : ContMDiffAt I (𝓘(ℝ, ℝ).prod I) ∞
      (fun y : M => ((t, y) : ℝ × M)) x :=
    contMDiffAt_const.prodMk contMDiffAt_id
  have hcomp := (hF (t, x)).comp x hpair
  simpa only [Function.comp_def] using hcomp

def diffeomorphFamily
    {Φ Ψ : ℝ → M → M}
    (hΦ : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞
      (fun p : ℝ × M => Φ p.1 p.2))
    (hΨ : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞
      (fun p : ℝ × M => Ψ p.1 p.2))
    (hΨΦ : ∀ (t : ℝ) (x : M), Ψ t (Φ t x) = x)
    (hΦΨ : ∀ (t : ℝ) (x : M), Φ t (Ψ t x) = x) :
    ℝ → Diffeomorph I I M M ∞ := fun t =>
  diffeomorphOfSmoothInverse (smooth_slice hΦ t) (smooth_slice hΨ t)
    (hΨΦ t) (hΦΨ t)

@[simp] theorem diffeomorphFamily_apply
    {Φ Ψ : ℝ → M → M}
    (hΦ : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞
      (fun p : ℝ × M => Φ p.1 p.2))
    (hΨ : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞
      (fun p : ℝ × M => Ψ p.1 p.2))
    (hΨΦ : ∀ (t : ℝ) (x : M), Ψ t (Φ t x) = x)
    (hΦΨ : ∀ (t : ℝ) (x : M), Φ t (Ψ t x) = x)
    (t : ℝ) (x : M) :
    diffeomorphFamily hΦ hΨ hΨΦ hΦΨ t x = Φ t x := rfl

@[simp] theorem diffeomorphFamily_symm_apply
    {Φ Ψ : ℝ → M → M}
    (hΦ : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞
      (fun p : ℝ × M => Φ p.1 p.2))
    (hΨ : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞
      (fun p : ℝ × M => Ψ p.1 p.2))
    (hΨΦ : ∀ (t : ℝ) (x : M), Ψ t (Φ t x) = x)
    (hΦΨ : ∀ (t : ℝ) (x : M), Φ t (Ψ t x) = x)
    (t : ℝ) (x : M) :
    (diffeomorphFamily hΦ hΨ hΨΦ hΦΨ t).symm x = Ψ t x := rfl

theorem diffeomorphFamily_zero
    {Φ Ψ : ℝ → M → M}
    (hΦ : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞
      (fun p : ℝ × M => Φ p.1 p.2))
    (hΨ : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞
      (fun p : ℝ × M => Ψ p.1 p.2))
    (hΨΦ : ∀ (t : ℝ) (x : M), Ψ t (Φ t x) = x)
    (hΦΨ : ∀ (t : ℝ) (x : M), Φ t (Ψ t x) = x)
    (h0 : ∀ x, Φ 0 x = x) :
    diffeomorphFamily hΦ hΨ hΨΦ hΦΨ 0 = Diffeomorph.refl I M ∞ := by
  apply Diffeomorph.ext
  intro x
  simp [h0 x]

end PoincareConjecture.ConjugatingFlowNative

end
