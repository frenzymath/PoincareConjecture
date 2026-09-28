import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Basic
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Linearity
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Divergence.Regularity
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Regularity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

namespace LeviCivitaData

noncomputable def spatialDrift (D : LeviCivitaData g) (f h : M → ℝ) (x : M) : ℝ :=
  D.laplacian h x - 2 * mvfderiv (𝓡 n) h x (D.gradient f x)

theorem spatialDrift_add (D : LeviCivitaData g) (f : M → ℝ)
    {h k : M → ℝ} (hh : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ h)
    (hk : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ k) (x : M) :
    D.spatialDrift f (fun y ↦ h y + k y) x =
      D.spatialDrift f h x + D.spatialDrift f k x := by
  rw [spatialDrift, D.laplacian_add hh hk,
    mvfderiv_fun_add ((hh x).mdifferentiableAt (by simp))
      ((hk x).mdifferentiableAt (by simp))]
  simp only [spatialDrift, add_apply]
  ring

theorem spatialDrift_sub (D : LeviCivitaData g) (f : M → ℝ)
    {h k : M → ℝ} (hh : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ h)
    (hk : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ k) (x : M) :
    D.spatialDrift f (fun y ↦ h y - k y) x =
      D.spatialDrift f h x - D.spatialDrift f k x := by
  rw [spatialDrift, D.laplacian_sub hh hk,
    mvfderiv_fun_sub ((hh x).mdifferentiableAt (by simp))
      ((hk x).mdifferentiableAt (by simp))]
  simp only [spatialDrift, sub_apply]
  ring

theorem spatialDrift_const_mul (D : LeviCivitaData g) (f h : M → ℝ)
    (c : ℝ) (x : M) :
    D.spatialDrift f (fun y ↦ c * h y) x = c * D.spatialDrift f h x := by
  rw [spatialDrift, D.laplacian_const_mul, mvfderiv_const_mul, spatialDrift]
  ring

@[simp] theorem spatialDrift_const (D : LeviCivitaData g) (f : M → ℝ)
    (c : ℝ) (x : M) : D.spatialDrift f (fun _ ↦ c) x = 0 := by
  simp [spatialDrift, laplacian, hessian, hessianOnFields, mvfderiv_const]

end LeviCivitaData

namespace RicciFlow

variable {J : Set ℝ}

noncomputable def entropyFactor (F : RicciFlow n M J)
    (f : M × ℝ → ℝ) (t : ℝ) (x : M) : ℝ :=
  -t * (2 * (F.connection t).laplacian (fun y ↦ f (y, t)) x -
      (F.metric t).inner x ((F.connection t).gradient (fun y ↦ f (y, t)) x)
        ((F.connection t).gradient (fun y ↦ f (y, t)) x) +
      (F.connection t).scalarCurvature x) + f (x, t) - n

theorem contMDiff_entropyFactor (F : RicciFlow n M J)
    {f : M × ℝ → ℝ} {t : ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y ↦ f (y, t))) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (F.entropyFactor f t) :=
  ((contMDiff_const.mul (((contMDiff_const.mul
    ((F.connection t).contMDiff_laplacian hf)).sub
      ((F.connection t).contMDiff_inner_gradient hf hf)).add
        (F.connection t).contMDiff_scalarCurvature)).add hf).sub contMDiff_const

theorem spatialDrift_entropyFactor (F : RicciFlow n M J)
    {f : M × ℝ → ℝ} {t : ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y ↦ f (y, t))) (x : M) :
    let D := F.connection t
    let φ := fun y ↦ f (y, t)
    D.spatialDrift φ (F.entropyFactor f t) x =
      -t * (2 * D.spatialDrift φ (D.laplacian φ) x -
        D.spatialDrift φ (fun y ↦ (F.metric t).inner y (D.gradient φ y)
          (D.gradient φ y)) x + D.spatialDrift φ D.scalarCurvature x) +
      D.spatialDrift φ φ x := by
  let D := F.connection t
  let φ := fun y ↦ f (y, t)
  let L := D.laplacian φ
  let N := fun y ↦ (F.metric t).inner y (D.gradient φ y) (D.gradient φ y)
  let R := D.scalarCurvature
  have hL : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ L := D.contMDiff_laplacian hf
  have hN : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ N := D.contMDiff_inner_gradient hf hf
  have hR : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ R := D.contMDiff_scalarCurvature
  have hA : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y ↦ 2 * L y - N y + R y) :=
    ((contMDiff_const.mul hL).sub hN).add hR
  have hB : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun y ↦ -t * (2 * L y - N y + R y) + φ y) :=
    (contMDiff_const.mul hA).add hf
  have hT : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun y ↦ -t * (2 * L y - N y + R y)) := contMDiff_const.mul hA
  have h2L : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y ↦ 2 * L y) :=
    contMDiff_const.mul hL
  have h2LN : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y ↦ 2 * L y - N y) :=
    h2L.sub hN
  change D.spatialDrift φ (fun y ↦ -t * (2 * L y - N y + R y) + φ y - (n : ℝ)) x = _
  rw [D.spatialDrift_sub φ hB contMDiff_const, D.spatialDrift_const, sub_zero,
    D.spatialDrift_add φ hT hf, D.spatialDrift_const_mul,
    D.spatialDrift_add φ h2LN hR, D.spatialDrift_sub φ h2L hN,
    D.spatialDrift_const_mul]

end RicciFlow

end PoincareConjecture
