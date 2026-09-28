import PoincareConjecture.Proofs.M60.Def18_17_FillingArea.LoopCollar
import PoincareConjecture.Proofs.M58.Cor18_28_PolarDerivatives










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

open Proofs.M58

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]



theorem m60LoopCollar_polar (C : ℝ × (M × M) → M)
    (γ₀ γ₁ : C1FreeLoopSpace (M := M)) {r : ℝ} (hr : 0 < r) (t : ℝ) :
    m60LoopCollar C γ₀ γ₁ (r • angularPoint t) =
      C (1 - diskTimeProfile r, periodicFreeLoop γ₁ t, periodicFreeLoop γ₀ t) := by
  have hnorm : ‖r • angularPoint t‖ = r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, norm_angularPoint, mul_one]
  have hrad : radialNormalization (r • angularPoint t) = angularPoint t := by
    rw [radialNormalization, hnorm, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
  rw [m60LoopCollar, hnorm, hrad]
  rfl



theorem m60LoopCollar_mfderiv_radial (C : ℝ × (M × M) → M)
    (γ₀ γ₁ : C1FreeLoopSpace (M := M)) {r : ℝ} (hr : 0 < r) (t : ℝ)
    (hF : MDifferentiableAt (𝓡 2) (𝓡 3) (m60LoopCollar C γ₀ γ₁) (r • angularPoint t))
    (hC : MDifferentiableAt (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) C
      (1 - diskTimeProfile r, periodicFreeLoop γ₁ t, periodicFreeLoop γ₀ t)) :
    mfderiv (𝓡 2) (𝓡 3) (m60LoopCollar C γ₀ γ₁) (r • angularPoint t) (angularPoint t) =
      -deriv diskTimeProfile r •
        mfderiv (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) C
          (1 - diskTimeProfile r, periodicFreeLoop γ₁ t, periodicFreeLoop γ₀ t)
          (1, 0, 0) := by
  let δ : ℝ → LoopPlane := fun s => s • angularPoint t
  have hδ : HasDerivAt δ (angularPoint t) r := by
    simpa +instances only [one_smul] using! (hasDerivAt_id r).smul_const (angularPoint t)
  have hδM := hδ.differentiableAt.mdifferentiableAt
  have hδv : mfderiv 𝓘(ℝ, ℝ) (𝓡 2) δ r 1 = angularPoint t := by
    simpa +instances only [mfderiv_eq_fderiv, fderiv_apply_one_eq_deriv] using! hδ.deriv
  let χ := fun s => 1 - diskTimeProfile s
  have hχd : HasDerivAt χ (-deriv diskTimeProfile r) r := by
    simpa +instances only [zero_sub] using! (hasDerivAt_const r (1 : ℝ)).sub
      (contDiff_diskTimeProfile.differentiable (by norm_num) r).hasDerivAt
  have hχ := hχd.differentiableAt.mdifferentiableAt
  have hi : MDifferentiableAt 𝓘(ℝ, ℝ)
      (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3)))
      (fun s => (χ s, periodicFreeLoop γ₁ t, periodicFreeLoop γ₀ t)) r :=
    hχ.prodMk (mdifferentiableAt_const.prodMk mdifferentiableAt_const)
  have heq : m60LoopCollar C γ₀ γ₁ ∘ δ =ᶠ[𝓝 r]
      (fun s => C (χ s, periodicFreeLoop γ₁ t, periodicFreeLoop γ₀ t)) := by
    filter_upwards [Ioi_mem_nhds hr] with s hs
    exact m60LoopCollar_polar C γ₀ γ₁ hs t
  have hd := congrArg (fun D => D (1 : ℝ))
    (heq.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := 𝓡 3))
  erw [mfderiv_comp_apply r hF hδM, hδv] at hd
  have hc := mfderiv_comp_apply_of_eq r hC hi rfl (1 : ℝ)
  erw [mfderiv_prodMk hχ (mdifferentiableAt_const.prodMk mdifferentiableAt_const),
    mfderiv_prodMk mdifferentiableAt_const mdifferentiableAt_const] at hc
  simp only [mfderiv_const] at hc
  have hχv : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) χ r 1 = -deriv diskTimeProfile r := by
    simpa +instances only [mfderiv_eq_fderiv, fderiv_apply_one_eq_deriv] using! hχd.deriv
  change mfderiv 𝓘(ℝ, ℝ) (𝓡 3)
      (fun s => C (χ s, periodicFreeLoop γ₁ t, periodicFreeLoop γ₀ t)) r 1 =
    mfderiv (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) C
      (χ r, periodicFreeLoop γ₁ t, periodicFreeLoop γ₀ t)
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) χ r 1, 0, 0) at hc
  rw [hχv] at hc
  apply hd.trans (hc.trans ?_)
  have hv : (-deriv diskTimeProfile r, 0, 0) = -deriv diskTimeProfile r •
      ((1, 0, 0) : ℝ × (LoopAmbient × LoopAmbient)) := by simp
  erw [hv, map_smul]



theorem m60LoopCollar_mfderiv_angular (C : ℝ × (M × M) → M)
    (γ₀ γ₁ : C1FreeLoopSpace (M := M)) {r : ℝ} (hr : 0 < r) (t : ℝ)
    (hF : MDifferentiableAt (𝓡 2) (𝓡 3) (m60LoopCollar C γ₀ γ₁) (r • angularPoint t))
    (hC : MDifferentiableAt (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) C
      (1 - diskTimeProfile r, periodicFreeLoop γ₁ t, periodicFreeLoop γ₀ t)) :
    mfderiv (𝓡 2) (𝓡 3) (m60LoopCollar C γ₀ γ₁) (r • angularPoint t)
        (r • angularVector t) =
      mfderiv (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) C
        (1 - diskTimeProfile r, periodicFreeLoop γ₁ t, periodicFreeLoop γ₀ t)
        (0, curveVelocity (periodicFreeLoop γ₁) t, curveVelocity (periodicFreeLoop γ₀) t) := by
  let δ : ℝ → LoopPlane := fun s => r • angularPoint s
  have hδ : HasDerivAt δ (r • angularVector t) t := (hasDerivAt_angularPoint t).const_smul r
  have hδM := hδ.differentiableAt.mdifferentiableAt
  have hδv : mfderiv 𝓘(ℝ, ℝ) (𝓡 2) δ t 1 = r • angularVector t := by
    simpa +instances only [mfderiv_eq_fderiv, fderiv_apply_one_eq_deriv] using! hδ.deriv
  have hγ₀ := (contMDiff_periodicFreeLoop γ₀ t).mdifferentiableAt one_ne_zero
  have hγ₁ := (contMDiff_periodicFreeLoop γ₁ t).mdifferentiableAt one_ne_zero
  have hi : MDifferentiableAt 𝓘(ℝ, ℝ)
      (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3)))
      (fun s => (1 - diskTimeProfile r, periodicFreeLoop γ₁ s, periodicFreeLoop γ₀ s)) t :=
    mdifferentiableAt_const.prodMk (hγ₁.prodMk hγ₀)
  have heq : m60LoopCollar C γ₀ γ₁ ∘ δ =
      (fun s => C (1 - diskTimeProfile r, periodicFreeLoop γ₁ s, periodicFreeLoop γ₀ s)) :=
    funext (m60LoopCollar_polar C γ₀ γ₁ hr)
  have hd := mfderiv_comp_apply t hF hδM (1 : ℝ)
  erw [heq, hδv] at hd
  have hc := mfderiv_comp_apply_of_eq t hC hi rfl (1 : ℝ)
  erw [mfderiv_prodMk mdifferentiableAt_const (hγ₁.prodMk hγ₀),
    mfderiv_prodMk hγ₁ hγ₀] at hc
  simp only [mfderiv_const] at hc
  exact hd.symm.trans hc

end PoincareConjecture
