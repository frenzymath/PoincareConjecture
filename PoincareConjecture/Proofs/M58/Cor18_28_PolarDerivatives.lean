import PoincareConjecture.Proofs.M58.Cor18_28_DiskExtension










set_option autoImplicit false

open Set Filter Real
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Proofs.M58



noncomputable def angularVector (t : ℝ) : LoopPlane := !₂[-sin t, cos t]



theorem hasDerivAt_angularPoint (t : ℝ) : HasDerivAt angularPoint (angularVector t) t := by
  have h : HasDerivAt (fun s : ℝ => ![cos s, sin s]) ![-sin t, cos t] t := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact hasDerivAt_cos t
    · exact hasDerivAt_sin t
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm.toContinuousLinearMap.hasFDerivAt
    |>.comp_hasDerivAt t h

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]



theorem contractionDiskMap_polar (C : ℝ × (M × M) → M)
    (p : M) (γ : C1FreeLoopSpace (M := M)) {r : ℝ} (hr : 0 < r) (t : ℝ) :
    contractionDiskMap C p γ (r • angularPoint t) =
      C (diskTimeProfile r, p, periodicFreeLoop γ t) := by
  have hnorm : ‖r • angularPoint t‖ = r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, norm_angularPoint, mul_one]
  have hz : r • angularPoint t ≠ 0 := by
    intro h
    rw [h, norm_zero] at hnorm
    exact hr.ne' hnorm.symm
  have hrad : radialNormalization (r • angularPoint t) = angularPoint t := by
    rw [radialNormalization, hnorm, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
  rw [contractionDiskMap, if_neg hz, hnorm, hrad]
  rfl



theorem mfderiv_contractionDiskMap_radial (C : ℝ × (M × M) → M)
    (p : M) (γ : C1FreeLoopSpace (M := M)) {r : ℝ} (hr : 0 < r) (t : ℝ)
    (hF : MDifferentiableAt (𝓡 2) (𝓡 3) (contractionDiskMap C p γ) (r • angularPoint t))
    (hC : MDifferentiableAt (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) C
      (diskTimeProfile r, p, periodicFreeLoop γ t)) :
    mfderiv (𝓡 2) (𝓡 3) (contractionDiskMap C p γ) (r • angularPoint t) (angularPoint t) =
      deriv diskTimeProfile r •
        mfderiv (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) C
          (diskTimeProfile r, p, periodicFreeLoop γ t) (1, 0, 0) := by
  let δ : ℝ → LoopPlane := fun s => s • angularPoint t
  have hδ : HasDerivAt δ (angularPoint t) r := by
    simpa +instances only [one_smul] using! (hasDerivAt_id r).smul_const (angularPoint t)
  have hδM : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 2) δ r :=
    hδ.differentiableAt.mdifferentiableAt
  have hδv : mfderiv 𝓘(ℝ, ℝ) (𝓡 2) δ r 1 = angularPoint t := by
    simpa +instances only [mfderiv_eq_fderiv, fderiv_apply_one_eq_deriv] using! hδ.deriv
  have hχ : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) diskTimeProfile r :=
    contDiff_diskTimeProfile.contMDiff.mdifferentiableAt (by simp)
  have hinput : MDifferentiableAt 𝓘(ℝ, ℝ)
      (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3)))
      (fun s => (diskTimeProfile s, p, periodicFreeLoop γ t)) r :=
    hχ.prodMk (mdifferentiableAt_const.prodMk mdifferentiableAt_const)
  have heq : (contractionDiskMap C p γ ∘ δ) =ᶠ[𝓝 r]
      (fun s => C (diskTimeProfile s, p, periodicFreeLoop γ t)) := by
    filter_upwards [Ioi_mem_nhds hr] with s hs
    exact contractionDiskMap_polar C p γ hs t
  have hderiv := congrArg (fun D => D (1 : ℝ))
    (heq.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := 𝓡 3))
  erw [mfderiv_comp_apply r hF hδM, hδv] at hderiv
  have hchain := mfderiv_comp_apply_of_eq r hC hinput rfl (1 : ℝ)
  erw [mfderiv_prodMk hχ (mdifferentiableAt_const.prodMk mdifferentiableAt_const),
    mfderiv_prodMk mdifferentiableAt_const mdifferentiableAt_const] at hchain
  simp only [mfderiv_const] at hchain
  change mfderiv 𝓘(ℝ, ℝ) (𝓡 3)
      (fun s => C (diskTimeProfile s, p, periodicFreeLoop γ t)) r 1 =
    mfderiv (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) C
      (diskTimeProfile r, p, periodicFreeLoop γ t)
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) diskTimeProfile r 1, 0, 0) at hchain
  have hχv : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) diskTimeProfile r 1 = deriv diskTimeProfile r := by
    simpa +instances only [mfderiv_eq_fderiv] using!
      (fderiv_apply_one_eq_deriv : fderiv ℝ diskTimeProfile r 1 = deriv diskTimeProfile r)
  erw [hχv] at hchain
  apply hderiv.trans (hchain.trans ?_)
  have hv : (deriv diskTimeProfile r, 0, 0) = deriv diskTimeProfile r •
      ((1, 0, 0) : ℝ × (LoopAmbient × LoopAmbient)) := by simp
  erw [hv, map_smul]



theorem mfderiv_contractionDiskMap_angular (C : ℝ × (M × M) → M)
    (p : M) (γ : C1FreeLoopSpace (M := M)) {r : ℝ} (hr : 0 < r) (t : ℝ)
    (hF : MDifferentiableAt (𝓡 2) (𝓡 3) (contractionDiskMap C p γ) (r • angularPoint t))
    (hC : MDifferentiableAt (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) C
      (diskTimeProfile r, p, periodicFreeLoop γ t)) :
    mfderiv (𝓡 2) (𝓡 3) (contractionDiskMap C p γ) (r • angularPoint t)
        (r • angularVector t) =
      mfderiv (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) C
        (diskTimeProfile r, p, periodicFreeLoop γ t)
        (0, 0, curveVelocity (periodicFreeLoop γ) t) := by
  let δ : ℝ → LoopPlane := fun s => r • angularPoint s
  have hδ : HasDerivAt δ (r • angularVector t) t := (hasDerivAt_angularPoint t).const_smul r
  have hδM : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 2) δ t :=
    hδ.differentiableAt.mdifferentiableAt
  have hδv : mfderiv 𝓘(ℝ, ℝ) (𝓡 2) δ t 1 = r • angularVector t := by
    simpa +instances only [mfderiv_eq_fderiv, fderiv_apply_one_eq_deriv] using! hδ.deriv
  have hγ : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 3) (periodicFreeLoop γ) t :=
    (contMDiff_periodicFreeLoop γ t).mdifferentiableAt one_ne_zero
  have hinput : MDifferentiableAt 𝓘(ℝ, ℝ)
      (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3)))
      (fun s => (diskTimeProfile r, p, periodicFreeLoop γ s)) t :=
    mdifferentiableAt_const.prodMk (mdifferentiableAt_const.prodMk hγ)
  have heq : contractionDiskMap C p γ ∘ δ =
      (fun s => C (diskTimeProfile r, p, periodicFreeLoop γ s)) :=
    funext (contractionDiskMap_polar C p γ hr)
  have hderiv := mfderiv_comp_apply t hF hδM (1 : ℝ)
  erw [heq, hδv] at hderiv
  have hchain := mfderiv_comp_apply_of_eq t hC hinput rfl (1 : ℝ)
  erw [mfderiv_prodMk mdifferentiableAt_const (mdifferentiableAt_const.prodMk hγ),
    mfderiv_prodMk mdifferentiableAt_const hγ] at hchain
  simp only [mfderiv_const] at hchain
  exact hderiv.symm.trans hchain

end PoincareConjecture.Proofs.M58
