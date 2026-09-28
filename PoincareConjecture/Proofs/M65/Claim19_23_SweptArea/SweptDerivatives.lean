import PoincareConjecture.Proofs.M65.Claim19_23_SweptArea.InteriorSweptAnnulus
import PoincareConjecture.Proofs.M65.Mathlib.SmoothTimeChange

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

private theorem hasDerivAt_annulusPoint_left (x y : ℝ) :
    HasDerivAt (fun r => annulusPoint r y) (EuclideanSpace.basisFun (Fin 2) ℝ 0) x := by
  have h : HasDerivAt (fun r : ℝ => ![r, y]) ![1, 0] x := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact hasDerivAt_id x
    · exact hasDerivAt_const x y
  have hh := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm.toContinuousLinearMap
    |>.hasFDerivAt.comp_hasDerivAt x h
  have heq : EuclideanSpace.basisFun (Fin 2) ℝ 0 = annulusPoint 1 0 := by
    ext i
    fin_cases i <;> simp [EuclideanSpace.basisFun_apply, annulusPoint, EuclideanSpace.single]
  rw [heq]
  exact hh

private theorem hasDerivAt_annulusPoint_right (x y : ℝ) :
    HasDerivAt (annulusPoint x) (EuclideanSpace.basisFun (Fin 2) ℝ 1) y := by
  have h : HasDerivAt (fun r : ℝ => ![x, r]) ![0, 1] y := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact hasDerivAt_const y x
    · exact hasDerivAt_id y
  have hh := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm.toContinuousLinearMap
    |>.hasFDerivAt.comp_hasDerivAt y h
  have heq : EuclideanSpace.basisFun (Fin 2) ℝ 1 = annulusPoint 0 1 := by
    ext i
    fin_cases i <;> simp [EuclideanSpace.basisFun_apply, annulusPoint, EuclideanSpace.single]
  rw [heq]
  exact hh

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Set.Icc a b)}

theorem m65SweptMap_angular_derivative {c : ℝ → ℝ → M} (hc : M62ShrinkingCurve F c)
    {s t : ℝ} (has : a < s) (hst : s ≤ t) (htb : t < b) (x y : ℝ) :
    mfderiv (𝓡 2) (𝓡 n) (m65SweptMap c s t) (annulusPoint x y)
        (EuclideanSpace.basisFun (Fin 2) ℝ 0) =
      curveVelocity (fun r => c r (s + (t - s) * Real.smoothTransition y)) x := by
  have hd := hasDerivAt_annulusPoint_left x y
  have hdv : mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (fun r => annulusPoint r y) x 1 =
      EuclideanSpace.basisFun (Fin 2) ℝ 0 := by
    simpa +instances only [mfderiv_eq_fderiv, fderiv_apply_one_eq_deriv] using! hd.deriv
  have hchain := mfderiv_comp_apply (f := fun r => annulusPoint r y)
    (g := m65SweptMap c s t) x
    ((m65SweptMap_contMDiff hc has hst htb).mdifferentiableAt (by simp))
    hd.differentiableAt.mdifferentiableAt (1 : ℝ)
  erw [hdv] at hchain
  exact hchain.symm

theorem m65SweptMap_time_derivative {c : ℝ → ℝ → M} (hc : M62ShrinkingCurve F c)
    {s t : ℝ} (has : a < s) (hst : s ≤ t) (htb : t < b) (x y : ℝ) :
    mfderiv (𝓡 2) (𝓡 n) (m65SweptMap c s t) (annulusPoint x y)
        (EuclideanSpace.basisFun (Fin 2) ℝ 1) =
      ((t - s) * deriv Real.smoothTransition y) •
        m62CurvatureVector F c (s + (t - s) * Real.smoothTransition y) x := by
  let tau : ℝ → ℝ := fun r => s + (t - s) * Real.smoothTransition r
  have htau : tau y ∈ Set.Ioo a b :=
    ⟨has.trans_le (m65SweptTime_mem hst y).1, (m65SweptTime_mem hst y).2.trans_lt htb⟩
  have hmem : (x, tau y) ∈ (Set.univ ×ˢ Set.Ioo a b : Set (ℝ × ℝ)) :=
    ⟨Set.mem_univ _, htau⟩
  have hcTime : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n) (c x) (tau y) :=
    (((hc.joint_smooth (x, tau y) hmem).contMDiffAt
      ((isOpen_univ.prod isOpen_Ioo).mem_nhds hmem)).mdifferentiableAt (by simp)).comp _
        ((differentiableAt_const x).prodMk differentiableAt_id).mdifferentiableAt
  have htd := Real.hasDerivAt_affine_smoothTransition s t y
  have htv : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) tau y 1 =
      (t - s) * deriv Real.smoothTransition y := by
    simpa +instances only [mfderiv_eq_fderiv, fderiv_apply_one_eq_deriv] using! htd.deriv
  have hd := hasDerivAt_annulusPoint_right x y
  have hdv : mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (annulusPoint x) y 1 =
      EuclideanSpace.basisFun (Fin 2) ℝ 1 := by
    simpa +instances only [mfderiv_eq_fderiv, fderiv_apply_one_eq_deriv] using! hd.deriv
  have hplane := mfderiv_comp_apply (f := annulusPoint x) (g := m65SweptMap c s t) y
    ((m65SweptMap_contMDiff hc has hst htb).mdifferentiableAt (by simp))
    hd.differentiableAt.mdifferentiableAt (1 : ℝ)
  erw [hdv] at hplane
  have htime := mfderiv_comp_apply (f := tau) (g := c x) y hcTime
    htd.differentiableAt.mdifferentiableAt (1 : ℝ)
  erw [htv] at htime
  have hscale : (t - s) * deriv Real.smoothTransition y =
      ((t - s) * deriv Real.smoothTransition y) • (1 : ℝ) := by simp
  erw [hscale, map_smul] at htime
  exact hplane.symm.trans (htime.trans (congrArg _ (hc.equation (tau y) htau x)))

end PoincareConjecture
