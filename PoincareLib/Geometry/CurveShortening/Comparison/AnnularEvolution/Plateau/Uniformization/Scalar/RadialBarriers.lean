import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Uniformization.Scalar.Maximum

/-!
# Actual radial barriers for the annular scalar potential

The squared Euclidean radius has nonzero differential on the closed
annulus. Compact retained-metric estimates therefore make both steep
radial exponentials strictly subharmonic. Normalizing their actual
circle values gives positive interior comparison functions for each
of the annular boundary components.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

namespace PoincareMT.M64Uniformization

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

variable {g : RiemannianMetric 2 Plane} (D : LeviCivitaData g)

private theorem radial_smooth :
    ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (fun x : Plane => ‖x‖ ^ 2) :=
  contMDiff_iff_contDiff.mpr (contDiff_id.norm_sq ℝ)

/-- Squared radius has strictly positive retained gradient energy away from the actual
origin, independently of the choice of smooth metric. Source: Morgan--Tian (2007), Lemma
19.15, pp. 447-449, with the project construction in
`proof-work/tasks/M64/derivations/2026-09-24-annular-strict-range.md`; scalar boundary and
energy details are recorded in
`proof-work/tasks/M64/reviews/2026-09-27-round1-uniformization-scalar.md`. -/
theorem scalarRadial_gradient_pos {x : Plane} (hx : x ≠ 0) :
    0 < g.inner x (D.gradient (fun y : Plane => ‖y‖ ^ 2) x)
      (D.gradient (fun y : Plane => ‖y‖ ^ 2) x) := by
  apply g.pos x
  intro hzero
  have h := D.inner_gradient (fun y : Plane => ‖y‖ ^ 2) x x
  rw [hzero] at h
  have hd : fderiv ℝ (fun y : Plane => ‖y‖ ^ 2) x x = 2 * ‖x‖ ^ 2 := by
    have heq := congrArg (fun L : Plane →L[ℝ] ℝ => L x)
      ((hasFDerivAt_id x).norm_sq).fderiv
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      add_apply, ContinuousLinearMap.comp_id,
      smul_apply, id_eq, innerSL_apply_apply, real_inner_self_eq_norm_sq,
      two_smul, two_mul] using heq
  have hdf : mvfderiv (𝓡 2) (fun y : Plane => ‖y‖ ^ 2) x x =
      fderiv ℝ (fun y : Plane => ‖y‖ ^ 2) x x := by
    simp only [mvfderiv, mfderiv_eq_fderiv, NormedSpace.fromTangentSpace]
    rfl
  rw [hdf, hd] at h
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hinner : g.inner x 0 x = 0 := by simp
  rw [hinner] at h
  nlinarith [sq_pos_of_pos hn]

/-- The literal radial exponential obeys the retained scalar chain rule. Source:
Morgan--Tian (2007), Lemma 19.15, pp. 447-449, with the project construction in
`proof-work/tasks/M64/derivations/2026-09-24-annular-strict-range.md`; scalar boundary and
energy details are recorded in
`proof-work/tasks/M64/reviews/2026-09-27-round1-uniformization-scalar.md`. -/
theorem scalarRadial_exp_laplacian (c : ℝ) (x : Plane) :
    D.laplacian (fun y : Plane => Real.exp (c * ‖y‖ ^ 2)) x =
      Real.exp (c * ‖x‖ ^ 2) *
        (c * D.laplacian (fun y : Plane => ‖y‖ ^ 2) x +
          c ^ 2 * g.inner x (D.gradient (fun y : Plane => ‖y‖ ^ 2) x)
            (D.gradient (fun y : Plane => ‖y‖ ^ 2) x)) := by
  let F : ℝ → ℝ := fun r => Real.exp (c * r)
  have hF : ContDiff ℝ ∞ F := Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)
  have hdF (r : ℝ) : deriv F r = c * Real.exp (c * r) := by
    have h := (Real.hasDerivAt_exp (c * r)).comp r ((hasDerivAt_id r).const_mul c)
    simpa only [F, Function.comp_def, mul_one, one_mul, mul_comm] using h.deriv
  have hddF (r : ℝ) : deriv (deriv F) r = c ^ 2 * Real.exp (c * r) := by
    rw [show deriv F = fun s => c * F s from funext hdF]
    rw [deriv_const_mul _ (hF.differentiable (by simp) r), hdF]
    ring
  have h := D.laplacian_comp radial_smooth hF x
  rw [hdF, hddF] at h
  change D.laplacian (fun y : Plane => Real.exp (c * ‖y‖ ^ 2)) x = _ at h
  rw [h]
  ring

/-- One actual positive coefficient makes both increasing and decreasing radial exponentials
strictly subharmonic on the entire closed annulus. Source: Morgan--Tian (2007), Lemma 19.15,
pp. 447-449, with the project construction in
`proof-work/tasks/M64/derivations/2026-09-24-annular-strict-range.md`; scalar boundary and
energy details are recorded in
`proof-work/tasks/M64/reviews/2026-09-27-round1-uniformization-scalar.md`. -/
theorem exists_annular_radial_exponential_barriers :
    ∃ alpha : ℝ, 0 < alpha ∧
      ∀ x, 0 ≤ scalarAnnulusDefining x →
        0 < D.laplacian (fun y : Plane => Real.exp (alpha * ‖y‖ ^ 2)) x ∧
        0 < D.laplacian (fun y : Plane => Real.exp (-alpha * ‖y‖ ^ 2)) x := by
  let f : Plane → ℝ := fun x => ‖x‖ ^ 2
  let E : Plane → ℝ := fun x => g.inner x (D.gradient f x) (D.gradient f x)
  let K := {x : Plane | 0 ≤ scalarAnnulusDefining x}
  have hK : IsCompact K := scalarClosedAnnulus_isCompact
  have hKne : K.Nonempty := scalarClosedAnnulus_isConnected.nonempty
  have hEc : Continuous E := D.continuous_inner_gradient radial_smooth radial_smooth
  have hEp (x : Plane) (hx : x ∈ K) : 0 < E x := by
    apply scalarRadial_gradient_pos D
    intro hz
    have h := ((scalarAnnulusDefining_nonneg x).mp hx).1
    norm_num [hz] at h
  obtain ⟨a, ha, hmin⟩ := hK.exists_isMinOn hKne hEc.continuousOn
  obtain ⟨b, hb, hmax⟩ := hK.exists_isMaxOn hKne
    (D.continuous_laplacian radial_smooth).abs.continuousOn
  let alpha := (|D.laplacian f b| + 1) / E a
  have halpha : 0 < alpha := div_pos (by positivity) (hEp a ha)
  have halphaE : alpha * E a = |D.laplacian f b| + 1 :=
    div_mul_cancel₀ _ (hEp a ha).ne'
  refine ⟨alpha, halpha, ?_⟩
  intro x hx
  have hbound : |D.laplacian f x| < alpha * E x := by
    have hmul := mul_le_mul_of_nonneg_left (hmin hx) halpha.le
    have hmax' : |D.laplacian f x| ≤ |D.laplacian f b| := hmax hx
    linarith
  have hp : 0 < alpha * E x + D.laplacian f x := by
    linarith [neg_abs_le (D.laplacian f x)]
  have hm : 0 < alpha * E x - D.laplacian f x := by
    linarith [le_abs_self (D.laplacian f x)]
  constructor
  · rw [scalarRadial_exp_laplacian]
    apply mul_pos (Real.exp_pos _)
    have h := mul_pos halpha hp
    change 0 < alpha * D.laplacian f x + alpha ^ 2 * E x
    nlinarith
  · rw [scalarRadial_exp_laplacian]
    apply mul_pos (Real.exp_pos _)
    have h := mul_pos halpha hm
    change 0 < -alpha * D.laplacian f x + (-alpha) ^ 2 * E x
    nlinarith

end PoincareMT.M64Uniformization
