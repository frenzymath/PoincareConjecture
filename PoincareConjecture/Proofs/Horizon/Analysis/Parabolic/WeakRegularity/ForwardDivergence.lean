import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.WeakRegularity.ForwardEquation


noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped ContDiff Topology

namespace Poincare.Analysis.Parabolic.WeakRegularity.Canonical

variable {n : ℕ} {U : Set (Spacetime n)}

private theorem sd_smooth (hU : IsOpen U) {f : Spacetime n → ℝ}
    (hf : ContDiffOn ℝ ∞ f U) (i : Fin n) :
    ContDiffOn ℝ ∞ (spatialDeriv i f) U :=
  (hf.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const

private theorem sd_mul (hU : IsOpen U) {f g : Spacetime n → ℝ}
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    {z : Spacetime n} (hz : z ∈ U) (i : Fin n) :
    spatialDeriv i (fun y => f y * g y) z =
      spatialDeriv i f z * g z + f z * spatialDeriv i g z := by
  rw [spatialDeriv, fderiv_fun_mul
    ((hf.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp))
    ((hg.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp))]
  simp only [add_apply, smul_apply, smul_eq_mul, spatialDeriv]
  ring

private theorem sd_sum (hU : IsOpen U) {f : Fin n → Spacetime n → ℝ}
    (hf : ∀ j, ContDiffOn ℝ ∞ (f j) U) {z : Spacetime n}
    (hz : z ∈ U) (i : Fin n) :
    spatialDeriv i (fun y => ∑ j, f j y) z = ∑ j, spatialDeriv i (f j) z := by
  rw [spatialDeriv, fderiv_fun_sum (fun j _ =>
    ((hf j).contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp))]
  simp only [ContinuousLinearMap.sum_apply, spatialDeriv]

private theorem sd_sub (hU : IsOpen U) {f g : Spacetime n → ℝ}
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    {z : Spacetime n} (hz : z ∈ U) (i : Fin n) :
    spatialDeriv i (fun y => f y - g y) z =
      spatialDeriv i f z - spatialDeriv i g z := by
  rw [spatialDeriv, fderiv_fun_sub
    ((hf.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp))
    ((hg.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp))]
  rfl

private theorem sd_add (hU : IsOpen U) {f g : Spacetime n → ℝ}
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    {z : Spacetime n} (hz : z ∈ U) (i : Fin n) :
    spatialDeriv i (fun y => f y + g y) z =
      spatialDeriv i f z + spatialDeriv i g z := by
  rw [spatialDeriv, fderiv_fun_add
    ((hf.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp))
    ((hg.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp))]
  rfl

private theorem sd_mul_second (hU : IsOpen U) {f g : Spacetime n → ℝ}
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    {z : Spacetime n} (hz : z ∈ U) (i j : Fin n) :
    spatialDeriv i (spatialDeriv j (fun y => f y * g y)) z =
      spatialDeriv i (spatialDeriv j f) z * g z +
      spatialDeriv j f z * spatialDeriv i g z +
      spatialDeriv i f z * spatialDeriv j g z +
      f z * spatialDeriv i (spatialDeriv j g) z := by
  have heq : spatialDeriv j (fun y => f y * g y) =ᶠ[𝓝 z]
      (fun y => spatialDeriv j f y * g y + f y * spatialDeriv j g y) := by
    filter_upwards [hU.mem_nhds hz] with y hy
    exact sd_mul hU hf hg hy j
  change fderiv ℝ _ z _ = _
  rw [heq.fderiv_eq]
  change spatialDeriv i (fun y => spatialDeriv j f y * g y +
    f y * spatialDeriv j g y) z = _
  rw [sd_add hU ((sd_smooth hU hf j).mul hg) (hf.mul (sd_smooth hU hg j)) hz,
    sd_mul hU (sd_smooth hU hf j) hg hz,
    sd_mul hU hf (sd_smooth hU hg j) hz]
  ring


theorem forwardCoefficients_operator_eq_divergence (hU : IsOpen U)
    {a : Fin n → Fin n → Spacetime n → ℝ} {b : Fin n → Spacetime n → ℝ}
    (ha : ∀ i j, ContDiffOn ℝ ∞ (a i j) U)
    (hb : ∀ i, ContDiffOn ℝ ∞ (b i) U)
    {w : Spacetime n → ℝ} (hw : ContDiffOn ℝ ∞ w U)
    {z : Spacetime n} (hz : z ∈ U) :
    (forwardCoefficients a b).operator w z = timeDeriv w z +
      ∑ i, spatialDeriv i (fun y => b i y * w y -
        ∑ j, spatialDeriv j (fun v => a i j v * w v) y) z := by
  have hsum (i : Fin n) : ContDiffOn ℝ ∞
      (fun y => ∑ j, spatialDeriv j (fun v => a i j v * w v) y) U :=
    ContDiffOn.sum (fun j _ => sd_smooth hU ((ha i j).mul hw) j)
  have hflux (i) := sd_sub hU ((hb i).mul hw) (hsum i) hz i
  have hds (i) := sd_sum hU (fun j => sd_smooth hU ((ha i j).mul hw) j) hz i
  have hd (i) := sd_sub hU (hb i)
    (ContDiffOn.sum (s := Finset.univ) (fun j _ =>
      (sd_smooth hU (ha i j) j).add (sd_smooth hU (ha j i) j))) hz i
  have hdd (i) := sd_sum hU (fun j =>
    (sd_smooth hU (ha i j) j).add (sd_smooth hU (ha j i) j)) hz i
  have hcross : (∑ i, ∑ j, spatialDeriv i (a i j) z * spatialDeriv j w z) =
      ∑ i, ∑ j, spatialDeriv j (a j i) z * spatialDeriv i w z :=
    Finset.sum_comm
  have hsecond : (∑ i, ∑ j, spatialDeriv i (spatialDeriv j (a j i)) z) =
      ∑ i, ∑ j, spatialDeriv j (spatialDeriv i (a i j)) z :=
    Finset.sum_comm
  have hsecondw := congrArg (fun r : ℝ => r * w z) hsecond
  simp only [Finset.sum_mul] at hsecondw
  simp only [Coefficients.operator, forwardCoefficients, hflux, hds, hd, hdd,
    sd_add hU (sd_smooth hU (ha _ _) _) (sd_smooth hU (ha _ _) _) hz,
    sd_mul hU (hb _) hw hz, sd_mul_second hU (ha _ _) hw hz]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_mul, sub_mul, add_mul]
  rw [hcross, hsecondw]
  ring



theorem forwardCoefficients_operator_weighted (hU : IsOpen U)
    {a : Fin n → Fin n → Spacetime n → ℝ} {b : Fin n → Spacetime n → ℝ}
    (ha : ∀ i j, ContDiffOn ℝ ∞ (a i j) U)
    (hb : ∀ i, ContDiffOn ℝ ∞ (b i) U)
    {ρ u : Spacetime n → ℝ} (hρ : ContDiffOn ℝ ∞ ρ U)
    (hu : ContDiffOn ℝ ∞ u U)
    (hbalance : ∀ z ∈ U, ∀ i,
      b i z * ρ z = ∑ j, spatialDeriv j (fun y => a i j y * ρ y) z)
    {z : Spacetime n} (hz : z ∈ U) :
    (forwardCoefficients a b).operator (fun y => ρ y * u y) z =
      timeDeriv (fun y => ρ y * u y) z -
      ∑ i, spatialDeriv i (fun y => ∑ j, ρ y * a i j y * spatialDeriv j u y) z := by
  rw [forwardCoefficients_operator_eq_divergence hU ha hb (hρ.mul hu) hz]
  have hflux (i) : (fun y => b i y * (ρ y * u y) -
      ∑ j, spatialDeriv j (fun v => a i j v * (ρ v * u v)) y) =ᶠ[𝓝 z]
      (fun y => -(∑ j, ρ y * a i j y * spatialDeriv j u y)) := by
    filter_upwards [hU.mem_nhds hz] with y hy
    have hprod (j) : spatialDeriv j (fun v => a i j v * (ρ v * u v)) y =
        spatialDeriv j (fun v => a i j v * ρ v) y * u y +
          ρ y * a i j y * spatialDeriv j u y := by
      simp_rw [← mul_assoc]
      rw [sd_mul hU ((ha i j).mul hρ) hu hy]
      ring
    simp only [hprod]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← hbalance y hy i]
    ring
  have hd (i) : spatialDeriv i (fun y => b i y * (ρ y * u y) -
      ∑ j, spatialDeriv j (fun v => a i j v * (ρ v * u v)) y) z =
      -spatialDeriv i (fun y => ∑ j, ρ y * a i j y * spatialDeriv j u y) z := by
    change fderiv ℝ _ z _ = _
    rw [(hflux i).fderiv_eq, fderiv_fun_neg]
    rfl
  simp only [hd]
  simp only [Finset.sum_neg_distrib, sub_eq_add_neg]

end Poincare.Analysis.Parabolic.WeakRegularity.Canonical
