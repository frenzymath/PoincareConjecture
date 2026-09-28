import PoincareConjecture.Proofs.Horizon.Analysis.Approximation.RegularizedMinimum
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Composition
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Linearity
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Hessian.Locality









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

private theorem scalar_mvfderiv_comp {f : M → ℝ} {F : ℝ → ℝ} {x : M}
    (hf : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f x)
    (hF : DifferentiableAt ℝ F (f x)) (v : TangentSpace (𝓡 n) x) :
    mvfderiv (𝓡 n) (F ∘ f) x v = deriv F (f x) * mvfderiv (𝓡 n) f x v := by
  rw [mvfderiv_comp x hF.mdifferentiableAt hf]
  simp only [ContinuousLinearMap.comp_apply, mvfderiv, mfderiv_eq_fderiv]
  rw [hF.hasDerivAt.hasFDerivAt.fderiv]
  change mvfderiv (𝓡 n) f x v * deriv F (f x) = _
  exact mul_comm _ _


theorem contMDiffAt_regularizedMin (δ : ℝ) (hδ : 0 < δ)
    {f h : M → ℝ} {x : M}
    (hf : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f x)
    (hh : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ h x) :
    ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y => Poincare.regularizedMin δ hδ (f y) (h y)) x := by
  have ha := (Poincare.contDiff_regularizedAbs δ hδ).contMDiff.contMDiffAt.comp x (hf.sub hh)
  have hp : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun y => (f y + h y - Poincare.regularizedAbs δ hδ (f y - h y)) * (2 : ℝ)⁻¹) x :=
    ((hf.add hh).sub ha).mul contMDiffAt_const
  simpa only [Poincare.regularizedMin, div_eq_mul_inv] using hp


theorem mvfderiv_regularizedMin (δ : ℝ) (hδ : 0 < δ)
    {f h : M → ℝ} {x : M}
    (hf : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f x)
    (hh : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) h x)
    (v : TangentSpace (𝓡 n) x) :
    mvfderiv (𝓡 n) (fun y => Poincare.regularizedMin δ hδ (f y) (h y)) x v =
      ((1 - deriv (Poincare.regularizedAbs δ hδ) (f x - h x)) / 2) * mvfderiv (𝓡 n) f x v +
      ((1 + deriv (Poincare.regularizedAbs δ hδ) (f x - h x)) / 2) * mvfderiv (𝓡 n) h x v := by
  have ha := (Poincare.contDiff_regularizedAbs δ hδ).differentiable (by simp)
  have hsum : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) (fun y => f y + h y) x := hf.add hh
  have hdiff : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) (fun y => f y - h y) x := hf.sub hh
  have hcomp : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ)
      (fun y => Poincare.regularizedAbs δ hδ (f y - h y)) x :=
    (ha (f x - h x)).mdifferentiableAt.comp x hdiff
  have heq : (fun y => Poincare.regularizedMin δ hδ (f y) (h y)) =
      fun y => (1 / 2 : ℝ) * (f y + h y - Poincare.regularizedAbs δ hδ (f y - h y)) := by
    funext y
    unfold Poincare.regularizedMin
    ring
  rw [heq, mvfderiv_const_mul, mvfderiv_fun_sub hsum hcomp, mvfderiv_fun_add hf hh]
  simp only [sub_apply, add_apply]
  have hchain := scalar_mvfderiv_comp hdiff (ha _) v
  change mvfderiv (𝓡 n) (fun y => Poincare.regularizedAbs δ hδ (f y - h y)) x v = _ at hchain
  rw [hchain, mvfderiv_fun_sub hf hh]
  simp only [sub_apply]
  ring



theorem mvfderiv_regularizedMin_le (δ : ℝ) (hδ : 0 < δ)
    {f h : M → ℝ} {x : M}
    (hf : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f x)
    (hh : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) h x)
    (v : TangentSpace (𝓡 n) x) {B : ℝ}
    (hfB : mvfderiv (𝓡 n) f x v ≤ B) (hhB : mvfderiv (𝓡 n) h x v ≤ B) :
    mvfderiv (𝓡 n) (fun y => Poincare.regularizedMin δ hδ (f y) (h y)) x v ≤ B := by
  obtain ⟨ha, hb⟩ := abs_le.mp (Poincare.abs_deriv_regularizedAbs_le_one δ hδ (f x - h x))
  rw [mvfderiv_regularizedMin δ hδ hf hh]
  calc
    _ ≤ ((1 - deriv (Poincare.regularizedAbs δ hδ) (f x - h x)) / 2) * B +
        ((1 + deriv (Poincare.regularizedAbs δ hδ) (f x - h x)) / 2) * B :=
      add_le_add (mul_le_mul_of_nonneg_left hfB (by linarith))
        (mul_le_mul_of_nonneg_left hhB (by linarith))
    _ = B := by ring



theorem le_mvfderiv_regularizedMin (δ : ℝ) (hδ : 0 < δ)
    {f h : M → ℝ} {x : M}
    (hf : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f x)
    (hh : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) h x)
    (v : TangentSpace (𝓡 n) x) {B : ℝ}
    (hfB : B ≤ mvfderiv (𝓡 n) f x v) (hhB : B ≤ mvfderiv (𝓡 n) h x v) :
    B ≤ mvfderiv (𝓡 n) (fun y => Poincare.regularizedMin δ hδ (f y) (h y)) x v := by
  obtain ⟨ha, hb⟩ := abs_le.mp (Poincare.abs_deriv_regularizedAbs_le_one δ hδ (f x - h x))
  rw [mvfderiv_regularizedMin δ hδ hf hh]
  calc
    B = ((1 - deriv (Poincare.regularizedAbs δ hδ) (f x - h x)) / 2) * B +
        ((1 + deriv (Poincare.regularizedAbs δ hδ) (f x - h x)) / 2) * B := by ring
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hfB (by linarith))
      (mul_le_mul_of_nonneg_left hhB (by linarith))



theorem contMDiffOn_regularizedMin (δ : ℝ) (hδ : 0 < δ)
    {f h : M → ℝ} {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f U)
    (hh : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ h U) :
    ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y => Poincare.regularizedMin δ hδ (f y) (h y)) U := by
  intro x hx
  exact (contMDiffAt_regularizedMin δ hδ ((hf x hx).contMDiffAt (hU.mem_nhds hx))
    ((hh x hx).contMDiffAt (hU.mem_nhds hx))).contMDiffWithinAt

namespace LeviCivitaData

variable [IsManifold (𝓡 n) ∞ M] {g : RiemannianMetric n M}

private theorem hessian_add_at (D : LeviCivitaData g) {f h : M → ℝ} {x : M}
    (hf : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f x)
    (hh : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ h x) (u v : TangentSpace (𝓡 n) x) :
    D.hessian (fun y => f y + h y) x u v = D.hessian f x u v + D.hessian h x u v := by
  have hgf := (D.contMDiffAt_gradient hf).mdifferentiableAt (by simp)
  have hgh := (D.contMDiffAt_gradient hh).mdifferentiableAt (by simp)
  have hsum : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y => f y + h y) x := hf.add hh
  have hfn := (contMDiffAt_iff_contMDiffAt_nhds (by simp : (1 : ℕ∞ω) ≠ ∞)).mp
    (hf.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp))
  have hhn := (contMDiffAt_iff_contMDiffAt_nhds (by simp : (1 : ℕ∞ω) ≠ ∞)).mp
    (hh.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp))
  have heq : D.gradient (fun y => f y + h y) =ᶠ[𝓝 x] D.gradient f + D.gradient h := by
    filter_upwards [hfn, hhn] with y hfy hhy
    exact D.gradient_add (hfy.mdifferentiableAt (by simp)) (hhy.mdifferentiableAt (by simp))
  have hc := D.connection.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
    ((D.contMDiffAt_gradient hsum).mdifferentiableAt (by simp))
    (mdifferentiableAt_add_section hgf hgh) (by simp) heq
  rw [D.hessian_eq_inner_connection_gradient hsum,
    D.hessian_eq_inner_connection_gradient hf, D.hessian_eq_inner_connection_gradient hh,
    congrArg (fun F => F u) hc, D.connection.isCovariantDerivativeOn.add hgf hgh]
  simp only [add_apply, map_add]

private theorem hessian_sub_at (D : LeviCivitaData g) {f h : M → ℝ} {x : M}
    (hf : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f x)
    (hh : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ h x) (u v : TangentSpace (𝓡 n) x) :
    D.hessian (fun y => f y - h y) x u v = D.hessian f x u v - D.hessian h x u v := by
  have heq : (fun y => f y - h y) = fun y => f y + (-1 : ℝ) * h y := by
    funext y
    ring
  have hneg : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y => (-1 : ℝ) * h y) x :=
    contMDiffAt_const.mul hh
  rw [heq, hessian_add_at D hf hneg, D.hessian_const_mul]
  ring

private theorem hessian_comp_at (D : LeviCivitaData g) {f : M → ℝ} {F : ℝ → ℝ} {x : M}
    (hf : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f x) (hF : ContDiff ℝ ∞ F)
    (u v : TangentSpace (𝓡 n) x) :
    D.hessian (F ∘ f) x u v = deriv F (f x) * D.hessian f x u v +
      deriv (deriv F) (f x) * mvfderiv (𝓡 n) f x u * mvfderiv (𝓡 n) f x v := by
  have hcomp := hF.contMDiff.contMDiffAt.comp x hf
  have hdf := (hF.deriv' (n := ∞)).contMDiff.contMDiffAt.comp x hf
  have hgf := (D.contMDiffAt_gradient hf).mdifferentiableAt (by simp)
  have hfn := (contMDiffAt_iff_contMDiffAt_nhds (by simp : (1 : ℕ∞ω) ≠ ∞)).mp
    (hf.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp))
  have heq : D.gradient (F ∘ f) =ᶠ[𝓝 x] (deriv F ∘ f) • D.gradient f := by
    filter_upwards [hfn] with y hy
    exact D.gradient_comp (hy.mdifferentiableAt (by simp)) (hF.differentiable (by simp) (f y))
  have hc := D.connection.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
    ((D.contMDiffAt_gradient hcomp).mdifferentiableAt (by simp))
    ((hdf.mdifferentiableAt (by simp)).smul_section hgf) (by simp) heq
  rw [D.hessian_eq_inner_connection_gradient hcomp,
    congrArg (fun F => F u) hc,
    D.connection.isCovariantDerivativeOn.leibniz hgf (hdf.mdifferentiableAt (by simp)),
    D.hessian_eq_inner_connection_gradient hf]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    map_add, map_smul, smul_eq_mul, Function.comp_apply, D.inner_gradient]
  rw [scalar_mvfderiv_comp (hf.mdifferentiableAt (by simp))
    ((hF.deriv' (n := ∞)).differentiable (by simp) (f x))]



theorem hessian_regularizedMin (D : LeviCivitaData g) (δ : ℝ) (hδ : 0 < δ)
    {f h : M → ℝ} {x : M}
    (hf : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f x)
    (hh : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ h x) (u v : TangentSpace (𝓡 n) x) :
    D.hessian (fun y => Poincare.regularizedMin δ hδ (f y) (h y)) x u v =
      ((1 - deriv (Poincare.regularizedAbs δ hδ) (f x - h x)) / 2) * D.hessian f x u v +
      ((1 + deriv (Poincare.regularizedAbs δ hδ) (f x - h x)) / 2) * D.hessian h x u v -
      (deriv (deriv (Poincare.regularizedAbs δ hδ)) (f x - h x) / 2) *
        (mvfderiv (𝓡 n) f x u - mvfderiv (𝓡 n) h x u) *
        (mvfderiv (𝓡 n) f x v - mvfderiv (𝓡 n) h x v) := by
  have hA := Poincare.contDiff_regularizedAbs δ hδ
  have hsum : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y => f y + h y) x := hf.add hh
  have hdiff : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y => f y - h y) x := hf.sub hh
  have ha : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun y => Poincare.regularizedAbs δ hδ (f y - h y)) x :=
    hA.contMDiff.contMDiffAt.comp x hdiff
  have heq : (fun y => Poincare.regularizedMin δ hδ (f y) (h y)) =
      fun y => (1 / 2 : ℝ) * (f y + h y - Poincare.regularizedAbs δ hδ (f y - h y)) := by
    funext y
    unfold Poincare.regularizedMin
    ring
  have hchain := hessian_comp_at D hdiff hA u v
  change D.hessian (fun y => Poincare.regularizedAbs δ hδ (f y - h y)) x u v = _ at hchain
  rw [heq, D.hessian_const_mul, hessian_sub_at D hsum ha,
    hessian_add_at D hf hh, hchain,
    hessian_sub_at D hf hh, mvfderiv_fun_sub (hf.mdifferentiableAt (by simp))
      (hh.mdifferentiableAt (by simp))]
  simp only [sub_apply]
  ring



theorem hessian_regularizedMin_le (D : LeviCivitaData g) (δ : ℝ) (hδ : 0 < δ)
    {f h : M → ℝ} {x : M}
    (hf : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f x)
    (hh : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ h x)
    (v : TangentSpace (𝓡 n) x) {H : ℝ}
    (hfH : D.hessian f x v v ≤ H * g.inner x v v)
    (hhH : D.hessian h x v v ≤ H * g.inner x v v) :
    D.hessian (fun y => Poincare.regularizedMin δ hδ (f y) (h y)) x v v ≤
      H * g.inner x v v := by
  obtain ⟨ha, hb⟩ := abs_le.mp (Poincare.abs_deriv_regularizedAbs_le_one δ hδ (f x - h x))
  have hc := mul_nonneg
    (div_nonneg (Poincare.deriv2_regularizedAbs_nonneg δ hδ (f x - h x)) (by norm_num : (0 : ℝ) ≤ 2))
    (sq_nonneg (mvfderiv (𝓡 n) f x v - mvfderiv (𝓡 n) h x v))
  rw [hessian_regularizedMin D δ hδ hf hh]
  calc
    _ ≤ ((1 - deriv (Poincare.regularizedAbs δ hδ) (f x - h x)) / 2) * D.hessian f x v v +
        ((1 + deriv (Poincare.regularizedAbs δ hδ) (f x - h x)) / 2) * D.hessian h x v v := by
      nlinarith only [hc]
    _ ≤ ((1 - deriv (Poincare.regularizedAbs δ hδ) (f x - h x)) / 2) * (H * g.inner x v v) +
        ((1 + deriv (Poincare.regularizedAbs δ hδ) (f x - h x)) / 2) * (H * g.inner x v v) :=
      add_le_add (mul_le_mul_of_nonneg_left hfH (by linarith))
        (mul_le_mul_of_nonneg_left hhH (by linarith))
    _ = _ := by ring



theorem gradient_regularizedMin_norm_le (D : LeviCivitaData g) (δ : ℝ) (hδ : 0 < δ)
    {f h : M → ℝ} {x : M}
    (hf : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f x)
    (hh : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) h x)
    {L : ℝ} (hL : 0 ≤ L)
    (hfL : Real.sqrt (g.inner x (D.gradient f x) (D.gradient f x)) ≤ L)
    (hhL : Real.sqrt (g.inner x (D.gradient h x) (D.gradient h x)) ≤ L) :
    Real.sqrt (g.inner x
      (D.gradient (fun y => Poincare.regularizedMin δ hδ (f y) (h y)) x)
      (D.gradient (fun y => Poincare.regularizedMin δ hδ (f y) (h y)) x)) ≤ L := by
  apply (D.gradient_norm_le_iff _ x hL).mpr
  intro v
  have hfB := (D.gradient_norm_le_iff f x hL).mp hfL v
  have hhB := (D.gradient_norm_le_iff h x hL).mp hhL v
  apply abs_le.mpr
  exact ⟨le_mvfderiv_regularizedMin δ hδ hf hh v (abs_le.mp hfB).1 (abs_le.mp hhB).1,
    mvfderiv_regularizedMin_le δ hδ hf hh v (abs_le.mp hfB).2 (abs_le.mp hhB).2⟩

end LeviCivitaData
end PoincareConjecture
