import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.ImplicitFunction.UniqueScalarRoot
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Topology.Order.IntermediateValue










noncomputable section
set_option autoImplicit false

open Set
open scoped ContDiff Manifold

namespace Poincare.Manifold



theorem bijective_of_deriv_pos_of_bounded_displacement
    {f : ℝ → ℝ} (hf : Continuous f) (hderiv : ∀ t, 0 < deriv f t)
    (hbound : ∃ C : ℝ, ∀ t, |f t - t| ≤ C) : Function.Bijective f := by
  refine ⟨(strictMono_of_deriv_pos hderiv).injective, ?_⟩
  obtain ⟨C, hC⟩ := hbound
  have hCnonneg : 0 ≤ C := (abs_nonneg (f 0 - 0)).trans (hC 0)
  intro y
  have hlo := (abs_le.mp (hC (y - C))).2
  have hhi := (abs_le.mp (hC (y + C))).1
  obtain ⟨t, _, ht⟩ := intermediate_value_Icc
    (show y - C ≤ y + C by linarith) hf.continuousOn
    (show y ∈ Icc (f (y - C)) (f (y + C)) from ⟨by linarith, by linarith⟩)
  exact ⟨t, ht⟩

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]



theorem exists_smooth_scalar_inverse
    {f : P × ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hbij : ∀ p, Function.Bijective (fun t => f (p, t)))
    (hderiv : ∀ p t, deriv (fun s => f (p, s)) t ≠ 0) :
    ∃ g : P × ℝ → ℝ, ContDiff ℝ ∞ g ∧
      (∀ p t, f (p, g (p, t)) = t) ∧
      ∀ p t, g (p, f (p, t)) = t := by
  classical
  let e (p : P) : ℝ ≃ ℝ := Equiv.ofBijective (fun t => f (p, t)) (hbij p)
  let g : P × ℝ → ℝ := fun q => (e q.1).symm q.2
  have hfg (p : P) (t : ℝ) : f (p, g (p, t)) = t := (e p).apply_symm_apply t
  have hgf (p : P) (t : ℝ) : g (p, f (p, t)) = t := (e p).symm_apply_apply t
  refine ⟨g, ?_, hfg, hgf⟩
  let F : (P × ℝ) × ℝ → ℝ := fun z => f (z.1.1, z.2) - z.1.2
  have hF : ContDiff ℝ ∞ F :=
    (hf.comp ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd)).sub
      (contDiff_snd.comp contDiff_fst)
  have hfp (p : P) : ContDiff ℝ ∞ (fun t => f (p, t)) :=
    hf.comp (contDiff_const.prodMk contDiff_id)
  apply Poincare.Analysis.contDiff_unique_scalar_root hF isOpen_univ
    (τ := g) (d := fun q => deriv (fun t => f (q.1, t)) (g q)) (c := 0)
    (fun _ => mem_univ _) (fun q => by simp only [F, hfg, sub_self])
  · intro q
    exact ((hfp q.1).differentiable (by simp) (g q)).hasDerivAt.sub_const q.2
  · intro q
    exact hderiv q.1 (g q)
  · intro q t _ ht
    apply (hbij q.1).injective
    exact (sub_eq_zero.mp ht).trans (hfg q.1 q.2).symm



def triangularDiffeomorph
    (f : P × ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (hbij : ∀ p, Function.Bijective (fun t => f (p, t)))
    (hderiv : ∀ p t, deriv (fun s => f (p, s)) t ≠ 0) :
    Diffeomorph 𝓘(ℝ, P × ℝ) 𝓘(ℝ, P × ℝ) (P × ℝ) (P × ℝ) ∞ := by
  classical
  let g := Classical.choose (exists_smooth_scalar_inverse hf hbij hderiv)
  have hg := Classical.choose_spec (exists_smooth_scalar_inverse hf hbij hderiv)
  exact {
    toEquiv := {
      toFun := fun z => (z.1, f z)
      invFun := fun z => (z.1, g z)
      left_inv := fun z => Prod.ext rfl (hg.2.2 z.1 z.2)
      right_inv := fun z => Prod.ext rfl (hg.2.1 z.1 z.2) }
    contMDiff_toFun := (contDiff_fst.prodMk hf).contMDiff
    contMDiff_invFun := (contDiff_fst.prodMk hg.1).contMDiff }

@[simp]
theorem triangularDiffeomorph_apply
    (f : P × ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (hbij : ∀ p, Function.Bijective (fun t => f (p, t)))
    (hderiv : ∀ p t, deriv (fun s => f (p, s)) t ≠ 0) (z : P × ℝ) :
    triangularDiffeomorph f hf hbij hderiv z = (z.1, f z) := rfl

@[simp]
theorem triangularDiffeomorph_symm_fst
    (f : P × ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (hbij : ∀ p, Function.Bijective (fun t => f (p, t)))
    (hderiv : ∀ p t, deriv (fun s => f (p, s)) t ≠ 0) (z : P × ℝ) :
    ((triangularDiffeomorph f hf hbij hderiv).symm z).1 = z.1 := rfl




def triangularDiffeomorphOfBoundedDisplacement
    (f : P × ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (hderiv : ∀ p t, 0 < deriv (fun s => f (p, s)) t)
    (hbound : ∀ p, ∃ C : ℝ, ∀ t, |f (p, t) - t| ≤ C) :
    Diffeomorph 𝓘(ℝ, P × ℝ) 𝓘(ℝ, P × ℝ) (P × ℝ) (P × ℝ) ∞ :=
  triangularDiffeomorph f hf
    (fun p => bijective_of_deriv_pos_of_bounded_displacement
      (hf.comp (contDiff_const.prodMk contDiff_id)).continuous (hderiv p) (hbound p))
    (fun p t => (hderiv p t).ne')

@[simp]
theorem triangularDiffeomorphOfBoundedDisplacement_apply
    (f : P × ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (hderiv : ∀ p t, 0 < deriv (fun s => f (p, s)) t)
    (hbound : ∀ p, ∃ C : ℝ, ∀ t, |f (p, t) - t| ≤ C) (z : P × ℝ) :
    triangularDiffeomorphOfBoundedDisplacement f hf hderiv hbound z = (z.1, f z) := rfl

end Poincare.Manifold
