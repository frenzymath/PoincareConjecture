import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.DirectionEvaluation
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Matrix.Positivity.StrictContact


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle BigOperators Topology

universe u

namespace Poincare.RicciFlow.Harnack

open PoincareConjecture Poincare.VectorBundle

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}



lemma differentiableAt_perturbedHamiltonDirectionQuadratic
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M J) (T₀ : ℝ)
    {t : ℝ} (ht : t ∈ interior J) (hτ : t - T₀ ≠ 0)
    (q : HamiltonDirection n M) {φ : ℝ × M → ℝ} {ψ : ℝ → ℝ}
    (hφ : DifferentiableAt ℝ (fun s => φ (s, q.1.val.1)) t)
    (hψ : DifferentiableAt ℝ ψ t) :
    DifferentiableAt ℝ (fun s => perturbedHamiltonDirectionQuadratic F T₀ φ ψ s q) t := by
  let x := q.1.val.1
  let e := FiberFamily.vector q.1
  let U := fun a b => q.2 (Sum.inl (a, b))
  let W := fun a => q.2 (Sum.inr a)
  have hg (a b : Fin n) : DifferentiableAt ℝ
      (fun s => (F.metric s).inner x (e a) (e b)) t :=
    ((F.equation t (interior_subset ht) x (e a) (e b)).hasDerivAt
      (mem_interior_iff_mem_nhds.mp ht)).differentiableAt
  have hi (a b c d : Fin n) : DifferentiableAt ℝ
      (fun s => metricTwoFormIdentity (F.metric s) x ![e a, e b, e c, e d]) t :=
    (((hg a c).mul (hg b d)).sub ((hg a d).mul (hg b c))).div_const 2
  have hm := DifferentiableAt.fun_sum (u := Finset.univ) fun a _ =>
    DifferentiableAt.fun_sum (u := Finset.univ) fun b _ =>
      ((differentiableAt_hamiltonM hC F T₀ ht hτ x (e a) (e b)).mul_const (W a)).mul_const (W b)
  have hp := DifferentiableAt.fun_sum (u := Finset.univ) fun a _ =>
    DifferentiableAt.fun_sum (u := Finset.univ) fun b _ =>
      DifferentiableAt.fun_sum (u := Finset.univ) fun c _ =>
        (((hasDerivAt_hamiltonP_evolution hC F ht x (e a) (e b) (e c)).differentiableAt.mul_const
          (U a b)).mul_const (W c))
  have hr := DifferentiableAt.fun_sum (u := Finset.univ) fun a _ =>
    DifferentiableAt.fun_sum (u := Finset.univ) fun b _ =>
      DifferentiableAt.fun_sum (u := Finset.univ) fun c _ =>
        DifferentiableAt.fun_sum (u := Finset.univ) fun d _ =>
          ((((hC.curvature_evolution n M J F t (interior_subset ht) x
            (e a) (e b) (e c) (e d)).hasDerivAt
              (mem_interior_iff_mem_nhds.mp ht)).differentiableAt.mul_const (U a b)).mul_const (U c d))
  have hgs := DifferentiableAt.fun_sum (u := Finset.univ) fun a _ =>
    DifferentiableAt.fun_sum (u := Finset.univ) fun b _ =>
      ((hg a b).mul_const (W a)).mul_const (W b)
  have his := DifferentiableAt.fun_sum (u := Finset.univ) fun a _ =>
    DifferentiableAt.fun_sum (u := Finset.univ) fun b _ =>
      DifferentiableAt.fun_sum (u := Finset.univ) fun c _ =>
        DifferentiableAt.fun_sum (u := Finset.univ) fun d _ =>
          ((hi a b c d).mul_const (U a b)).mul_const (U c d)
  exact ((((hm.add (hp.const_mul 2)).add hr).add (hφ.mul hgs)).add (hψ.mul his))

end Poincare.RicciFlow.Harnack
