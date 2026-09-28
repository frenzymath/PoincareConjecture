import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Product.CurvatureSupplement
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Product.Curvature
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.LocalIsometryRicci









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (n+1))) P] [IsManifold (𝓡 (n+1)) ∞ P]


theorem ricci_eq_of_line_product_local_isometry
    (g : RiemannianMetric n M) (G : RiemannianMetric (n+1) P)
    (D : LeviCivitaData g) (DG : LeviCivitaData G)
    (f : M × ℝ → P) (hf : ContMDiff ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓡 (n+1)) ∞ f)
    (hmetric : ∀ (z : M × ℝ) (v w : TangentSpace ((𝓡 n).prod 𝓘(ℝ, ℝ)) z),
      G.inner (f z)
        (mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓡 (n+1)) f z v)
        (mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓡 (n+1)) f z w) =
        g.inner z.1 v.1 w.1 + v.2 * w.2)
    (z : M × ℝ) (v w : TangentSpace (𝓡 n) z.1) :
    DG.ricci (f z)
      (mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓡 (n+1)) f z (v, 0))
      (mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓡 (n+1)) f z (w, 0)) =
      D.ricci z.1 v w := by
  let := lineProductChartedSpace (n := n) (M := M)
  let := lineProductIsManifold (n := n) (M := M)
  let e := lineProductDiffeomorph (n := n) (M := M)
  let H := lineProduct g
  let F : M × ℝ → P := f ∘ e.symm
  have hF : ContMDiff (𝓡 (n+1)) (𝓡 (n+1)) ∞ F := hf.comp e.symm.contMDiff
  have hFe : F ∘ e = f := by ext x; simp [F]
  have hfx (x : M × ℝ) : F (e x) = f x := congrFun hFe x
  have hd (x : M × ℝ) (a : TangentSpace ((𝓡 n).prod 𝓘(ℝ, ℝ)) x) :
      mfderiv (𝓡 (n+1)) (𝓡 (n+1)) F (e x)
        (mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓡 (n+1)) e x a) =
      mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓡 (n+1)) f x a := by
    rw [← mfderiv_comp_apply x (hF.mdifferentiable (by simp) _)
      (e.contMDiff.mdifferentiable (by simp) _), hFe]
  have hm (y : M × ℝ) (a b : TangentSpace (𝓡 (n+1)) y) :
      H.inner y a b = G.inner (F y)
        (mfderiv (𝓡 (n+1)) (𝓡 (n+1)) F y a)
        (mfderiv (𝓡 (n+1)) (𝓡 (n+1)) F y b) := by
    obtain ⟨x, rfl⟩ := e.surjective y
    obtain ⟨a, rfl⟩ := (e.mfderivToContinuousLinearEquiv (by simp) x).surjective a
    obtain ⟨b, rfl⟩ := (e.mfderivToContinuousLinearEquiv (by simp) x).surjective b
    change H.inner (e x)
      (mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓡 (n+1)) e x a)
      (mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓡 (n+1)) e x b) =
      G.inner (F (e x))
        (mfderiv (𝓡 (n+1)) (𝓡 (n+1)) F (e x)
          (mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓡 (n+1)) e x a))
        (mfderiv (𝓡 (n+1)) (𝓡 (n+1)) F (e x)
          (mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓡 (n+1)) e x b))
    rw [lineProduct_inner, hd, hd]
    erw [hfx]
    exact (hmetric x a b).symm
  have hr := H.leviCivitaData.ricci_eq_of_local_isometry DG isOpen_univ
    hF.contMDiffOn (fun y _ => hm y) (mem_univ (e z))
    (mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓡 (n+1)) e z (v, 0))
    (mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓡 (n+1)) e z (w, 0))
  rw [hd, hd] at hr
  erw [hfx] at hr
  exact hr.symm.trans
    (g.ricci_eq_of_line_product H D H.leviCivitaData e (lineProduct_inner g) z v w)

end PoincareConjecture.RiemannianMetric
