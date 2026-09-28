import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Splitting.ParallelGradient.FlowIsometry
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Splitting.ParallelGradient.LevelSet

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

open Set TopologicalSpace
open Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M]
  [IsManifold (𝓡 (n + 1)) ∞ M] {g : RiemannianMetric (n + 1) M}

theorem gradientFlow_product_metric
    {D : LeviCivitaData g} {f : M → ℝ} {Φ : ℝ → M → M}
    (hf : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ f)
    (hu : HasUnitGradient D f) (hz : HasZeroHessian D f)
    (hs : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 (n + 1))) (𝓡 (n + 1)) ∞
      (fun z : ℝ × M => Φ z.1 z.2))
    (hΦ : ∀ x, IsMIntegralCurve (fun t => Φ t x) (D.gradient f))
    (h0 : ∀ x, Φ 0 x = x) :
    letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
      ⟨finrank_euclideanSpace_fin⟩
    letI := openLevelSetChartedSpace hf (⊤ : Opens M)
      (fun x _ => regular_of_hasUnitGradient hu x) n 0
    letI := isManifold_openLevelSet hf (⊤ : Opens M)
      (fun x _ => regular_of_hasUnitGradient hu x) n 0
    let h := regularLevelMetric hf (⊤ : Opens M)
      (fun x _ => regular_of_hasUnitGradient hu x) 0 g
    let F := fun z : zeroLevelSet f × ℝ => Φ z.2 (zeroLevelIncl f z.1)
    ∀ (z : zeroLevelSet f × ℝ) (v w : TangentSpace ((𝓡 n).prod 𝓘(ℝ, ℝ)) z),
      g.inner (F z) (mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓡 (n + 1)) F z v)
        (mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓡 (n + 1)) F z w) =
          h.inner z.1 v.1 w.1 + v.2 * w.2 := by
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  let hreg := fun x (_ : x ∈ (⊤ : Opens M)) => regular_of_hasUnitGradient hu x
  letI := openLevelSetChartedSpace hf (⊤ : Opens M) hreg n 0
  letI := isManifold_openLevelSet hf (⊤ : Opens M) hreg n 0
  let h := regularLevelMetric hf (⊤ : Opens M) hreg 0 g
  let F := fun z : zeroLevelSet f × ℝ => Φ z.2 (zeroLevelIncl f z.1)
  have hi := contMDiff_openLevelIncl hf (⊤ : Opens M) hreg n 0
  have hFs (s : ℝ) : ContMDiff (𝓡 (n + 1)) (𝓡 (n + 1)) ∞ (Φ s) :=
    hs.comp (contMDiff_const.prodMk contMDiff_id)
  have hF : ContMDiff ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓡 (n + 1)) ∞ F :=
    hs.comp (contMDiff_snd.prodMk (hi.comp contMDiff_fst))
  change ∀ (z : zeroLevelSet f × ℝ) (v w : TangentSpace ((𝓡 n).prod 𝓘(ℝ, ℝ)) z),
    g.inner (F z) (mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓡 (n + 1)) F z v)
      (mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓡 (n + 1)) F z w) =
        h.inner z.1 v.1 w.1 + v.2 * w.2
  intro z v w
  let A := mfderiv (𝓡 n) (𝓡 (n + 1)) (fun y => Φ z.2 (zeroLevelIncl f y)) z.1
  let V := D.gradient f (F z)
  have hd (u : TangentSpace ((𝓡 n).prod 𝓘(ℝ, ℝ)) z) :
      mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓡 (n + 1)) F z u = A u.1 + u.2 • V := by
    rw [mfderiv_prod_eq_add_apply (hF.mdifferentiable (by simp) z)]
    have ht := (hΦ (zeroLevelIncl f z.1) z.2).mfderiv
    change mfderiv 𝓘(ℝ, ℝ) (𝓡 (n + 1)) (fun t => Φ t (zeroLevelIncl f z.1)) z.2 =
      (1 : ℝ →L[ℝ] ℝ).smulRight V at ht
    change A u.1 + mfderiv 𝓘(ℝ, ℝ) (𝓡 (n + 1))
      (fun t => Φ t (zeroLevelIncl f z.1)) z.2 u.2 = _
    rw [ht]
    rfl
  have hA : A = (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) (Φ z.2) (zeroLevelIncl f z.1)).comp
      (mfderiv (𝓡 n) (𝓡 (n + 1)) (zeroLevelIncl f) z.1) :=
    mfderiv_comp z.1 (hFs z.2 |>.mdifferentiable (by simp) _) (hi.mdifferentiable (by simp) _)
  have hhorizontal : g.inner (F z) (A v.1) (A w.1) = h.inner z.1 v.1 w.1 := by
    rw [hA]
    exact gradientFlow_preserves_metric hf hz hs hΦ h0 z.2 (zeroLevelIncl f z.1) _ _
  have hscalar : (fun y : zeroLevelSet f => f (Φ z.2 (zeroLevelIncl f y))) = fun _ => z.2 := by
    funext y
    rw [integralCurve_value_eq_add hf hu (hΦ _) (h0 _) z.2,
      show f (zeroLevelIncl f y) = 0 from y.2, zero_add]
  have horth (u : TangentSpace (𝓡 n) z.1) : g.inner (F z) V (A u) = 0 := by
    rw [D.inner_gradient]
    have hc := mfderiv_comp z.1 (hf.mdifferentiable (by simp) _)
      (((hFs z.2).comp hi).mdifferentiable (by simp) _)
    change mfderiv (𝓡 n) 𝓘(ℝ, ℝ)
      (fun y : zeroLevelSet f => f (Φ z.2 (zeroLevelIncl f y))) z.1 =
        (mfderiv (𝓡 (n + 1)) 𝓘(ℝ, ℝ) f (F z)).comp A at hc
    rw [hscalar, mfderiv_const] at hc
    exact (congrArg (fun L => L u) hc).symm
  change g.inner (F z) _ _ = h.inner z.1 v.1 w.1 + v.2 * w.2
  rw [hd v, hd w]
  simp only [map_add, add_apply, map_smul, smul_apply, smul_eq_mul]
  rw [hhorizontal, horth, g.symm (F z) (A v.1) V, horth, hu (F z)]
  ring

end PoincareConjecture.RiemannianMetric
