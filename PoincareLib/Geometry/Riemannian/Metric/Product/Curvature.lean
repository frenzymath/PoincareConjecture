import PoincareLib.Geometry.Riemannian.Metric.Product.EuclideanModel
import PoincareLib.Geometry.Riemannian.Metric.Product.Height
import PoincareLib.Geometry.Riemannian.Metric.Product.Sectional
import PoincareLib.Geometry.Riemannian.Splitting.ParallelGradient.FactorCurvature.Level

/-!
# Curvature of the Actual Product with the Real Line

The height is parallel and the horizontal inclusions are isometric. The
parallel-normal Gauss equation gives the horizontal tensor restriction,
which determines the scalar trace and every sectional lower bound.
-/

open Set Filter
open scoped Manifold ContDiff Bundle Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace PoincareMT.RiemannianMetric
variable {n : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (n+1))) P] [IsManifold (𝓡 (n+1)) ∞ P]
  (g : RiemannianMetric n M) (G : RiemannianMetric (n+1) P)
  (D : LeviCivitaData g) (DG : LeviCivitaData G)
  (e : (M × ℝ) ≃ₘ⟮(𝓡 n).prod 𝓘(ℝ,ℝ), 𝓡 (n+1)⟯ P)
  (hmetric : ∀ (z : M × ℝ) (v w : TangentSpace ((𝓡 n).prod 𝓘(ℝ,ℝ)) z),
    G.inner (e z)
      (mfderiv ((𝓡 n).prod 𝓘(ℝ,ℝ)) (𝓡 (n+1)) e z v)
      (mfderiv ((𝓡 n).prod 𝓘(ℝ,ℝ)) (𝓡 (n+1)) e z w) =
      g.inner z.1 v.1 w.1 + v.2*w.2)
include hmetric in
private theorem product_ricci_scalar_and_sectional (z : M × ℝ) :
    (∀ v w : TangentSpace (𝓡 n) z.1,
      DG.ricci (e z)
        (mfderiv ((𝓡 n).prod 𝓘(ℝ,ℝ)) (𝓡 (n+1)) e z (v, 0))
        (mfderiv ((𝓡 n).prod 𝓘(ℝ,ℝ)) (𝓡 (n+1)) e z (w, 0)) =
          D.ricci z.1 v w) ∧
    DG.scalarCurvature (e z) = D.scalarCurvature z.1 ∧
    ∀ {K : ℝ}, 0 ≤ K →
      (∀ v w : TangentSpace (𝓡 n) z.1, -K ≤ D.sectionalCurvature z.1 v w) →
      ∀ v w : TangentSpace (𝓡 (n+1)) (e z), -K ≤ DG.sectionalCurvature (e z) v w := by
  let i : M → P := fun x => e (x,z.2)
  let h : P → ℝ := Prod.snd ∘ e.symm
  have hh : ContMDiff (𝓡 (n+1)) 𝓘(ℝ,ℝ) ∞ h := contMDiff_snd.comp e.symm.contMDiff
  have hi : ContMDiff (𝓡 n) (𝓡 (n+1)) ∞ i :=
    e.contMDiff.comp (contMDiff_id.prodMk contMDiff_const)
  have hid (x : M) (v : TangentSpace (𝓡 n) x) :
      mfderiv (𝓡 n) (𝓡 (n+1)) i x v =
        mfderiv ((𝓡 n).prod 𝓘(ℝ,ℝ)) (𝓡 (n+1)) e (x,z.2) (v,0) := by
    change mfderiv (𝓡 n) (𝓡 (n+1)) (e ∘ fun x => (x,z.2)) x v = _
    erw [mfderiv_comp_apply _ (e.contMDiff.mdifferentiable (by simp) _)
      (mdifferentiableAt_id.prodMk mdifferentiableAt_const), mfderiv_prod_left]
    rfl
  have hm (x : M) (v w : TangentSpace (𝓡 n) x) :
      g.inner x v w = G.inner (i x)
        (mfderiv (𝓡 n) (𝓡 (n+1)) i x v) (mfderiv (𝓡 n) (𝓡 (n+1)) i x w) := by
    rw [hid,hid]
    change g.inner x v w = G.inner (e (x,z.2)) _ _
    rw [hmetric]
    simp
  obtain ⟨hu,hz⟩ := product_height_hasUnitGradient_and_hasZeroHessian g G DG e hmetric
  have ho (x : M) (v : TangentSpace (𝓡 n) x) :
      G.inner (i x) (DG.gradient h (i x)) (mfderiv (𝓡 n) (𝓡 (n+1)) i x v) = 0 := by
    rw [DG.inner_gradient]
    have hc := mfderiv_comp_apply x (hh.mdifferentiable (by simp) _) (hi.mdifferentiable (by simp) _) v
    have he : h ∘ i = fun _ => z.2 := by ext x; simp [h,i]
    rw [he,mfderiv_const] at hc
    exact hc.symm
  obtain ⟨_,hR⟩ := FactorCurvature.totallyGeodesic_and_curvatureTensor_of_orthogonal_parallel_gradient
    DG D hi hm hh hu hz ho z.1
  let L := (mfderiv (𝓡 n) (𝓡 (n+1)) i z.1).toLinearMap
  have hL (u v) : G.inner (i z.1) (L u) (L v) = g.inner z.1 u v := (hm _ _ _).symm
  have hn := curvatureTensor_gradient_slots_eq_zero hh hz (i z.1)
  have htrace := FactorCurvature.trace_identities DG D (i z.1) z.1 L hL
    (DG.gradient h (i z.1)) (hu _) (ho _) hR hn
  refine ⟨?_, htrace.2.1.symm, ?_⟩
  · intro v w
    simpa only [L, ContinuousLinearMap.coe_coe, hid] using (htrace.1 v w).symm
  intro K hK hsec
  exact FactorCurvature.sectional_lower_bound_of_null_normal DG D (i z.1) z.1 L hL
    (DG.gradient h (i z.1)) (hu _) (ho _) hR hn hK hsec

include hmetric in
/-- The ambient Ricci tensor restricts to the factor Ricci tensor on
horizontal tangent vectors of an isometric product with the line. -/
theorem ricci_eq_of_line_product (z : M × ℝ) (v w : TangentSpace (𝓡 n) z.1) :
    DG.ricci (e z)
      (mfderiv ((𝓡 n).prod 𝓘(ℝ,ℝ)) (𝓡 (n+1)) e z (v, 0))
      (mfderiv ((𝓡 n).prod 𝓘(ℝ,ℝ)) (𝓡 (n+1)) e z (w, 0)) =
        D.ricci z.1 v w :=
  (product_ricci_scalar_and_sectional g G D DG e hmetric z).1 v w

include hmetric in
/-- An isometric product with the line has exactly the scalar curvature of
its horizontal factor, with the specified Levi-Civita connections. -/
theorem scalarCurvature_eq_of_line_product (z : M × ℝ) :
    DG.scalarCurvature (e z) = D.scalarCurvature z.1 :=
  (product_ricci_scalar_and_sectional g G D DG e hmetric z).2.1
end PoincareMT.RiemannianMetric

namespace PoincareMT.RiemannianMetric
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem lineProduct_scalarCurvature (g : RiemannianMetric n M) (D : LeviCivitaData g) :
    let := lineProductChartedSpace (n := n) (M := M)
    let := lineProductIsManifold (n := n) (M := M)
    ∀ z : M × ℝ, (lineProduct g).leviCivitaData.scalarCurvature
      (lineProductDiffeomorph (n := n) (M := M) z) = D.scalarCurvature z.1 := by
  let := lineProductChartedSpace (n := n) (M := M)
  let := lineProductIsManifold (n := n) (M := M)
  dsimp only
  intro z
  exact (product_ricci_scalar_and_sectional g (lineProduct g) D (lineProduct g).leviCivitaData
    (lineProductDiffeomorph (n := n) (M := M)) (lineProduct_inner g) z).2.1

theorem lineProduct_sectionalCurvature_lower_bound (g : RiemannianMetric n M)
    (D : LeviCivitaData g)
    (hsec : ∀ x (v w : TangentSpace (𝓡 n) x), -1 ≤ D.sectionalCurvature x v w) :
    let := lineProductChartedSpace (n := n) (M := M)
    let := lineProductIsManifold (n := n) (M := M)
    ∀ z : M × ℝ, ∀ v w : TangentSpace (𝓡 (n+1)) z,
      -1 ≤ (lineProduct g).leviCivitaData.sectionalCurvature z v w := by
  let := lineProductChartedSpace (n := n) (M := M)
  let := lineProductIsManifold (n := n) (M := M)
  dsimp only
  intro z
  let e := lineProductDiffeomorph (n := n) (M := M)
  obtain ⟨x,rfl⟩ := e.surjective z
  exact (product_ricci_scalar_and_sectional g (lineProduct g) D (lineProduct g).leviCivitaData
    e (lineProduct_inner g) x).2.2 zero_le_one (hsec x.1)
end PoincareMT.RiemannianMetric
