import PoincareLib.Geometry.Riemannian.Metric.Product.Height
import PoincareLib.Geometry.Riemannian.Splitting.ParallelGradient.FactorCurvature.Normal

/-!
# Axial Ricci curvature in an actual metric product

Morgan--Tian Claim 11.34, printed pp. 288-289, and Claim 11.35, p. 290.
The exact product metric makes its height gradient parallel for the retained
connection. Contraction then annihilates every purely axial tangent vector.
The elementary inverse-derivative and gradient calculations rederive the
private `product_mfderiv_inverse`, `product_mfderiv_surjective`, and
`product_height_gradient` in the eligible Metric/Product/Height module.
Reviewed derivation: `claim11_34-neck-product-graph.md`, section 3.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u v

namespace PoincareMT.M32

variable {n : ℕ} {C : Type u} {L : Type v}
  [TopologicalSpace C] [TopologicalSpace L]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) C] [IsManifold (𝓡 n) ∞ C]
  [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) L] [IsManifold (𝓡 (n + 1)) ∞ L]
  (gC : RiemannianMetric n C) (gL : RiemannianMetric (n + 1) L)
  (DL : LeviCivitaData gL)
  (Phi : (C × ℝ) ≃ₘ⟮(𝓡 n).prod 𝓘(ℝ, ℝ), 𝓡 (n + 1)⟯ L)
  (hproduct : ∀ (z : C × ℝ) (v w : TangentSpace ((𝓡 n).prod 𝓘(ℝ, ℝ)) z),
    gL.inner (Phi z)
      (mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓡 (n + 1)) Phi z v)
      (mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓡 (n + 1)) Phi z w) =
      gC.inner z.1 v.1 w.1 + v.2 * w.2)

omit [IsManifold (𝓡 n) ∞ C] [IsManifold (𝓡 (n + 1)) ∞ L] in
private theorem graph_product_mfderiv_inverse (z : C × ℝ)
    (v : TangentSpace ((𝓡 n).prod 𝓘(ℝ, ℝ)) z) :
    mfderiv (𝓡 (n + 1)) ((𝓡 n).prod 𝓘(ℝ, ℝ)) Phi.symm (Phi z)
      (mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓡 (n + 1)) Phi z v) = v := by
  have hh := mfderiv_comp z (Phi.symm.contMDiff.mdifferentiable (by simp) _)
    (Phi.contMDiff.mdifferentiable (by simp) _)
  have hid : (Phi.symm : L → C × ℝ) ∘ Phi = id := funext Phi.symm_apply_apply
  rw [hid, mfderiv_id] at hh
  exact (congrArg (fun A => A v) hh).symm

omit [IsManifold (𝓡 n) ∞ C] [IsManifold (𝓡 (n + 1)) ∞ L] in
private theorem graph_product_mfderiv_surjective (z : C × ℝ) :
    Function.Surjective (mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓡 (n + 1)) Phi z) := by
  intro w
  refine ⟨mfderiv (𝓡 (n + 1)) ((𝓡 n).prod 𝓘(ℝ, ℝ)) Phi.symm (Phi z) w, ?_⟩
  have hh := mfderiv_comp (Phi z) (Phi.contMDiff.mdifferentiable (by simp) _)
    (Phi.symm.contMDiff.mdifferentiable (by simp) _)
  have hid : (Phi : C × ℝ → L) ∘ Phi.symm = id := funext Phi.apply_symm_apply
  rw [hid, mfderiv_id, Phi.symm_apply_apply] at hh
  exact (congrArg (fun A => A w) hh).symm

include hproduct in
private theorem graph_product_height_gradient (z : C × ℝ) :
    DL.gradient (Prod.snd ∘ Phi.symm) (Phi z) =
      mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓡 (n + 1)) Phi z (0, 1) := by
  apply (gL.inner_isInvertible (Phi z)).injective
  ext w
  obtain ⟨v, rfl⟩ := graph_product_mfderiv_surjective Phi z w
  rw [DL.inner_gradient, hproduct]
  change mfderiv (𝓡 (n + 1)) 𝓘(ℝ, ℝ) (Prod.snd ∘ Phi.symm) (Phi z)
    (mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓡 (n + 1)) Phi z v) = _
  rw [mfderiv_comp_apply _ mdifferentiableAt_snd
    (Phi.symm.contMDiff.mdifferentiable (by simp) _),
    graph_product_mfderiv_inverse Phi z v, mfderiv_snd]
  simp
  rfl

include hproduct in
/-- Axial tangent vectors have zero Ricci curvature for the actual retained
connection in an exact metric product. Source: Claim 11.34, pp. 288-289,
and the product comparison in Claim 11.35, p. 290. The arbitrary-dimensional
argument is detailed in `claim11_34-neck-product-graph.md`, section 3. -/
theorem ricci_eq_zero_of_product_projection_mfderiv_eq_zero
    (x : L) (v : TangentSpace (𝓡 (n + 1)) x)
    (haxial : (mfderiv (𝓡 (n + 1)) ((𝓡 n).prod 𝓘(ℝ, ℝ)) Phi.symm x v).1 = 0) :
    DL.ricci x v v = 0 := by
  obtain ⟨z, rfl⟩ := Phi.surjective x
  obtain ⟨w, rfl⟩ := graph_product_mfderiv_surjective Phi z v
  erw [graph_product_mfderiv_inverse Phi z w] at haxial
  let H : L → ℝ := Prod.snd ∘ Phi.symm
  have hH : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ H :=
    contMDiff_snd.comp Phi.symm.contMDiff
  have hzero : RiemannianMetric.HasZeroHessian DL H :=
    (RiemannianMetric.product_height_hasUnitGradient_and_hasZeroHessian
      gC gL DL Phi hproduct).2
  have hw : w = w.2 • ((0, 1) : TangentSpace ((𝓡 n).prod 𝓘(ℝ, ℝ)) z) := by
    apply Prod.ext <;> simp [haxial]
  have hv : mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓡 (n + 1)) Phi z w =
      w.2 • DL.gradient H (Phi z) := by
    calc
      _ = mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓡 (n + 1)) Phi z
          (w.2 • ((0, 1) : TangentSpace ((𝓡 n).prod 𝓘(ℝ, ℝ)) z)) :=
        congrArg _ hw
      _ = w.2 • mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓡 (n + 1)) Phi z (0, 1) :=
        map_smul _ _ _
      _ = _ := congrArg (fun u => w.2 • u)
        (graph_product_height_gradient gC gL DL Phi hproduct z).symm
  change DL.ricci (Phi z)
    (mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓡 (n + 1)) Phi z w)
    (mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓡 (n + 1)) Phi z w) = 0
  rw [hv]
  simp only [LeviCivitaData.ricci, DL.curvatureTensor_smul_first,
    RiemannianMetric.curvatureTensor_gradient_first_eq_zero hH hzero,
    mul_zero, Finset.sum_const_zero]

end PoincareMT.M32
