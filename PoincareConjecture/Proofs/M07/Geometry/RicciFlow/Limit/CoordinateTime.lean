import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Limit.TimeDerivative
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Coefficients

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators Topology
open Filter

namespace PoincareConjecture.RiemannianMetric

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

private theorem deriv_bilinear_eq_sum
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E)
    (B : ℝ → E →L[ℝ] E →L[ℝ] ℝ) (t : ℝ)
    (hB : ∀ i j, DifferentiableAt ℝ (fun s => B s (b i) (b j)) t)
    (u v : E) :
    deriv (fun s => B s u v) t =
      ∑ i, ∑ j, (b.repr u i * b.repr v j) * deriv (fun s => B s (b i) (b j)) t := by
  classical
  have hexpand (s : ℝ) : B s u v =
      ∑ i, ∑ j, (b.repr u i * b.repr v j) * B s (b i) (b j) := by
    conv_lhs => rw [← b.sum_repr u, ← b.sum_repr v]
    simp only [map_sum, sum_apply, map_smul, smul_apply, smul_eq_mul, Finset.mul_sum,
      mul_assoc]
    rw [Finset.sum_comm]
    congr 1
    ext i
    congr 1
    ext j
    ring
  have hd := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    HasDerivAt.fun_sum (u := Finset.univ) (fun j _ =>
      (hB i j).hasDerivAt.const_mul (b.repr u i * b.repr v j)))
  simpa only [← hexpand] using hd.deriv

theorem tendsto_inner_time_deriv_of_coordinate_deriv
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {α : Type*} {l : Filter α} {J : Set ℝ}
    (gseq : α → ℝ → RiemannianMetric n M) (g : ℝ → RiemannianMetric n M)
    (hseq : ∀ k, IsSmoothFamilyOn (gseq k) J) (hg : IsSmoothFamilyOn g J)
    (hJ : IsOpen J) {t : ℝ} (ht : t ∈ J) (x : M)
    (h : ∀ a b : Fin n,
      Tendsto (fun k => deriv (fun s => (gseq k s).pullbackCoefficients
        (extChartAt (𝓡 n) x).symm (extChartAt (𝓡 n) x x)
        (EuclideanSpace.basisFun (Fin n) ℝ a)
        (EuclideanSpace.basisFun (Fin n) ℝ b)) t) l
        (𝓝 (deriv (fun s => (g s).pullbackCoefficients
          (extChartAt (𝓡 n) x).symm (extChartAt (𝓡 n) x x)
          (EuclideanSpace.basisFun (Fin n) ℝ a)
          (EuclideanSpace.basisFun (Fin n) ℝ b)) t)))
    (u v : TangentSpace (𝓡 n) x) :
    Tendsto (fun k => deriv (fun s => (gseq k s).inner x u v) t) l
      (𝓝 (deriv (fun s => (g s).inner x u v) t)) := by
  classical
  let c := extChartAt (𝓡 n) x
  let p := c x
  have hp : c.symm p = x := c.left_inv (mem_extChartAt_source x)
  have hi : (mfderiv (𝓡 n) (𝓡 n) c.symm p).IsInvertible := by
    simpa only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] using
      isInvertible_mfderivWithin_extChartAt_symm (I := 𝓡 n) (mem_extChartAt_target x)
  obtain ⟨e, he⟩ := hi
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  have heval (G : ℝ → RiemannianMetric n M) (s : ℝ) :
      (G s).pullbackCoefficients c.symm p (e.symm u) (e.symm v) =
        (G s).inner x u v := by
    change (G s).inner (c.symm p)
      (mfderiv (𝓡 n) (𝓡 n) c.symm p (e.symm u))
      (mfderiv (𝓡 n) (𝓡 n) c.symm p (e.symm v)) = _
    rw [← he]
    simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]
    exact congrArg (fun y : M => (G s).inner y u v) hp
  have hdiff (G : ℝ → RiemannianMetric n M) (hG : IsSmoothFamilyOn G J)
      (a d : Fin n) :
      DifferentiableAt ℝ (fun s => (G s).pullbackCoefficients c.symm p (b a) (b d)) t := by
    change DifferentiableAt ℝ (fun s => (G s).inner (c.symm p)
      (mfderiv (𝓡 n) (𝓡 n) c.symm p (b a))
      (mfderiv (𝓡 n) (𝓡 n) c.symm p (b d))) t
    exact (hG.hasDerivAt_inner hJ ht _ _ _).differentiableAt
  have heq (G : ℝ → RiemannianMetric n M) (hG : IsSmoothFamilyOn G J) :=
    deriv_bilinear_eq_sum b (fun s => (G s).pullbackCoefficients c.symm p) t
      (hdiff G hG) (e.symm u) (e.symm v)
  simp only [heval] at heq
  simp_rw [heq _ hg, heq _ (hseq _)]
  apply tendsto_finsetSum
  intro a _
  apply tendsto_finsetSum
  intro d _
  exact (h a d).const_mul _

end PoincareConjecture.RiemannianMetric
