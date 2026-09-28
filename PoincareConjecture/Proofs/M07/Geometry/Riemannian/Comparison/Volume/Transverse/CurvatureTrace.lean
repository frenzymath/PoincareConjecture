import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.SectionalBounds
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Tensor.Contraction
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Transverse.Matrix












noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff BigOperators Bundle

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}


theorem ricci_eq_sum_frame_curvature
    (D : LeviCivitaData g) (x : M) (v : TangentSpace (𝓡 n) x)
    (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (P : EuclideanSpace ℝ (Fin n) ≃L[ℝ] TangentSpace (𝓡 n) x)
    (hP : ∀ u w, g.inner x (P u) (P w) = inner ℝ u w) :
    D.ricci x v v =
      ∑ i, g.inner x (D.curvature x (P (b i)) v v) (P (b i)) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let c := b.toBasis.map P.toLinearEquiv
  have hc : Orthonormal ℝ c := by
    apply orthonormal_iff_ite.mpr
    intro i j
    change g.inner x (P (b i)) (P (b j)) = _
    rw [hP]
    exact b.inner_eq_ite i j
  let d := c.toOrthonormalBasis hc
  have hd (i : Fin n) : d i = P (b i) := by
    simp [d, c]
  have htrace := bilinear_sum_orthonormalBasis_eq
    (D.curvatureTensor_bilinear_first_third x v v) (g.orthonormalBasis x) d
  simp only [curvatureTensor_bilinear_first_third_apply, hd] at htrace
  calc
    D.ricci x v v = ∑ i, D.curvatureTensor x (g.orthonormalBasis x i) v
        (g.orthonormalBasis x i) v := by
      apply Finset.sum_congr rfl
      intro i _
      rw [D.curvatureTensor_swap_first, D.curvatureTensor_swap_last]
      simp
    _ = ∑ i, D.curvatureTensor x (P (b i)) v (P (b i)) v := htrace
    _ = _ := rfl



theorem ricci_eq_transverse_curvature_trace
    {m : ℕ} {N : Type*} [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) N] [IsManifold (𝓡 (m + 1)) ∞ N]
    {g : RiemannianMetric (m + 1) N} (D : LeviCivitaData g) (x : N)
    (b : OrthonormalBasis (Fin (m + 1)) ℝ (EuclideanSpace ℝ (Fin (m + 1))))
    (P : EuclideanSpace ℝ (Fin (m + 1)) ≃L[ℝ] TangentSpace (𝓡 (m + 1)) x)
    (hP : ∀ u w, g.inner x (P u) (P w) = inner ℝ u w) :
    D.ricci x (P (b 0)) (P (b 0)) =
      (Matrix.of (fun i j : Fin m =>
        g.inner x (D.curvature x (P (b j.succ)) (P (b 0)) (P (b 0)))
          (P (b i.succ)))).trace := by
  rw [D.ricci_eq_sum_frame_curvature x (P (b 0)) b P hP, Fin.sum_univ_succ]
  have hzero : g.inner x (D.curvature x (P (b 0)) (P (b 0)) (P (b 0)))
      (P (b 0)) = 0 := by
    exact D.curvatureTensor_zero_first x (P (b 0)) (P (b 0)) (P (b 0))
  rw [hzero, zero_add]
  rfl

end PoincareConjecture.LeviCivitaData
