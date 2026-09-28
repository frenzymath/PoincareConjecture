import PoincareConjecture.Proofs.M35.CapGeometry.ParallelFieldCurvature
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.SectionalBounds









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter
open scoped Manifold ContDiff Bundle Topology BigOperators

namespace PoincareConjecture.M35

local notation "E2" => EuclideanSpace ℝ (Fin 2)



theorem positive_surface_curvature_kernel
    {M : Type*} [TopologicalSpace M] [ChartedSpace E2 M]
    [IsManifold (𝓡 2) ∞ M] {g : RiemannianMetric 2 M}
    (D : LeviCivitaData g) (x : M) (z : TangentSpace (𝓡 2) x)
    (hpos : ∀ u v : TangentSpace (𝓡 2) x,
      g.inner x u u = 1 → g.inner x v v = 1 → g.inner x u v = 0 →
        0 < D.sectionalCurvature x u v)
    (hnull : ∀ u v w : TangentSpace (𝓡 2) x, D.curvatureTensor x u v w z = 0) :
    z = 0 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 2) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 2) x) = 2 := finrank_euclideanSpace_fin
  let b := (g.orthonormalBasis x).reindex (finCongr hdim)
  have hinner (i j : Fin 2) : g.inner x (b i) (b j) = if i = j then 1 else 0 :=
    b.inner_eq_ite i j
  have h00 : g.inner x (b 0) (b 0) = 1 := by simp only [hinner, ite_true]
  have h11 : g.inner x (b 1) (b 1) = 1 := by simp only [hinner, ite_true]
  have h01 : g.inner x (b 0) (b 1) = 0 := by simp only [hinner, Fin.zero_ne_one, ite_false]
  have hK : 0 < D.curvatureTensor x (b 0) (b 1) (b 0) (b 1) := by
    have hp := hpos (b 0) (b 1) h00 h11 h01
    simpa only [LeviCivitaData.sectionalCurvature, h00, h11, h01,
      mul_one, zero_pow (by norm_num : (2 : ℕ) ≠ 0), sub_zero, div_one] using hp
  have hrepr : (b.repr z) 0 • b 0 + (b.repr z) 1 • b 1 = z := by
    simpa only [Fin.sum_univ_two] using b.sum_repr z
  have hz0 := hnull (b 0) (b 1) (b 0)
  have hz1 := hnull (b 0) (b 1) (b 1)
  rw [← hrepr, D.curvatureTensor_add_last, D.curvatureTensor_smul_last,
    D.curvatureTensor_smul_last, D.curvatureTensor_zero_last, mul_zero, zero_add] at hz0
  rw [← hrepr, D.curvatureTensor_add_last, D.curvatureTensor_smul_last,
    D.curvatureTensor_smul_last, D.curvatureTensor_zero_last, mul_zero, add_zero] at hz1
  have hswap := D.curvatureTensor_swap_last x (b 0) (b 1) (b 1) (b 0)
  have ha : (b.repr z) 0 = 0 := by
    rw [hswap] at hz1
    exact (mul_eq_zero.mp hz1).resolve_right (neg_ne_zero.mpr hK.ne')
  have hb : (b.repr z) 1 = 0 := (mul_eq_zero.mp hz0).resolve_right hK.ne'
  rw [ha, hb, zero_smul, zero_smul, zero_add] at hrepr
  exact hrepr.symm


theorem positive_surface_parallel_germ
    {g : RiemannianMetric 2 E2} (D : LeviCivitaData g)
    {Z : E2 → E2} {x : E2} (hZ : ContDiffAt ℝ ∞ Z x)
    (hparallel : ∀ᶠ y in 𝓝 x, ∀ v : E2, D.connection Z y v = 0)
    (hpos : ∀ u v : E2,
      g.inner x u u = 1 → g.inner x v v = 1 → g.inner x u v = 0 →
        0 < D.sectionalCurvature x u v) : Z x = 0 :=
  positive_surface_curvature_kernel D x (Z x) hpos
    (curvatureTensor_parallel_field_germ D hZ hparallel)

end PoincareConjecture.M35
