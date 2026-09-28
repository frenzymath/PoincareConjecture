import PoincareConjecture.Proofs.M47.BlowupControlsCapNativeDerivative
import PoincareConjecture.Proofs.M03.MetricDifferenceEvolution
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.Euclidean










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.M47

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)




theorem cap_curvature_difference_normal
    {g0 g1 : RiemannianMetric n V} (D0 : LeviCivitaData g0) (D1 : LeviCivitaData g1)
    (x : V) (hzero : ∀ u v : V, D0.euclideanConnection u v x = 0)
    (u v w : V) :
    let B := fun a b y => D1.euclideanConnection a b y - D0.euclideanConnection a b y
    D1.curvature x u v w - D0.curvature x u v w =
      fderiv ℝ (B v w) x u - fderiv ℝ (B u w) x v +
        B u (B v w x) x - B v (B u w x) x := by
  dsimp only
  rw [D1.curvature_eq_euclideanConnection, D0.curvature_eq_euclideanConnection]
  rw [fderiv_fun_sub ((D1.contDiffAt_euclideanConnection x v w).differentiableAt (by simp))
      ((D0.contDiffAt_euclideanConnection x v w).differentiableAt (by simp)),
    fderiv_fun_sub ((D1.contDiffAt_euclideanConnection x u w).differentiableAt (by simp))
      ((D0.contDiffAt_euclideanConnection x u w).differentiableAt (by simp))]
  simp only [sub_apply, hzero, sub_zero]
  abel



theorem cap_ricci_difference_normal
    {g0 g1 : RiemannianMetric n V} (D0 : LeviCivitaData g0) (D1 : LeviCivitaData g1)
    (x : V) (hzero : ∀ u v : V, D0.euclideanConnection u v x = 0)
    (b : Module.Basis (Fin n) ℝ V) (u v : V) :
    let B := fun a c y => D1.euclideanConnection a c y - D0.euclideanConnection a c y
    D1.ricci x u v - D0.ricci x u v =
      ∑ i, b.repr (fderiv ℝ (B u v) x (b i) - fderiv ℝ (B (b i) v) x u +
        B (b i) (B u v x) x - B u (B (b i) v x) x) i := by
  dsimp only
  rw [Proofs.M03.ricci_eq_sum_basis_of_curvature_pairing D1 x u v b,
    Proofs.M03.ricci_eq_sum_basis_of_curvature_pairing D0 x u v b, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  calc
    _ = b.repr ((D1.curvature x (b i) u v : V) - (D0.curvature x (b i) u v : V)) i := by
      rw [map_sub, Finsupp.sub_apply]
      rfl
    _ = _ := congrArg (fun z : V => b.repr z i)
      (cap_curvature_difference_normal D0 D1 x hzero (b i) u v)

end PoincareConjecture.M47
