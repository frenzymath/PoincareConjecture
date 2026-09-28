import PoincareConjecture.Proofs.M47.BlowupControlsCapConnectionDerivative
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.EuclideanNorm

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.M47

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)

private noncomputable def frameConnectionBilinear
    {g : RiemannianMetric n V} (D : LeviCivitaData g) (x : V) : V →ₗ[ℝ] V →ₗ[ℝ] V :=
  LinearMap.mk₂ ℝ (fun u v => D.euclideanConnection u v x)
    (fun u v w => congrFun (D.euclideanConnection_add_left u v w) x)
    (fun c u v => congrFun (D.euclideanConnection_smul_left c u v) x)
    (fun u v w => congrFun (D.euclideanConnection_add_right u v w) x)
    (fun c u v => congrFun (D.euclideanConnection_smul_right c u v) x)

theorem cap_connectionDifference_compose_frame
    {g0 g1 : RiemannianMetric n V} (D0 : LeviCivitaData g0) (D1 : LeviCivitaData g1)
    (e : V ≃L[ℝ] V) (x u v w : V) (k : Fin n) :
    let b := EuclideanSpace.basisFun (Fin n) ℝ
    let B := fun a c => D1.euclideanConnection a c x - D0.euclideanConnection a c x
    inner ℝ (b k) (e.symm (B u (B v w))) =
      ∑ l, inner ℝ (b k) (e.symm (B u (e (b l)))) * inner ℝ (b l) (e.symm (B v w)) := by
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  let B := frameConnectionBilinear D1 x - frameConnectionBilinear D0 x
  have hrec : (∑ l, inner ℝ (b l) (e.symm (B v w)) • e (b l)) = B v w := by
    calc
      _ = e (∑ l, inner ℝ (b l) (e.symm (B v w)) • b l) := by
        simp only [map_sum, map_smul]
      _ = e (e.symm (B v w)) := congrArg e (b.sum_repr' (e.symm (B v w)))
      _ = B v w := e.apply_symm_apply _
  change inner ℝ (b k) (e.symm (B u (B v w))) = _
  conv_lhs => rw [← hrec]
  simp only [map_sum, map_smul, inner_sum, inner_smul_right]
  apply Finset.sum_congr rfl
  intro l _
  change inner ℝ (b l) (e.symm (B v w)) * inner ℝ (b k) (e.symm (B u (e (b l)))) =
    inner ℝ (b k) (e.symm (B u (e (b l)))) * inner ℝ (b l) (e.symm (B v w))
  ring

theorem cap_ricci_difference_connection_frame
    {g0 g1 : RiemannianMetric n V} (D0 : LeviCivitaData g0) (D1 : LeviCivitaData g1)
    (e : V ≃L[ℝ] V) (x : V)
    (hzero : ∀ u v : V, D0.euclideanConnection u v x = 0) (i j : Fin n) :
    let b := EuclideanSpace.basisFun (Fin n) ℝ
    let Delta := fun u v y => D1.euclideanConnection u v y - D0.euclideanConnection u v y
    let B := fun k i j => inner ℝ (b k) (e.symm (Delta (e (b i)) (e (b j)) x))
    let dB := fun l k i j =>
      inner ℝ (b k) (e.symm (fderiv ℝ (Delta (e (b i)) (e (b j))) x (e (b l))))
    D1.ricci x (e (b i)) (e (b j)) - D0.ricci x (e (b i)) (e (b j)) =
      ∑ k, ((dB k k i j - dB i k k j) +
        ∑ l, (B k k l * B l i j - B k i l * B l k j)) := by
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  let E := b.toBasis.map e.toLinearEquiv
  have hcoord (z : V) (k : Fin n) : E.repr z k = inner ℝ (b k) (e.symm z) := by
    change (b.toBasis.repr (e.symm z)) k = _
    exact b.repr_apply_apply (e.symm z) k
  have hE (k : Fin n) : E k = e (b k) := rfl
  dsimp only
  rw [cap_ricci_difference_normal D0 D1 x hzero E]
  apply Finset.sum_congr rfl
  intro k _
  rw [hcoord, hE]
  have hlinear (v1 v2 v3 v4 : V) :
      inner ℝ (b k) (e.symm (v1 - v2 + v3 - v4)) =
        inner ℝ (b k) (e.symm v1) - inner ℝ (b k) (e.symm v2) +
          inner ℝ (b k) (e.symm v3) - inner ℝ (b k) (e.symm v4) := by
    simp only [map_sub, map_add, inner_sub_right, inner_add_right]
  rw [hlinear]
  rw [cap_connectionDifference_compose_frame D0 D1 e x,
    cap_connectionDifference_compose_frame D0 D1 e x]
  rw [Finset.sum_sub_distrib]
  ring

end PoincareConjecture.M47
