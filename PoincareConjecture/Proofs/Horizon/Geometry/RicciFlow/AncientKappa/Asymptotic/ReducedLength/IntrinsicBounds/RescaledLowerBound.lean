import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.IntrinsicBounds.GlobalLowerBound
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.TimeGrowth
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.RescalingGeometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M] {K : AncientKappaSolution n M}

theorem AncientRescaling.toReal_edist_sq_scale {c : ℝ} (R : AncientRescaling K c)
    {τ : ℝ} (hτ : 0 < τ) (x y : M) :
    ((R.flow.metric (-τ)).edist x y).toReal ^ 2 =
      ((K.flow.metric (-(c * τ))).edist x y).toReal ^ 2 / c := by
  rw [R.edist_scale (-τ) (neg_neg_of_pos hτ), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt (one_div_nonneg.mpr R.tau_pos.le)]
  simp only [mul_neg]
  ring

theorem AncientRescalingSequence.reducedLength_rescaled_lower_bound
    (S : AncientRescalingSequence K) (P : AncientAsymptoticSolitonPredecessors K)
    (k : ℕ) {τ : ℝ} (hτ : 0 < τ) (q : M) :
    (((S.rescaling k).flow.metric (-τ)).edist (S.base k) q).toReal ^ 2 /
        (16 * (2 * (n : ℝ) + 604) ^ 2 * τ) -
          (n : ℝ) / 2 * max (τ ^ 2) (τ ^ 2)⁻¹ - 1 ≤
      reducedLength K.flow 0 S.reference q (S.scale k * τ) := by
  have hl := P.reducedLength_intrinsic_lower_bound S.reference (S.base k) q
    (mul_pos (S.scale_pos k) hτ)
  have hb := S.reducedLength_at_base_time_le P k hτ
  rw [(S.rescaling k).toReal_edist_sq_scale hτ]
  have heq :
      ((K.flow.metric (-(S.scale k * τ))).edist (S.base k) q).toReal ^ 2 / S.scale k /
          (16 * (2 * (n : ℝ) + 604) ^ 2 * τ) =
        ((K.flow.metric (-(S.scale k * τ))).edist (S.base k) q).toReal ^ 2 /
          (16 * (2 * (n : ℝ) + 604) ^ 2 * (S.scale k * τ)) := by
    rw [div_div]
    congr 1
    ring
  rw [heq]
  linarith

theorem AncientRescalingSequence.exp_neg_reducedLength_le_gaussian
    (S : AncientRescalingSequence K) (P : AncientAsymptoticSolitonPredecessors K)
    (k : ℕ) {τ : ℝ} (hτ : 0 < τ) (q : M) :
    Real.exp (-reducedLength K.flow 0 S.reference q (S.scale k * τ)) ≤
      Real.exp ((n : ℝ) / 2 * max (τ ^ 2) (τ ^ 2)⁻¹ + 1) *
        Real.exp (-(((S.rescaling k).flow.metric (-τ)).edist (S.base k) q).toReal ^ 2 /
          (16 * (2 * (n : ℝ) + 604) ^ 2 * τ)) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h := S.reducedLength_rescaled_lower_bound P k hτ q
  rw [neg_div]
  linarith

end PoincareConjecture
