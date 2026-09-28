import PoincareConjecture.Proofs.M34.Thm12_5_Existence.CommonCompactLifetime
import PoincareConjecture.Proofs.M34.Thm12_5_Existence.DoubleCurvature
import PoincareConjecture.Proofs.M03.ConnectionExistence
import PoincareConjecture.Statements.M34StandardCapExistence

set_option autoImplicit false

open scoped Manifold ContDiff
open Set

namespace PoincareConjecture.M34

instance endDouble_t3Space {g : RiemannianMetric 3 StandardCapSpace}
    (e : StandardCylindricalEnd g) {L : ℝ} (hL : 1 < L) : T3Space (EndDouble e hL) := by
  let := endDouble_t2Space e hL
  let := endDouble_compactSpace e hL
  let : R1Space (EndDouble e hL) := T2Space.r1Space
  let : T1Space (EndDouble e hL) := T2Space.t1Space
  let : NormalSpace (EndDouble e hL) := NormalSpace.of_compactSpace_r1Space
  let : T4Space (EndDouble e hL) := {}
  exact T4Space.t3Space

theorem exists_uniform_endDouble_flows (P : M34StandardCapPredecessors)
    (g0 : StandardInitialMetric) (E0 : StandardCapEstimate g0) :
    ∃ τ B : ℝ, 0 < τ ∧ 0 < B ∧ ∀ (L : ℝ) (hL : 1 < L),
      ∃ F : RicciFlow 3 (EndDouble g0.cylindrical_end hL) (Icc 0 τ),
        F.metric 0 = endDoubleMetric g0.cylindrical_end hL ∧
        (∀ t ∈ Icc 0 τ, MetricComplete (F.metric t)) ∧
        ∀ t ∈ Icc 0 τ, ∀ q : EndDouble g0.cylindrical_end hL,
          (F.connection t).curvatureTensorNorm q ≤ B := by
  obtain ⟨C, hC, hbound⟩ := endDouble_curvatureTensorNorm_bound g0 E0
  let τ : ℝ := 1 / (23328 * C)
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hsmall : 16 * (3 : ℝ) ^ 6 * C * τ ≤ 1 / 2 := by
    have hCne : C ≠ 0 := ne_of_gt hC
    dsimp [τ]
    norm_num
    field_simp
    nlinarith
  refine ⟨τ, 2 * C, hτ, by positivity, ?_⟩
  intro L hL
  obtain ⟨D⟩ := exists_leviCivitaData (endDoubleMetric g0.cylindrical_end hL)
  obtain ⟨F, hF, hnorm⟩ := exists_compactFlow_on_small_slab
    (P.local_flow 3 (EndDouble g0.cylindrical_end hL))
    (endDoubleMetric g0.cylindrical_end hL) D hC hτ hsmall (hbound L hL D)
  exact ⟨F, hF, fun t _ => (F.metric t).metricComplete_of_compact, hnorm⟩

end PoincareConjecture.M34
