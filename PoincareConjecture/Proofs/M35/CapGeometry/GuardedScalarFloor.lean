import PoincareConjecture.Proofs.M35.CapGeometry.UnitTimeScalarEstimates
import PoincareConjecture.Proofs.M35.TerminalBlowup.ScalarNeighborhood










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal

namespace PoincareConjecture.M35



theorem scalar_floor_on_ball_of_guarded_gradient
    (g : RiemannianMetric 3 StandardCapSpace) (D : LeviCivitaData g)
    (hpos : ∀ x, 0 < D.scalarCurvature x)
    (hreg : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ D.scalarCurvature)
    {A H : ℝ} (hA : 0 < A)
    (hgrad : ∀ x, H ≤ D.scalarCurvature x →
      ∀ v : TangentSpace (𝓡 3) x, g.inner x v v = 1 →
        |mvfderiv (𝓡 3) D.scalarCurvature x v| ≤
          A * D.scalarCurvature x ^ (3 / 2 : ℝ))
    {x y : StandardCapSpace} (hx : 16 * H ≤ D.scalarCurvature x)
    (hy : y ∈ g.ball x (D.scalarCurvature x ^ (-1 / 2 : ℝ) / A)) :
    D.scalarCurvature x / 16 < D.scalarCurvature y := by
  by_contra hnot
  have hyK := le_of_not_gt hnot
  let Q := D.scalarCurvature x
  have hQ : 0 < Q := hpos x
  have hK : 0 < Q / 16 := div_pos hQ (by norm_num)
  have hscale : Q ^ (-1 / 2 : ℝ) ≤ (Q / 16) ^ (-1 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos hK (by dsimp only [Q]; linarith [hpos x]) (by norm_num)
  have hcomm : g.edist y x = g.edist x y :=
    @edist_comm StandardCapSpace g.toEMetricSpace.toPseudoEMetricSpace y x
  have hxy : x ∈ g.ball y ((Q / 16) ^ (-1 / 2 : ℝ) / A) := by
    change g.edist y x < _
    rw [hcomm]
    exact hy.trans_le (ENNReal.ofReal_le_ofReal
      (div_le_div_of_nonneg_right hscale hA.le))
  have h := scalar_radius_lower_on_ball g D hpos hreg hA hK
    (by dsimp only [Q]; linarith) hgrad hyK hxy
  have h16 : (16 : ℝ) ^ (-1 / 2 : ℝ) = 1 / 4 := by
    rw [neg_div, Real.rpow_neg (by norm_num), ← Real.sqrt_eq_rpow]
    norm_num
  have hKpow : (Q / 16) ^ (-1 / 2 : ℝ) = 4 * Q ^ (-1 / 2 : ℝ) := by
    rw [Real.div_rpow hQ.le (by norm_num), h16]
    ring
  rw [hKpow] at h
  have hpow := Real.rpow_pos_of_pos hQ (-1 / 2 : ℝ)
  change 4 * Q ^ (-1 / 2 : ℝ) / 2 ≤ Q ^ (-1 / 2 : ℝ) at h
  linarith

end PoincareConjecture.M35

namespace PoincareConjecture.RepairedStandardCapExistenceData



theorem exists_high_scalar_ball_floor (P : M35StandardCapPredecessors)
    {g₀ : StandardInitialMetric} (E : RepairedStandardCapExistenceData g₀) :
    ∃ A H : ℝ, 0 < A ∧ 0 < H ∧ ∀ t ∈ Ico 0 E.flow.base.lifetime,
      ∀ x : StandardCapSpace, H ≤ (E.flow.connection t).scalarCurvature x →
      ∀ y ∈ (E.flow.metric t).ball x
        ((E.flow.connection t).scalarCurvature x ^ (-1 / 2 : ℝ) / A),
        (E.flow.connection t).scalarCurvature x / 16 <
          (E.flow.connection t).scalarCurvature y := by
  obtain ⟨A, H, hA, hH, hbounds⟩ :=
    M35.OrdinaryRealization.exists_unit_time_scalar_estimates P E
  refine ⟨A, 16 * H, hA, mul_pos (by norm_num) hH, ?_⟩
  intro t ht x hx y hy
  exact M35.scalar_floor_on_ball_of_guarded_gradient (E.flow.metric t)
    (E.flow.connection t) (E.scalar_pos ht)
    (Proofs.M09.scalarCurvature_contMDiff P.curvature (E.flow.connection t)) hA
    (fun z hz => (hbounds t ht z hz).1) hx hy

end PoincareConjecture.RepairedStandardCapExistenceData
