import PoincareConjecture.Proofs.M35.Uniqueness.RawDistanceExhaustion

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.M35.Uniqueness

theorem raw_curvature_derivatives_bounded_on_slab
    (P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
    (H : StandardCapEstimate g₀) (G : PartialStandardCapFlow g₀)
    {T : ℝ} (hT : 0 < T) (hTlt : T < G.lifetime) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t ∈ Icc 0 T, ∀ x : StandardCapSpace,
      (G.flow.connection t).curvatureDerivativeNorm k x ≤ C := by
  classical
  have hsub : Icc 0 T ⊆ Ico 0 G.lifetime := fun _ ht => ⟨ht.1, ht.2.trans_lt hTlt⟩
  let F := Poincare.Geometry.RicciFlow.Harnack.restrictFlow G.flow hsub
    (ordConnected_Icc : (Icc (0 : ℝ) T).OrdConnected)
    (show (Icc (0 : ℝ) T).Nontrivial from
      ⟨0, ⟨le_rfl, hT.le⟩, T, ⟨hT.le, le_rfl⟩, hT.ne⟩)
  obtain ⟨K₀, hK₀, hcurv⟩ := G.curvature_locally_bounded T hT.le hTlt
  choose C hC hCb using H.curvature_derivative_bounds
  let K := max K₀ (∑ j ∈ Finset.range (k + 1), C j) + 1
  have hK₀K : K₀ ≤ K := by
    dsimp only [K]
    linarith [le_max_left K₀ (∑ j ∈ Finset.range (k + 1), C j)]
  have hK : 0 < K := by
    dsimp only [K]
    linarith [le_max_left K₀ (∑ j ∈ Finset.range (k + 1), C j)]
  have hCK (j : ℕ) (hj : j ≤ k) : C j ≤ K := by
    have hjmem : j ∈ Finset.range (k + 1) := Finset.mem_range.mpr (by omega)
    have hsum := Finset.single_le_sum (fun i (_ : i ∈ Finset.range (k + 1)) => hC i) hjmem
    dsimp only [K]
    linarith [le_max_right K₀ (∑ j ∈ Finset.range (k + 1), C j)]
  have hinit (j : ℕ) (hj : j ≤ k) (x : StandardCapSpace) :
      (F.connection 0).curvatureDerivativeNorm j x ≤ K := by
    have htransport (g h : RiemannianMetric 3 StandardCapSpace)
        (D : LeviCivitaData g) (D' : LeviCivitaData h) (heq : g = h) (hD : HEq D D') :
        D.curvatureDerivativeNorm j x = D'.curvatureDerivativeNorm j x := by
      subst h
      cases eq_of_heq hD
      rfl
    change (G.flow.connection 0).curvatureDerivativeNorm j x ≤ K
    rw [htransport _ _ _ _ G.initial_metric G.initial_connection]
    exact (hCb j x).trans (hCK j hj)
  obtain ⟨B, hB, hShi⟩ := P.initial_derivative_estimates 3 k k K (K * T) 1
    hK (mul_pos hK hT) (by norm_num)
  refine ⟨B, hB, ?_⟩
  intro t ht x
  have hcompact : IsCompact (closure ((F.metric 0).ball x 1)) :=
    Proofs.M09.isCompact_closure_metric_ball (F.metric 0)
      (G.complete P ⟨le_rfl, G.lifetime_pos⟩) x 1
  have hx : x ∈ (F.metric 0).ball x (1 / 2) := by
    change (F.metric 0).edist x x < ENNReal.ofReal (1 / 2)
    rw [← RiemannianMetric.toEMetricSpace_edist]
    have hz := @edist_self StandardCapSpace
      (F.metric 0).toEMetricSpace.toPseudoEMetricSpace x
    rw [hz]
    exact ENNReal.ofReal_pos.mpr (by norm_num)
  have htime : T ≤ (K * T) / K := by
    rw [le_div_iff₀ hK]
    exact le_of_eq (mul_comm T K)
  have hbound := hShi StandardCapSpace T hT htime F x hcompact
    (fun s hs y => ((le_abs_self _).trans (hcurv s hs y)).trans hK₀K)
    hinit t ht (Or.inr le_rfl) x hx
  change (F.connection t).curvatureDerivativeNorm k x ≤ B
  simpa only [Nat.sub_self, Nat.cast_zero, zero_div, Real.rpow_zero, div_one] using hbound

end PoincareConjecture.M35.Uniqueness
