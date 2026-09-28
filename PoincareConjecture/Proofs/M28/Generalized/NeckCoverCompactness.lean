import PoincareConjecture.Proofs.M28.Generalized.OrdinaryNeckVolume
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.NeckPrecompactBalls
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Covering










set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.M28

variable {M : Type u} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}




theorem exists_compact_bounded_scalar_neck_cover
    (K : NeckOnlyCover g) (D : LeviCivitaData g)
    (hD : ∀ N ∈ K.necks, N.connection = D)
    (hfinite : g.volumeMeasure univ ≠ ⊤) {B : ℝ} (hB : 0 < B) :
    ∃ C : Set M, IsCompact C ∧ {x | x ∈ K.X ∧ D.scalarCurvature x ≤ B} ⊆ C := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
      (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 3) M
  let S : Set M := {x | x ∈ K.X ∧ D.scalarCurvature x ≤ B}
  let δ := B ^ (-1 / 2 : ℝ) / 16
  let v := normalizedNeckVolumeLowerConstant * δ ^ 3
  have hδ : 0 < δ := div_pos (Real.rpow_pos_of_pos hB _) (by norm_num)
  have hv : 0 < v := mul_pos normalizedNeckVolumeLowerConstant_pos (pow_pos hδ 3)
  have hball (q : M) (s : ℝ) : Metric.eball q (ENNReal.ofReal s) = g.ball q s := by
    ext y
    change g.edist y q < ENNReal.ofReal s ↔ g.edist q y < ENNReal.ofReal s
    rw [show g.edist y q = g.edist q y from Manifold.riemannianEDist_comm]
  have hlocal (x : M) (hx : x ∈ S) :
      ENNReal.ofReal v ≤ g.volumeMeasure (g.ball x δ) ∧
        IsCompact (closure (g.ball x (2 * δ))) := by
    obtain ⟨N, hN, hcenter⟩ := K.pointwise_center_cover x hx.1
    have hsmall : N.epsilon ≤ (1 / 200 : ℝ) := by
      rw [K.neck_epsilon N hN]
      exact K.epsilon_le_threshold.trans K.epsilon_threshold_le_one_two_hundred
    have hR : 0 < D.scalarCurvature x := by
      simpa only [hD N hN, hcenter] using N.scalar_center_pos
    have hscale : B ^ (-1 / 2 : ℝ) ≤ N.scale := by
      rw [N.scale_eq_scalar, hD N hN, hcenter]
      exact Real.rpow_le_rpow_of_nonpos hR hx.2 (by norm_num)
    have hδscale : δ ≤ N.scale / 8 := by dsimp only [δ]; linarith [N.scale_pos]
    have htwo : 2 * δ ≤ N.scale / 8 := by dsimp only [δ]; linarith
    have hinv : 1 ≤ N.epsilon⁻¹ := (one_le_inv₀ N.epsilon_pos).mpr (by
      linarith [N.epsilon_lt_half])
    have hradius : 2 * δ ≤ N.scale * N.epsilon⁻¹ / 8 := by
      nlinarith [mul_le_mul_of_nonneg_left hinv N.scale_pos.le]
    constructor
    · simpa only [hcenter] using ordinary_neck_center_ball_volume_lower N hsmall hδ hδscale
    · have hc := (N.precompact_ball_of_central_sphere N.center_on_central_sphere).1
      rw [hcenter] at hc
      apply hc.of_isClosed_subset isClosed_closure
      apply closure_mono
      intro y hy
      exact hy.trans_le (ENNReal.ofReal_le_ofReal hradius)
  obtain ⟨F, hFS, _hcard, _hsep, hcover⟩ :=
    Poincare.exists_finset_cover_of_separated_card_le S
      (ENNReal.ofReal_pos.mpr (show 0 < 2 * δ by positivity))
      ⌈(g.volumeMeasure univ).toReal / v⌉₊ (by
        intro F hFS hsep
        have hbound := Poincare.MeasureTheory.card_le_measure_div_of_separated_balls
          g.volumeMeasure F (r := ENNReal.ofReal δ) (U := univ) hv hfinite
          (by
            intro x hx y hy hxy
            rw [← ENNReal.ofReal_add hδ.le hδ.le,
              show δ + δ = 2 * δ by ring]
            exact hsep hx hy hxy)
          (fun _ _ => subset_univ _) (by
            intro x hx
            rw [hball]
            exact (hlocal x (hFS hx)).1)
        exact_mod_cast hbound.trans (Nat.le_ceil ((g.volumeMeasure univ).toReal / v)))
  refine ⟨⋃ x ∈ F, closure (g.ball x (2 * δ)),
    F.finite_toSet.isCompact_biUnion (fun x hx => (hlocal x (hFS hx)).2), ?_⟩
  intro x hx
  obtain ⟨y, hy, hxy⟩ := hcover x hx
  apply mem_iUnion₂.mpr
  refine ⟨y, hy, subset_closure ?_⟩
  change g.edist y x < ENNReal.ofReal (2 * δ)
  change g.edist x y < ENNReal.ofReal (2 * δ) at hxy
  simpa only [RiemannianMetric.edist, Manifold.riemannianEDist_comm] using hxy




theorem exists_scalar_gt_of_neck_cover_noncompact_closure
    (K : NeckOnlyCover g) (D : LeviCivitaData g)
    (hD : ∀ N ∈ K.necks, N.connection = D)
    (hfinite : g.volumeMeasure univ ≠ ⊤) (hcompact : ¬ IsCompact (closure K.X))
    (B : ℝ) : ∃ x ∈ K.X, B < D.scalarCurvature x := by
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
  by_contra! hbound
  obtain ⟨C, hC, hsub⟩ := exists_compact_bounded_scalar_neck_cover K D hD hfinite
    (show 0 < max B 1 from lt_of_lt_of_le zero_lt_one (le_max_right _ _))
  apply hcompact
  apply hC.of_isClosed_subset isClosed_closure
  apply closure_minimal _ hC.isClosed
  intro x hx
  exact hsub ⟨hx, (hbound x hx).trans (le_max_left _ _)⟩

end PoincareConjecture.M28
