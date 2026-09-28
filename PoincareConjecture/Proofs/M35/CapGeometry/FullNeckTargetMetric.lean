import PoincareConjecture.Proofs.M35.Thm12_28.FullNeckMetricRealization









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.RiemannianMetric



theorem exists_normalized_chart_realization
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    (g : RiemannianMetric 3 M) (Q : ℝ) (hQ : 0 < Q) (c : M) :
    ∃ (gB : RiemannianMetric 3 (EuclideanSpace ℝ (Fin 3)))
      (V : Set (EuclideanSpace ℝ (Fin 3))),
      IsOpen V ∧ extChartAt (𝓡 3) c c ∈ V ∧ V ⊆ (extChartAt (𝓡 3) c).target ∧
        ∀ y ∈ V, gB.euclideanCoefficients y =
          Q • g.pullbackCoefficients (extChartAt (𝓡 3) c).symm y := by
  let phi := (extChartAt (𝓡 3) c).symm
  have hregular (y : EuclideanSpace ℝ (Fin 3))
      (hy : y ∈ (extChartAt (𝓡 3) c).target) :
      ContMDiffAt (𝓡 3) (𝓡 3) ∞ phi y :=
    (contMDiffOn_extChartAt_symm (n := ∞) c).contMDiffAt
      ((isOpen_extChartAt_target (I := 𝓡 3) c).mem_nhds hy)
  have hinvertible (y : EuclideanSpace ℝ (Fin 3))
      (hy : y ∈ (extChartAt (𝓡 3) c).target) :
      (mfderiv (𝓡 3) (𝓡 3) phi y).IsInvertible := by
    have h := isInvertible_mfderivWithin_extChartAt_symm hy
    simpa only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] using h
  obtain ⟨gB, _D, V, hV, hcV, hVU, hmetric⟩ := RiemannianMetric.exists_local_realization
    (isOpen_extChartAt_target (I := 𝓡 3) c) (mem_extChartAt_target c)
    (fun y => Q • g.pullbackCoefficients phi y)
    (fun y hy =>
      ((g.contDiffAt_pullbackCoefficients (hregular y hy)).const_smul Q).contDiffWithinAt)
    (fun y _ v w => congrArg (fun a : ℝ => Q * a) (g.symm (phi y) _ _))
    (fun y hy v hv => mul_pos hQ (g.pos (phi y) _ (fun hz => hv
      ((hinvertible y hy).injective
        (hz.trans (map_zero (mfderiv (𝓡 3) (𝓡 3) phi y)).symm)))))
  exact ⟨gB, V, hV, hcV, hVU, hmetric⟩

end PoincareConjecture.RiemannianMetric
