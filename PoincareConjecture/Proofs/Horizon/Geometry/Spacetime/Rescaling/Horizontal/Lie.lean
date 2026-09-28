import PoincareConjecture.Proofs.Horizon.Geometry.Spacetime.Rescaling.Horizontal.Basic
import PoincareConjecture.Proofs.Horizon.Geometry.Spacetime.Rescaling.HorizontalCalculus










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology

universe u

open PoincareConjecture.Homothety

namespace PoincareConjecture.ParabolicRescaling

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  {A : AdaptedMetricAtlas n X} {R : GeneralizedFlowCarrierConclusion A}
  {Q : ℝ} {hQ : 0 < Q} {a : ℝ}

theorem parabolic_lie_on_fields
    (U : Set R.spacetime.Point) (hU : IsOpen U)
    (V W : HorizontalSection R.spacetime)
    (hV : IsSmoothHorizontalSectionOn R.spacetime V U)
    (hW : IsSmoothHorizontalSectionOn R.spacetime W U)
    (p : R.spacetime.Point) (hp : p ∈ U) :
    horizontalMetricLieDerivativeOnFields (spacetimeRescaling R Q hQ a).realization.spacetime
      (parabolicHorizontalSection (spacetimeRescaling R Q hQ a) V)
      (parabolicHorizontalSection (spacetimeRescaling R Q hQ a) W) p =
        horizontalMetricLieDerivativeOnFields R.spacetime V W p := by
  let : ChartedSpace (ModelProd (EuclideanHalfSpace 1) (EuclideanSpace ℝ (Fin n)))
      R.spacetime.Point := R.spacetime.chartedSpace
  let : IsManifold (spacetimeModel n) ∞ R.spacetime.Point := R.spacetime.isManifold
  let P := spacetimeRescaling R Q hQ a
  have hpair := horizontalMetric_inner_mdifferentiableAt V W p
    ((hV.contMDiffAt (hU.mem_nhds hp)).mdifferentiableAt (by simp))
    ((hW.contMDiffAt (hU.mem_nhds hp)).mdifferentiableAt (by simp))
  have hmetric : (fun q : R.spacetime.Point ↦ P.realization.spacetime.horizontalMetric.inner q
      (parabolicHorizontalSection P V q) (parabolicHorizontalSection P W q)) =
      (fun q ↦ Q * R.spacetime.horizontalMetric.inner q (V q) (W q)) := by
    funext q
    exact P.metric_eq q (V q) (W q)
  unfold horizontalMetricLieDerivativeOnFields
  rw [hmetric, parabolic_timeBracket, parabolic_timeBracket]
  change mvfderiv (spacetimeModel n)
      (fun q : R.spacetime.Point ↦ Q * R.spacetime.horizontalMetric.inner q (V q) (W q)) p
      ((1 / Q : ℝ) • R.spacetime.timeVector p) -
    P.realization.spacetime.horizontalMetric.inner p
      ((1 / Q : ℝ) • P.horizontal p (horizontalTimeBracket R.spacetime V p))
      (P.horizontal p (W p)) -
    P.realization.spacetime.horizontalMetric.inner p (P.horizontal p (V p))
      ((1 / Q : ℝ) • P.horizontal p (horizontalTimeBracket R.spacetime W p)) = _
  rw [mvfderiv_fun_mul mdifferentiableAt_const hpair]
  simp only [mvfderiv_const, smul_zero, add_zero, map_smul, smul_apply, smul_eq_mul,
    P.metric_eq]
  field_simp [hQ.ne']

theorem parabolic_horizontal_lie
    (D : LeafwiseLeviCivitaFamily R.spacetime R.slices)
    (D' : LeafwiseLeviCivitaFamily (spacetimeRescaling R Q hQ a).realization.spacetime
      (spacetimeRescaling R Q hQ a).realization.slices)
    (hD : HorizontalRicciCalculus D) (hD' : HorizontalRicciCalculus D')
    (p : R.spacetime.Point) (v w : R.spacetime.Horizontal p) :
    horizontalMetricLieDerivative (spacetimeRescaling R Q hQ a).realization.spacetime p
      ((spacetimeRescaling R Q hQ a).horizontal p v)
      ((spacetimeRescaling R Q hQ a).horizontal p w) =
        horizontalMetricLieDerivative R.spacetime p v w := by
  let P := spacetimeRescaling R Q hQ a
  let V : HorizontalSection R.spacetime := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v
  let W : HorizontalSection R.spacetime := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) w
  obtain ⟨U, hUp, hV⟩ := FiberBundle.exists_contMDiffOn_extend (k := ∞)
    (spacetimeModel n) (EuclideanSpace ℝ (Fin n)) v
  obtain ⟨U', hU'p, hW⟩ := FiberBundle.exists_contMDiffOn_extend (k := ∞)
    (spacetimeModel n) (EuclideanSpace ℝ (Fin n)) w
  obtain ⟨O, hOU, hO, hp⟩ := mem_nhds_iff.mp (Filter.inter_mem hUp hU'p)
  have hVO : IsSmoothHorizontalSectionOn R.spacetime V O :=
    hV.mono (fun _ hx ↦ (hOU hx).1)
  have hWO : IsSmoothHorizontalSectionOn R.spacetime W O :=
    hW.mono (fun _ hx ↦ (hOU hx).2)
  calc
    _ = horizontalMetricLieDerivative P.realization.spacetime p
        (P.horizontal p (V p)) (P.horizontal p (W p)) := by
      simp only [P, V, W, FiberBundle.extend_apply_self]
    _ = horizontalMetricLieDerivativeOnFields P.realization.spacetime
        (parabolicHorizontalSection P V) (parabolicHorizontalSection P W) p :=
      hD'.lie_on_fields O hO _ _
        ((parabolic_section_smooth_iff V O).2 hVO)
        ((parabolic_section_smooth_iff W O).2 hWO) p hp
    _ = horizontalMetricLieDerivativeOnFields R.spacetime V W p :=
      parabolic_lie_on_fields O hO V W hVO hWO p hp
    _ = horizontalMetricLieDerivative R.spacetime p (V p) (W p) :=
      (hD.lie_on_fields O hO V W hVO hWO p hp).symm
    _ = _ := by simp only [V, W, FiberBundle.extend_apply_self]

end PoincareConjecture.ParabolicRescaling
