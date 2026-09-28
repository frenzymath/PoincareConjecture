import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Metric.Construction.MetricPullback









set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u v

namespace PoincareConjecture.MetricSurgery

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) Y]
  [IsManifold (𝓡 3) ∞ X] [IsManifold (𝓡 3) ∞ Y]

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "TX" => TangentSpace (𝓡 3) (M := X)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in

noncomputable def weightedPullbackMetric (g : RiemannianMetric 3 Y)
    (h : RiemannianMetric 3 X) (f : X → Y) (a : X → ℝ) (U : Set X)
    (hU : IsOpen U) (ha : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ a)
    (hab : ∀ x, 0 ≤ a x ∧ a x ≤ 1) (hsupport : tsupport a ⊆ U)
    (hf : ∀ x ∈ U, ContMDiffAt (𝓡 3) (𝓡 3) ∞ f x)
    (hD : ∀ x ∈ U, Function.Bijective (mfderiv (𝓡 3) (𝓡 3) f x)) :
    RiemannianMetric 3 X where
  inner x := a x • metricPullbackForm g f x + (1 - a x) • h.inner x
  symm x v w := by
    change a x * metricPullbackForm g f x v w + (1 - a x) * h.inner x v w =
      a x * metricPullbackForm g f x w v + (1 - a x) * h.inner x w v
    rw [metricPullbackForm_apply, metricPullbackForm_apply, g.symm, h.symm]
  pos x v hv := by
    change 0 < a x * metricPullbackForm g f x v v + (1 - a x) * h.inner x v v
    by_cases hx : (1 / 2 : ℝ) ≤ a x
    · have ha' : 0 < a x := by linarith
      have hxU : x ∈ U := hsupport (subset_tsupport a ha'.ne')
      have hpos : 0 < metricPullbackForm g f x v v := g.pos (f x) _ (by
        intro hz
        apply hv
        apply (hD x hxU).1
        change (mfderiv (𝓡 3) (𝓡 3) f x : E →L[ℝ] E) v =
          (mfderiv (𝓡 3) (𝓡 3) f x : E →L[ℝ] E) 0
        rw [map_zero]
        exact hz)
      exact add_pos_of_pos_of_nonneg (mul_pos ha' hpos)
        (mul_nonneg (sub_nonneg.mpr (hab x).2) (metric_inner_nonneg h x v))
    · exact add_pos_of_nonneg_of_pos
        (mul_nonneg (hab x).1 (metricPullbackForm_nonneg g f x v))
        (mul_pos (by linarith) (h.pos x v hv))
  isVonNBounded x := by
    by_cases hx : (1 / 2 : ℝ) ≤ a x
    · have ha' : 0 < a x := by linarith
      have hxU : x ∈ U := hsupport (subset_tsupport a ha'.ne')
      let D : E →L[ℝ] E := mfderiv (𝓡 3) (𝓡 3) f x
      let e : E ≃L[ℝ] E :=
        (LinearEquiv.ofBijective D.toLinearMap (hD x hxU)).toContinuousLinearEquiv
      let ref := positiveScaling g (fun _ => 1 / 2) contMDiff_const (by
        intro _
        norm_num)
      refine ((ref.isVonNBounded (f x)).image e.symm.toContinuousLinearMap).subset ?_
      intro v hv
      refine ⟨e v, ?_, e.symm_apply_apply v⟩
      change (1 / 2 : ℝ) * metricPullbackForm g f x v v < 1
      change a x * metricPullbackForm g f x v v + (1 - a x) * h.inner x v v < 1 at hv
      have hp := mul_nonneg (sub_nonneg.mpr hx) (metricPullbackForm_nonneg g f x v)
      have hh := mul_nonneg (sub_nonneg.mpr (hab x).2) (metric_inner_nonneg h x v)
      nlinarith
    · let ref := positiveScaling h (fun _ => 1 / 2) contMDiff_const (by
        intro _
        norm_num)
      refine (ref.isVonNBounded x).subset ?_
      intro v hv
      change (1 / 2 : ℝ) * h.inner x v v < 1
      change a x * metricPullbackForm g f x v v + (1 - a x) * h.inner x v v < 1 at hv
      have hp := mul_nonneg (hab x).1 (metricPullbackForm_nonneg g f x v)
      have hh := mul_nonneg (by linarith : 0 ≤ 1 / 2 - a x) (metric_inner_nonneg h x v)
      nlinarith
  contMDiff := by
    have hP : ContMDiffOn (𝓡 3) ((𝓡 3).prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
        (fun x => Bundle.TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) x (metricPullbackForm g f x)) U :=
      fun x hx => (metricPullbackForm_contMDiffAt g (hf x hx)).contMDiffWithinAt
    exact (ha.contMDiffOn.smul_section_of_tsupport hU hsupport hP).add_section
      ((contMDiff_const.sub ha).smul_section h.contMDiff)

theorem weightedPullbackMetric_inner (g : RiemannianMetric 3 Y)
    (h : RiemannianMetric 3 X) (f : X → Y) (a : X → ℝ) (U : Set X)
    (hU : IsOpen U) (ha : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ a)
    (hab : ∀ x, 0 ≤ a x ∧ a x ≤ 1) (hsupport : tsupport a ⊆ U)
    (hf : ∀ x ∈ U, ContMDiffAt (𝓡 3) (𝓡 3) ∞ f x)
    (hD : ∀ x ∈ U, Function.Bijective (mfderiv (𝓡 3) (𝓡 3) f x))
    (x : X) (v w : TX x) :
    (weightedPullbackMetric g h f a U hU ha hab hsupport hf hD).inner x v w =
      a x * metricPullbackForm g f x v w + (1 - a x) * h.inner x v w := rfl

end PoincareConjecture.MetricSurgery
