import PoincareLib.Geometry.RicciFlow.Surgery.GlobalSchedule.Event.EventTransportMetricJets

/-!
# Exact pullback identities on chart neighborhoods

Every identity here is local. Equality of maps on a neighborhood gives
equality of their totalized differentials at its center, and therefore of
their actual metric coefficient fields.
These are the chart identities for Morgan--Tian Definition 15.8,
pp. 361-362; see the explicit transport derivation in
`proof-work/tasks/M51/derivations/2026-09-24-event-transport.md`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT.M51EventTransport

local notation "V3" => EuclideanSpace ℝ (Fin 3)

variable {A C : GeneralizedSliceCarrier.{u}}

/-- Locally equal maps have equal metric pullback coefficients;
this supports Definition 15.8, pp. 361-362. -/
theorem pullbackCoefficients_congr
    (g : RiemannianMetric 3 A.carrier)
    {f h : V3 → A.carrier} {x : V3} (heq : f =ᶠ[𝓝 x] h) :
    g.pullbackCoefficients f x = g.pullbackCoefficients h x := by
  ext v w
  change g.inner (f x) (mfderiv (𝓡 3) (𝓡 3) f x v)
      (mfderiv (𝓡 3) (𝓡 3) f x w) =
    g.inner (h x) (mfderiv (𝓡 3) (𝓡 3) h x v)
      (mfderiv (𝓡 3) (𝓡 3) h x w)
  rw [heq.eq_of_nhds, heq.mfderiv_eq]

/-- Smooth coordinate composition gives the tensor pullback formula;
this supports Definition 15.8, pp. 361-362. -/
theorem pullbackCoefficients_comp
    (g : RiemannianMetric 3 A.carrier)
    {f : V3 → A.carrier} {a : V3 → V3} {x : V3}
    (hf : ContMDiffAt (𝓡 3) (𝓡 3) ∞ f (a x))
    (ha : ContDiffAt ℝ ∞ a x) :
    g.pullbackCoefficients (f ∘ a) x =
      (g.pullbackCoefficients f (a x)).bilinearComp
        (fderiv ℝ a x) (fderiv ℝ a x) := by
  have hderiv := mfderiv_comp x (hf.mdifferentiableAt (by simp))
    ((contMDiffAt_iff_contDiffAt.mpr ha).mdifferentiableAt (by simp))
  rw [mfderiv_eq_fderiv] at hderiv
  ext v w
  change g.inner (f (a x)) (mfderiv (𝓡 3) (𝓡 3) (f ∘ a) x v)
      (mfderiv (𝓡 3) (𝓡 3) (f ∘ a) x w) =
    g.inner (f (a x))
      (mfderiv (𝓡 3) (𝓡 3) f (a x) (fderiv ℝ a x v))
      (mfderiv (𝓡 3) (𝓡 3) f (a x) (fderiv ℝ a x w))
  rw [hderiv]
  rfl

/-- Metric pullback commutes with coefficient extraction;
this supports Definition 15.8, pp. 361-362. -/
theorem pullbackCoefficients_metric_pullback
    (g : RiemannianMetric 3 A.carrier)
    (e : Diffeomorph (𝓡 3) (𝓡 3) C.carrier A.carrier ∞)
    {h : V3 → C.carrier} {x : V3}
    (hh : ContMDiffAt (𝓡 3) (𝓡 3) ∞ h x) :
    (g.pullbackOfLocalDiffeomorph e e.isLocalDiffeomorph).pullbackCoefficients h x =
      g.pullbackCoefficients (e ∘ h) x := by
  have hderiv := mfderiv_comp x (e.mdifferentiable (by simp) _)
    (hh.mdifferentiableAt (by simp))
  ext v w
  change (g.pullbackOfLocalDiffeomorph e e.isLocalDiffeomorph).inner (h x)
      (mfderiv (𝓡 3) (𝓡 3) h x v) (mfderiv (𝓡 3) (𝓡 3) h x w) =
    g.inner (e (h x)) (mfderiv (𝓡 3) (𝓡 3) (e ∘ h) x v)
      (mfderiv (𝓡 3) (𝓡 3) (e ∘ h) x w)
  rw [RiemannianMetric.pullbackOfLocalDiffeomorph_inner, hderiv]
  rfl

/-- Inverse-chart factorization holds as a germ throughout the source overlap;
this supports Definition 15.8, pp. 361-362. -/
theorem chart_factor_eventuallyEq
    (q : A.carrier) {h : V3 → A.carrier} {x : V3}
    (hh : ContinuousAt h x) (hx : h x ∈ (extChartAt (𝓡 3) q).source) :
    ((extChartAt (𝓡 3) q).symm ∘ ((extChartAt (𝓡 3) q) ∘ h)) =ᶠ[𝓝 x] h := by
  filter_upwards [hh.eventually ((isOpen_extChartAt_source (I := 𝓡 3) q).mem_nhds hx)]
    with y hy
  exact (extChartAt (𝓡 3) q).left_inv hy

end PoincareMT.M51EventTransport
