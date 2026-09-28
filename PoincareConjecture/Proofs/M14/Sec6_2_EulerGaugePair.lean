import PoincareConjecture.Proofs.M14.Sec6_2_EulerSurfaceDerivative
import PoincareConjecture.Proofs.M14.Sec6_2_ExtendedPathRegularity
import PoincareConjecture.Proofs.M14.Sec6_2_GaugeMomentumPair
import PoincareConjecture.Proofs.M14.Sec6_2_PullbackCongruence











set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}

private theorem horizontal_heq_of_val_eq {q r : G.Point} (h : q = r)
    {a : G.Horizontal q} {b : G.Horizontal r} (hab : a.val = b.val) : HEq a b := by
  cases h
  exact heq_of_eq (Subtype.ext hab)

private theorem eulerPair_heq {q r : G.Point} (h : q = r)
    {A V W : G.Horizontal q} {A' V' W' : G.Horizontal r}
    (hA : HEq A A') (hV : HEq V V') (hW : HEq W W') (s : ℝ) :
    G.spacetime.horizontalMetric.inner q A W -
        (1 / 2 : ℝ) * M14HorizontalScalarDifferential G q W.val +
        (1 / (2 * s) : ℝ) * G.spacetime.horizontalMetric.inner q V W +
        2 * horizontalRicci G.leafwise q V W =
      G.spacetime.horizontalMetric.inner r A' W' -
        (1 / 2 : ℝ) * M14HorizontalScalarDifferential G r W'.val +
        (1 / (2 * s) : ℝ) * G.spacetime.horizontalMetric.inner r V' W' +
        2 * horizontalRicci G.leafwise r V' W' := by
  cases h
  cases hA
  cases hV
  cases hW
  rfl

variable {T τ₁ τ₂ : ℝ} {x y : G.Point} (p : M14BackwardPath G T τ₁ τ₂ x y)
  (b : G.gaugeCover.index)
  (lift : G.Point → (G.timeIntervals.interval (G.gaugeCover.interval b)).Point ×
    G.gaugeCover.spatial b) (η : ℝ → EuclideanSpace ℝ (Fin n))




theorem hasDerivAt_supportedBackwardGauge_pair_of_euler (x₀ : G.gaugeCover.spatial b)
    (hCoordinates : M12MetricPredecessors.{0} n) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (E : M14PullbackExtension G p.curve (Ioo τ₁ τ₂) p.horizontal_velocity)
    {U : Set G.Point} (hU : IsOpen U)
    (hlift : ContMDiffOn (spacetimeModel n) (spacetimeModel n) ∞ lift U)
    (hright : ∀ q ∈ U, (G.gaugeCover.cylinder b).toSpacetime (lift q) = q)
    (hη : ContDiff ℝ ∞ η) (hsupp : tsupport η ⊆ Ioo τ₁ τ₂)
    (hsrcSupport : ∀ t ∈ tsupport η, p.curve t ∈ U)
    {s d : ℝ} (hs : s ∈ Ioo τ₁ τ₂) (hsrc : p.curve s ∈ U)
    (heuler : ∀ W : G.Horizontal (p.curve s), M14EulerResidual G p E s W = 0)
    (hdensity : HasDerivAt
      (fun v => M14RawLIntegrand G (supportedBackwardGaugeFamily p b lift η v)
        (projectedCurveVelocity G (supportedBackwardGaugeFamily p b lift η v)) s) d 0) :
    HasDerivAt (fun t =>
      backwardMetricCoefficient (G.gaugeCover.spatial b) (G.gaugeCover.metric b).metric T x₀
        (t, (lift (p.curve t)).2.val) (deriv (fun r => (lift (p.curve r)).2.val) t) (η t)) d s := by
  have hrightSupport : ∀ t ∈ tsupport η,
      (G.gaugeCover.cylinder b).toSpacetime (lift (p.curve t)) = p.curve t :=
    fun t ht => hright _ (hsrcSupport t ht)
  obtain ⟨r, hr, hshift⟩ :=
    exists_supportedBackwardGauge_radius p b lift η hU hlift hη hsupp hsrcSupport
  let P := Ioo (-r) r
  have hP : IsOpen P := isOpen_Ioo
  have hzero : (0 : ℝ) ∈ P := ⟨neg_lt_zero.mpr hr, hr⟩
  let α := fun z : ℝ × ℝ => supportedBackwardGaugeFamily p b lift η z.2 z.1
  have hα : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) (spacetimeModel n) ∞ α
      (Ioo τ₁ τ₂ ×ˢ P) :=
    supportedBackwardGaugeFamily_joint_contMDiffOn p b lift η
      (backwardPath_contMDiffOn_of_velocity_extension p E) hU hlift hright hη hsrcSupport hshift
  have hclock : ∀ z ∈ Ioo τ₁ τ₂ ×ˢ P, G.spacetime.timeFunction (α z) = T - z.1 := by
    intro z hz
    exact supportedBackwardGaugeFamily_time p b lift η
      (fun t ht => ((G.gaugeCover.cylinder b).time_eq (lift (p.curve t))).symm.trans
        (congrArg G.spacetime.timeFunction (hrightSupport t ht))) (Ioo_subset_Icc_self hz.1) z.2
  have hbase : p.curve = fun t => α (t, 0) :=
    (funext (supportedBackwardGaugeFamily_at_zero p b lift η hrightSupport)).symm
  have hvelocity : ∀ t ∈ Ioo τ₁ τ₂,
      HEq (p.horizontal_velocity t) (surfaceHorizontalFst α t 0) := by
    intro t ht
    apply horizontal_heq_of_val_eq (congrFun hbase t)
    exact (congrArg Subtype.val (backwardPath_velocity_eq_projected p ht)).trans
      (congrArg (fun γ : ℝ → G.Point => (projectedCurveVelocity G γ t).val) hbase)
  let EX := pullbackExtensionCongr E hbase hvelocity
  obtain ⟨W, hW⟩ : ∃ W : G.Horizontal (p.curve s), HEq W (surfaceHorizontalSnd α s 0) := by
    rw [congrFun hbase s]
    exact ⟨surfaceHorizontalSnd α s 0, HEq.rfl⟩
  have hpairEuler := eulerPair_heq (congrFun hbase s)
    (horizontalCovariantDerivative_congr E hbase hvelocity s) (hvelocity s hs) hW s
  change M14EulerResidual G p E s W = _ at hpairEuler
  have hpair := hasDerivAt_surfaceWeightedPair_of_euler hCoordinates hM12 isOpen_Ioo hP
    hα hclock hs hzero (p.tau_nonneg.trans_lt hs.1) EX
      (hpairEuler.symm.trans (heuler W)) hdensity
  apply hpair.congr_of_eventuallyEq
  have hp := (p.curve_regular s hs).contMDiffAt (isOpen_Ioo.mem_nhds hs)
  filter_upwards [isOpen_Ioo.mem_nhds hs,
    hp.continuousAt.preimage_mem_nhds (hU.mem_nhds hsrc)] with t ht htU
  exact (supportedBackwardGauge_weightedPair p b lift η x₀
    hU hlift hright hsrcSupport ht htU).symm

end PoincareConjecture.M14
