import PoincareConjecture.Proofs.M14.Sec6_2_SurfaceEulerMomentum
import PoincareConjecture.Proofs.M14.Sec6_2_GaugeMomentum
import PoincareConjecture.Proofs.M14.Sec6_2_GaugeMomentumPair
import PoincareConjecture.Proofs.M14.Sec6_2_BackwardTestField
import PoincareConjecture.Proofs.M14.Sec6_2_MinimizerSmooth
import PoincareConjecture.Proofs.M14.Sec6_2_PullbackCongruence
import PoincareConjecture.Statements.M14PathCalculus










set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₁ τ₂ : ℝ} {x y : G.Point} {p : M14BackwardPath G T τ₁ τ₂ x y}

private theorem horizontal_heq_of_val_eq {q r : G.Point} (h : q = r)
    {a : G.Horizontal q} {b : G.Horizontal r} (hab : a.val = b.val) : HEq a b := by
  cases h
  exact heq_of_eq (Subtype.ext hab)

private theorem horizontal_inner_heq {q r : G.Point} (h : q = r)
    {a b : G.Horizontal q} {c d : G.Horizontal r} (ha : HEq a c) (hb : HEq b d) :
    G.spacetime.horizontalMetric.inner q a b = G.spacetime.horizontalMetric.inner r c d := by
  cases h
  cases ha
  cases hb
  rfl

private theorem horizontal_scalar_heq {q r : G.Point} (h : q = r)
    {a : G.Horizontal q} {b : G.Horizontal r} (ha : HEq a b) :
    M14HorizontalScalarDifferential G q a.val = M14HorizontalScalarDifferential G r b.val := by
  cases h
  cases ha
  rfl

private theorem horizontal_ricci_heq {q r : G.Point} (h : q = r)
    {a b : G.Horizontal q} {c d : G.Horizontal r} (ha : HEq a c) (hb : HEq b d) :
    horizontalRicci G.leafwise q a b = horizontalRicci G.leafwise r c d := by
  cases h
  cases ha
  cases hb
  rfl




theorem eulerResidual_eq_zero_of_minimizing
    (hCoordinates : M12MetricPredecessors.{0} n) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (hmin : M14IsMinimizing p)
    (E : M14PullbackExtension G p.curve (Ioo τ₁ τ₂) p.horizontal_velocity)
    {s : ℝ} (hs : s ∈ Ioo τ₁ τ₂) (W : G.Horizontal (p.curve s)) :
    M14EulerResidual G p E s W = 0 := by
  obtain ⟨b, U, lift, hU, hsU, hlift, hright, η, hη, hsupp, hsrc, hvalue⟩ :=
    exists_supportedBackwardGaugeTest_at p hs W
  have hrightSupport : ∀ t ∈ tsupport η,
      (G.gaugeCover.cylinder b).toSpacetime (lift (p.curve t)) = p.curve t :=
    fun t ht => hright _ (hsrc t ht)
  obtain ⟨r, hr, hshift⟩ := exists_supportedBackwardGauge_radius p b lift η hU hlift hη hsupp hsrc
  let P := Ioo (-r) r
  have hP : IsOpen P := isOpen_Ioo
  have hzero : (0 : ℝ) ∈ P := ⟨neg_lt_zero.mpr hr, hr⟩
  let α := fun z : ℝ × ℝ => supportedBackwardGaugeFamily p b lift η z.2 z.1
  have hα : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) (spacetimeModel n) ∞ α
      (Ioo τ₁ τ₂ ×ˢ P) :=
    supportedBackwardGaugeFamily_joint_contMDiffOn p b lift η
      (minimizing_curve_contMDiffOn p hM12 hmin) hU hlift hright hη hsrc hshift
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
  let J := Ioo τ₁ τ₂ ∩ p.curve ⁻¹' U
  have hJ : IsOpen J := p.curve_regular.continuousOn.isOpen_inter_preimage isOpen_Ioo hU
  have hsJ : s ∈ J := ⟨hs, hsU⟩
  obtain ⟨a, c, _, hacN, hacJ⟩ := exists_Icc_mem_subset_of_mem_nhds (hJ.mem_nhds hsJ)
  have hsac := Icc_mem_nhds_iff.mp hacN
  obtain ⟨d, hcoordinate, hdensity⟩ := minimizing_gauge_momentum_density_derivatives
    p b lift η (lift (p.curve s)).2 hM12 hmin hU hlift hright hJ inter_subset_left
      (fun _ ht => ht.2) (hsac.1.trans hsac.2) hacJ hsac hη
  have hmomentum : HasDerivAt
      (fun t => 2 * Real.sqrt t * G.spacetime.horizontalMetric.inner (α (t, 0))
        (surfaceHorizontalFst α t 0) (surfaceHorizontalSnd α t 0)) d s := by
    apply hcoordinate.congr_of_eventuallyEq
    filter_upwards [hJ.mem_nhds hsJ] with t ht
    exact supportedBackwardGauge_weightedPair p b lift η (lift (p.curve s)).2
      hU hlift hright hsrc ht.1 ht.2
  change HasDerivAt
    (fun v => M14RawLIntegrand G (fun t => α (t, v)) (fun t => surfaceHorizontalFst α t v) s)
    d 0 at hdensity
  have heuler := surfaceEulerPair_eq_zero hCoordinates hM12 isOpen_Ioo hP hα hclock hs hzero
    (p.tau_nonneg.trans_lt hs.1) EX hmomentum hdensity
  have hpoint : α (s, 0) = p.curve s := (congrFun hbase s).symm
  have hX := (hvelocity s hs).symm
  have hDX := (horizontalCovariantDerivative_congr E hbase hvelocity s).symm
  have hZval : (surfaceHorizontalSnd α s 0).val = W.val := by
    rw [surfaceHorizontalSnd_val isOpen_Ioo hP hα hclock hs hzero]
    exact (supportedBackwardGaugeFamily_parameter_mfderiv p b lift η hrightSupport s).trans hvalue
  have hZ := horizontal_heq_of_val_eq hpoint hZval
  rw [horizontal_inner_heq hpoint hDX hZ, horizontal_scalar_heq hpoint hZ,
    horizontal_inner_heq hpoint hX hZ, horizontal_ricci_heq hpoint hX hZ] at heuler
  exact heuler




theorem minimizerEulerStatement (hCoordinates : M12MetricPredecessors.{0} n)
    (hM12 : GeneralizedRicciGaugeTheory.{u} n) : M14MinimizerEulerStatement G := by
  intro T τ₁ τ₂ x y p hmin
  obtain ⟨E⟩ := exists_minimizing_velocity_extension p hM12 hmin
  exact ⟨E, fun s hs W => eulerResidual_eq_zero_of_minimizing hCoordinates hM12 hmin E hs W⟩

end PoincareConjecture.M14
