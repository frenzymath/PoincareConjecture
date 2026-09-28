import PoincareConjecture.Proofs.M14.Mathlib.OpenSubsetCurveShift
import PoincareConjecture.Proofs.M14.Sec6_2_PotentialCoefficient
import PoincareConjecture.Proofs.M14.Sec6_2_GaugeCoordinates
import PoincareConjecture.Proofs.M14.Sec6_1_GaugePerturbation










set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology intervalIntegral

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₁ τ₂ : ℝ} {x y : G.Point} (p : M14BackwardPath G T τ₁ τ₂ x y)
  (b : G.gaugeCover.index)
  (lift : G.Point → (G.timeIntervals.interval (G.gaugeCover.interval b)).Point ×
    G.gaugeCover.spatial b) (η : ℝ → EuclideanSpace ℝ (Fin n))
  (x₀ : G.gaugeCover.spatial b)




theorem backwardGaugeFamily_quadraticDensity {U : Set G.Point} (hU : IsOpen U)
    (hlift : ContMDiffOn (spacetimeModel n) (spacetimeModel n) ∞ lift U)
    (hright : ∀ q ∈ U, (G.gaugeCover.cylinder b).toSpacetime (lift q) = q)
    (hη : ContDiff ℝ ∞ η) {t v : ℝ} (ht : t ∈ Ioo τ₁ τ₂) (hsrc : p.curve t ∈ U)
    (hshift : (lift (p.curve t)).2.val + v • η t ∈ G.gaugeCover.spatial b) :
    M14RawLIntegrand G (backwardGaugeFamily p b lift η v)
      (projectedCurveVelocity G (backwardGaugeFamily p b lift η v)) t =
      backwardMetricCoefficient (G.gaugeCover.spatial b) (G.gaugeCover.metric b).metric T x₀
        (t, (lift (p.curve t)).2.val + v • η t)
        (deriv (fun s => (lift (p.curve s)).2.val) t + v • deriv η t)
        (deriv (fun s => (lift (p.curve s)).2.val) t + v • deriv η t) / 2 +
      backwardPotentialCoefficient b (fun s => (lift (p.curve s)).1) x₀
        (t, (lift (p.curve t)).2.val + v • η t) := by
  have hp := (p.curve_regular t ht).contMDiffAt (isOpen_Ioo.mem_nhds ht)
  have hL := (((hlift _ hsrc).contMDiffAt (hU.mem_nhds hsrc)).of_le (by simp)).comp t hp
  have hv : ContMDiff (𝓡 n) (𝓡 n) ∞
      (Subtype.val : G.gaugeCover.spatial b → EuclideanSpace ℝ (Fin n)) := contMDiff_subtype_val
  have hu := ((hv.of_le (by simp)).contMDiffAt.comp t hL.snd).contDiffAt
  have hS := (G.gaugeCover.spatial b).affineShift_curve_contMDiffAt
    (fun s => (lift (p.curve s)).2) η hL.snd (hη.contDiffAt.of_le (by simp)) hshift
  have hd := (G.gaugeCover.spatial b).affineShift_curve_hasDerivAt
    (fun s => (lift (p.curve s)).2) η (hu.differentiableAt (by simp))
      (hη.differentiable (by simp) t) hshift
  have hclock := gaugeLift_time_eq p b lift hright (Ioo_subset_Icc_self ht) hsrc
  have hdensity := gaugeCurve_quadraticDensity b (fun s => (lift (p.curve s)).1) x₀
    (fun s => (G.gaugeCover.spatial b).affineShift (lift (p.curve s)).2 (v • η s))
    (hL.fst.mdifferentiableAt (by simp)) (hS.mdifferentiableAt (by simp)) hclock
  change M14RawLIntegrand G (backwardGaugeFamily p b lift η v)
    (projectedCurveVelocity G (backwardGaugeFamily p b lift η v)) t = _ at hdensity
  simpa only [hd.deriv,
    (G.gaugeCover.spatial b).affineShift_val hshift] using hdensity




theorem middleAction_supportedBackwardGauge_eq_quadratic
    {U : Set G.Point} (hU : IsOpen U)
    (hlift : ContMDiffOn (spacetimeModel n) (spacetimeModel n) ∞ lift U)
    (hright : ∀ q ∈ U, (G.gaugeCover.cylinder b).toSpacetime (lift q) = q)
    {a c : ℝ} (ha : τ₁ < a) (hac : a < c) (hc : c < τ₂)
    (hη : ContDiff ℝ ∞ η) (hsrc : ∀ t ∈ Icc a c, p.curve t ∈ U) {v : ℝ}
    (hshift : ∀ t ∈ Icc a c,
      (lift (p.curve t)).2.val + v • η t ∈ G.gaugeCover.spatial b) :
    (∫ t in a..c, M14RawLIntegrand G (supportedBackwardGaugeFamily p b lift η v)
      (projectedCurveVelocity G (supportedBackwardGaugeFamily p b lift η v)) t) =
      ∫ t in a..c,
        backwardMetricCoefficient (G.gaugeCover.spatial b) (G.gaugeCover.metric b).metric T x₀
          (t, (lift (p.curve t)).2.val + v • η t)
          (derivWithin (fun s => (lift (p.curve s)).2.val) (Icc a c) t + v • deriv η t)
          (derivWithin (fun s => (lift (p.curve s)).2.val) (Icc a c) t + v • deriv η t) / 2 +
        backwardPotentialCoefficient b (fun s => (lift (p.curve s)).1) x₀
          (t, (lift (p.curve t)).2.val + v • η t) := by
  apply intervalIntegral.integral_congr_Ioo_of_le hac.le
  intro t ht
  have htp : t ∈ Ioo τ₁ τ₂ := ⟨ha.trans ht.1, ht.2.trans hc⟩
  have htc := Ioo_subset_Icc_self ht
  have hp := (p.curve_regular t htp).contMDiffAt (isOpen_Ioo.mem_nhds htp)
  have heq : supportedBackwardGaugeFamily p b lift η v =ᶠ[𝓝 t]
      backwardGaugeFamily p b lift η v := by
    filter_upwards [hp.continuousAt.preimage_mem_nhds (hU.mem_nhds (hsrc t htc))] with s hs
    exact supportedBackwardGaugeFamily_eq_gauge p b lift η (hright _ hs) v
  rw [rawLIntegrand_projectedVelocity_congr heq,
    backwardGaugeFamily_quadraticDensity p b lift η x₀ hU hlift hright hη htp
      (hsrc t htc) (hshift t htc)]
  dsimp only
  rw [derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]




theorem exists_quadratic_local_minimum
    (hM12 : GeneralizedRicciGaugeTheory.{u} n) (hmin : M14IsMinimizing p)
    {U : Set G.Point} (hU : IsOpen U)
    (hlift : ContMDiffOn (spacetimeModel n) (spacetimeModel n) ∞ lift U)
    (hright : ∀ q ∈ U, (G.gaugeCover.cylinder b).toSpacetime (lift q) = q)
    {a c : ℝ} (ha : τ₁ < a) (hac : a < c) (hc : c < τ₂)
    (hη : ContDiff ℝ ∞ η) (hsupport : tsupport η ⊆ Ioo a c)
    (hsrc : ∀ t ∈ Icc a c, p.curve t ∈ U) :
    ∃ r : ℝ, 0 < r ∧
      (∀ t ∈ Icc a c, ∀ v ∈ Ioo (-r) r,
        (lift (p.curve t)).2.val + v • η t ∈ G.gaugeCover.spatial b) ∧
      IsLocalMin (fun v : ℝ => ∫ t in a..c,
        backwardMetricCoefficient (G.gaugeCover.spatial b) (G.gaugeCover.metric b).metric T x₀
          (t, (lift (p.curve t)).2.val + v • η t)
          (derivWithin (fun s => (lift (p.curve s)).2.val) (Icc a c) t + v • deriv η t)
          (derivWithin (fun s => (lift (p.curve s)).2.val) (Icc a c) t + v • deriv η t) / 2 +
        backwardPotentialCoefficient b (fun s => (lift (p.curve s)).1) x₀
          (t, (lift (p.curve t)).2.val + v • η t)) 0 := by
  have hsupp : tsupport η ⊆ Ioo τ₁ τ₂ :=
    fun _ ht => ⟨ha.trans (hsupport ht).1, (hsupport ht).2.trans hc⟩
  have hsource : ∀ t ∈ tsupport η, p.curve t ∈ U :=
    fun t ht => hsrc t (Ioo_subset_Icc_self (hsupport ht))
  obtain ⟨r, hr, hshift⟩ := exists_supportedBackwardGauge_radius p b lift η hU hlift hη
    hsupp hsource
  have hadm : ∀ t ∈ Icc a c, ∀ v ∈ Ioo (-r) r,
      (lift (p.curve t)).2.val + v • η t ∈ G.gaugeCover.spatial b := by
    intro t _ v hv
    by_cases ht : t ∈ tsupport η
    · exact hshift t ht v hv
    · simpa only [image_eq_zero_of_notMem_tsupport ht, smul_zero, add_zero] using
        (lift (p.curve t)).2.property
  refine ⟨r, hr, hadm, ?_⟩
  apply (isLocalMin_middleAction_supportedBackwardGauge p b lift η hM12 hmin hU hlift hright
    ha hac hc hη hsupport hsource).congr
  filter_upwards [Ioo_mem_nhds (neg_lt_zero.mpr hr) hr] with v hv
  exact middleAction_supportedBackwardGauge_eq_quadratic p b lift η x₀ hU hlift hright
    ha hac hc hη hsrc (fun t ht => hadm t ht v hv)

end PoincareConjecture.M14
