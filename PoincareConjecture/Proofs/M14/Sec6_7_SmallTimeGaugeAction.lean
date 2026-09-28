import PoincareConjecture.Proofs.M14.Sec6_7_SmallTimeEnergy
import PoincareConjecture.Proofs.M14.Sec6_2_SquareCoefficients
import PoincareConjecture.Proofs.M14.Sec6_2_SquareGaugeEnergy










set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology intervalIntegral

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₁ τ₂ : ℝ} {x y : G.Point} (p : M14BackwardPath G T τ₁ τ₂ x y)
  (b : G.gaugeCover.index)
  (lift : G.Point → (G.timeIntervals.interval (G.gaugeCover.interval b)).Point ×
    G.gaugeCover.spatial b) (x₀ : G.gaugeCover.spatial b)




theorem squarePath_gauge_kinetic_eq {U : Set G.Point}
    (hlift : ContMDiffOn (spacetimeModel n) (spacetimeModel n) ∞ lift U)
    (hright : ∀ q ∈ U, (G.gaugeCover.cylinder b).toSpacetime (lift q) = q)
    (hsrc : ∀ s ∈ M14SqrtParameterInterval τ₁ τ₂, p.curve (s ^ 2) ∈ U)
    {s : ℝ} (hs : s ∈ Ioo (Real.sqrt τ₁) (Real.sqrt τ₂)) :
    squareMetricCoefficient (G.gaugeCover.spatial b) (G.gaugeCover.metric b).metric T x₀
      (s, (lift (p.curve (s ^ 2))).2.val)
      (deriv (fun r => (lift (p.curve (r ^ 2))).2.val) s)
      (deriv (fun r => (lift (p.curve (r ^ 2))).2.val) s) = pathSquareKinetic p s := by
  let θ := fun r => (lift (p.curve (r ^ 2))).1
  let u := fun r => (lift (p.curve (r ^ 2))).2
  have hLreg := (hlift.of_le (by simp : (1 : ℕ∞ω) ≤ ∞)).comp
    (squarePath_contMDiffOn p) (fun r hr => hsrc r (Ioo_subset_Icc_self hr))
  have htime := ((hLreg s hs).contMDiffAt (isOpen_Ioo.mem_nhds hs)).fst.mdifferentiableAt
    (by simp)
  have hspace := ((hLreg s hs).contMDiffAt (isOpen_Ioo.mem_nhds hs)).snd.mdifferentiableAt
    (by simp)
  have hbase : (fun r => p.curve (r ^ 2)) =ᶠ[𝓝 s]
      (fun r => (G.gaugeCover.cylinder b).toSpacetime (θ r, u r)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hs] with r hr
    exact (hright _ (hsrc r (Ioo_subset_Icc_self hr))).symm
  have hpoint : (G.gaugeCover.cylinder b).toSpacetime (θ s, u s) = p.curve (s ^ 2) :=
    hright _ (hsrc s (Ioo_subset_Icc_self hs))
  have hclock := gaugeLift_time_eq p b lift hright
    (squarePath_parameter_mem p (Ioo_subset_Icc_self hs)) (hsrc s (Ioo_subset_Icc_self hs))
  have hdensity := rawLIntegrand_projectedVelocity_congr (G := G) hbase
  rw [gaugeCurve_rawLIntegrand b θ u htime hspace, M14RawLIntegrand,
    squarePath_projectedVelocity p hs, hpoint] at hdensity
  have hsqrt : Real.sqrt s ≠ 0 :=
    (Real.sqrt_pos.mpr ((Real.sqrt_nonneg τ₁).trans_lt hs.1)).ne'
  have henergy := add_left_cancel (mul_left_cancel₀ hsqrt hdensity)
  rw [squareMetricCoefficient_apply, ← hclock]
  exact henergy.symm




theorem squarePath_gauge_potential_eq
    (θ : ℝ → (G.timeIntervals.interval (G.gaugeCover.interval b)).Point)
    {U : Set G.Point}
    (hright : ∀ q ∈ U, (G.gaugeCover.cylinder b).toSpacetime (lift q) = q)
    {s : ℝ} (hs : s ∈ M14SqrtParameterInterval τ₁ τ₂) (hsrc : p.curve (s ^ 2) ∈ U)
    (hclock : (θ s).val = T - s ^ 2) :
    squarePotentialCoefficient b θ x₀ (s, (lift (p.curve (s ^ 2))).2.val) =
      pathSquarePotential p s := by
  have heq : θ s = (lift (p.curve (s ^ 2))).1 := Subtype.ext
    (hclock.trans (gaugeLift_time_eq p b lift hright (squarePath_parameter_mem p hs) hsrc).symm)
  simp only [squarePotentialCoefficient, (G.gaugeCover.spatial b).chartAt_symm_apply_val,
    heq, hright _ hsrc, pathSquarePotential]




theorem squarePath_gauge_action_eq (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (θ : ℝ → (G.timeIntervals.interval (G.gaugeCover.interval b)).Point)
    {U : Set G.Point}
    (hlift : ContMDiffOn (spacetimeModel n) (spacetimeModel n) ∞ lift U)
    (hright : ∀ q ∈ U, (G.gaugeCover.cylinder b).toSpacetime (lift q) = q)
    (hsrc : ∀ s ∈ M14SqrtParameterInterval τ₁ τ₂, p.curve (s ^ 2) ∈ U)
    (hclock : ∀ s ∈ M14SqrtParameterInterval τ₁ τ₂, (θ s).val = T - s ^ 2) :
    let f := fun s => squareMetricCoefficient (G.gaugeCover.spatial b)
      (G.gaugeCover.metric b).metric T x₀ (s, (lift (p.curve (s ^ 2))).2.val)
        (deriv (fun r => (lift (p.curve (r ^ 2))).2.val) s)
        (deriv (fun r => (lift (p.curve (r ^ 2))).2.val) s) / 2 +
      squarePotentialCoefficient b θ x₀ (s, (lift (p.curve (s ^ 2))).2.val)
    IntervalIntegrable f volume (Real.sqrt τ₁) (Real.sqrt τ₂) ∧
      (∫ s in Real.sqrt τ₁..Real.sqrt τ₂, f s) = M14BackwardLAction G p := by
  dsimp only
  have hle := Real.sqrt_le_sqrt p.tau_lt.le
  have H := (hM12.leafwise_calculus X time I G.spacetime G.slices
    G.timeIntervals G.gaugeCover).2 G.leafwise
  have hpot : ContinuousOn (pathSquarePotential p) (M14SqrtParameterInterval τ₁ τ₂) :=
    (continuousOn_const.mul (continuousOn_id.pow 2)).mul
      (H.scalar_smooth.continuous.comp_continuousOn (squarePath_continuousOn p))
  have hp : IntervalIntegrable (pathSquarePotential p) volume
      (Real.sqrt τ₁) (Real.sqrt τ₂) := hpot.intervalIntegrable_of_Icc hle
  have hi := hp.add ((squarePath_kinetic_intervalIntegrable p hM12).const_mul (1 / 2 : ℝ))
  have heq (s : ℝ) (hs : s ∈ Ioo (Real.sqrt τ₁) (Real.sqrt τ₂)) :
      squareMetricCoefficient (G.gaugeCover.spatial b) (G.gaugeCover.metric b).metric T x₀
          (s, (lift (p.curve (s ^ 2))).2.val)
          (deriv (fun r => (lift (p.curve (r ^ 2))).2.val) s)
          (deriv (fun r => (lift (p.curve (r ^ 2))).2.val) s) / 2 +
        squarePotentialCoefficient b θ x₀ (s, (lift (p.curve (s ^ 2))).2.val) =
      pathSquarePotential p s + (1 / 2 : ℝ) * pathSquareKinetic p s := by
    rw [squarePath_gauge_kinetic_eq p b lift x₀ hlift hright hsrc hs,
      squarePath_gauge_potential_eq p b lift x₀ θ hright (Ioo_subset_Icc_self hs)
        (hsrc s (Ioo_subset_Icc_self hs)) (hclock s (Ioo_subset_Icc_self hs))]
    ring
  refine ⟨hi.congr_uIoo (fun s hs => (heq s (by simpa only [uIoo_of_le hle] using hs)).symm), ?_⟩
  rw [backwardPath_squareAction_eq p]
  exact intervalIntegral.integral_congr_Ioo_of_le hle heq

end PoincareConjecture.M14
