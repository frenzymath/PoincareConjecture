import PoincareConjecture.Proofs.M36.RetainedDifferential
import PoincareConjecture.Proofs.M36.RadialWeights
import PoincareConjecture.Proofs.M36.WeightedMetric










set_option autoImplicit false

open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M36

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

noncomputable def surgeryNeckWeight (g₀ : StandardInitialMetric) (N : EpsilonNeck g) :
    SurgeryBall.{u} g₀ (surgeryOuterRadius g₀ N.epsilon) → ℝ :=
  radialNeckWeight g₀ ∘ surgeryBallInclusion g₀ (surgeryOuterRadius g₀ N.epsilon)

noncomputable def surgeryTransitionDomain (g₀ : StandardInitialMetric)
    (N : EpsilonNeck g) : Set (SurgeryBall.{u} g₀ (surgeryOuterRadius g₀ N.epsilon)) :=
  {y | g₀.cylindrical_end.radius + 2 <
    radialArclength g₀ ‖surgeryBallInclusion g₀ (surgeryOuterRadius g₀ N.epsilon) y‖}

theorem surgeryTransitionDomain_isOpen (g₀ : StandardInitialMetric) (N : EpsilonNeck g) :
    IsOpen (surgeryTransitionDomain g₀ N) :=
  isOpen_lt continuous_const ((radialArclength_contDiff g₀).continuous.comp
    (surgeryBallInclusion_contMDiff g₀ _).continuous.norm)

theorem surgeryTransitionDomain_ne_zero (g₀ : StandardInitialMetric) (N : EpsilonNeck g)
    {y : SurgeryBall.{u} g₀ (surgeryOuterRadius g₀ N.epsilon)}
    (hy : y ∈ surgeryTransitionDomain g₀ N) :
    surgeryBallInclusion g₀ (surgeryOuterRadius g₀ N.epsilon) y ≠ 0 := by
  intro hz
  change g₀.cylindrical_end.radius + 2 <
    radialArclength g₀ ‖surgeryBallInclusion g₀ (surgeryOuterRadius g₀ N.epsilon) y‖ at hy
  rw [hz, norm_zero, radialArclength_zero] at hy
  linarith [g₀.cylindrical_end.radius_pos]

theorem surgeryNeckWeight_contMDiff (g₀ : StandardInitialMetric) (N : EpsilonNeck g) :
    ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (surgeryNeckWeight g₀ N) :=
  (radialNeckWeight_contDiff g₀).contMDiff.comp (surgeryBallInclusion_contMDiff g₀ _)

theorem surgeryNeckWeight_tsupport (g₀ : StandardInitialMetric) (N : EpsilonNeck g) :
    tsupport (surgeryNeckWeight g₀ N) ⊆ surgeryTransitionDomain g₀ N := by
  intro y hy
  have hmem := tsupport_comp_subset_preimage (radialNeckWeight g₀)
    (surgeryBallInclusion_contMDiff g₀ (surgeryOuterRadius g₀ N.epsilon)).continuous hy
  have hR := radialNeckWeight_tsupport g₀ hmem
  change g₀.cylindrical_end.radius + 4 - 7 / 4 ≤
    radialArclength g₀ ‖surgeryBallInclusion g₀ (surgeryOuterRadius g₀ N.epsilon) y‖ at hR
  change g₀.cylindrical_end.radius + 2 <
    radialArclength g₀ ‖surgeryBallInclusion g₀ (surgeryOuterRadius g₀ N.epsilon) y‖
  linarith

noncomputable def surgeryBackgroundMetric (g₀ : StandardInitialMetric) (N : EpsilonNeck g) :
    RiemannianMetric 3 (SurgeryBall.{u} g₀ (surgeryOuterRadius g₀ N.epsilon)) :=
  smoothPullbackMetric g₀.metric (surgeryBallInclusion g₀ _)
    (surgeryBallInclusion_contMDiff g₀ _) (surgeryBallInclusion_mfderiv_bijective g₀ _)

noncomputable def surgeryConformalMultiplier (g₀ : StandardInitialMetric)
    (N : EpsilonNeck g) (C q r : ℝ) :
    SurgeryBall.{u} g₀ (surgeryOuterRadius g₀ N.epsilon) → ℝ :=
  radialConformalMultiplier g₀ C q N.epsilon r ∘
    surgeryBallInclusion g₀ (surgeryOuterRadius g₀ N.epsilon)

theorem surgeryConformalMultiplier_contMDiff (g₀ : StandardInitialMetric)
    (N : EpsilonNeck g) (C q : ℝ) {r : ℝ} (hr : 0 < r) :
    ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (surgeryConformalMultiplier g₀ N C q r) :=
  (radialConformalMultiplier_contDiff g₀ C q N.epsilon hr).contMDiff.comp
    (surgeryBallInclusion_contMDiff g₀ _)

noncomputable def surgeryMetric (g₀ : StandardInitialMetric) (N : EpsilonNeck g)
    (hcut : surgeryCapRadius g₀ < N.epsilon⁻¹) (C q eta r : ℝ)
    (hlambda : 0 < N.connection.scalarCurvature N.center) (heta : 0 < eta) (hr : 0 < r) :
    RiemannianMetric 3 (SurgeryBall.{u} g₀ (surgeryOuterRadius g₀ N.epsilon)) :=
  let background := positiveScaling (surgeryBackgroundMetric g₀ N)
    (fun _ => eta / N.connection.scalarCurvature N.center) contMDiff_const
    (fun _ => div_pos heta hlambda)
  let blend := weightedPullbackMetric g background (surgeryRetainedInverse g₀ N)
    (surgeryNeckWeight g₀ N) (surgeryTransitionDomain g₀ N)
    (surgeryTransitionDomain_isOpen g₀ N) (surgeryNeckWeight_contMDiff g₀ N)
    (fun y => radialNeckWeight_bounds g₀ (surgeryBallInclusion g₀ _ y))
    (surgeryNeckWeight_tsupport g₀ N)
    (fun _ hy => surgeryRetainedInverse_contMDiffAt g₀ N hcut
      (surgeryTransitionDomain_ne_zero g₀ N hy))
    (fun _ hy => surgeryRetainedInverse_mfderiv_bijective g₀ N hcut
      (surgeryTransitionDomain_ne_zero g₀ N hy))
  positiveScaling blend (surgeryConformalMultiplier g₀ N C q r)
    (surgeryConformalMultiplier_contMDiff g₀ N C q hr)
    (fun y => radialConformalMultiplier_pos g₀ C q N.epsilon r (surgeryBallInclusion g₀ _ y))

theorem surgeryMetric_inner (g₀ : StandardInitialMetric) (N : EpsilonNeck g)
    (hcut : surgeryCapRadius g₀ < N.epsilon⁻¹) (C q eta r : ℝ)
    (hlambda : 0 < N.connection.scalarCurvature N.center) (heta : 0 < eta) (hr : 0 < r)
    (y : SurgeryBall.{u} g₀ (surgeryOuterRadius g₀ N.epsilon))
    (v w : TangentSpace (𝓡 3) y) :
    (surgeryMetric g₀ N hcut C q eta r hlambda heta hr).inner y v w =
      surgeryConformalMultiplier g₀ N C q r y *
        (surgeryNeckWeight g₀ N y * metricPullbackForm g (surgeryRetainedInverse g₀ N) y v w +
          (1 - surgeryNeckWeight g₀ N y) * (eta / N.connection.scalarCurvature N.center *
            metricPullbackForm g₀.metric (surgeryBallInclusion g₀ _) y v w)) := rfl

theorem surgeryMetric_eq_pullback_retained (g₀ : StandardInitialMetric) (N : EpsilonNeck g)
    (hcut : surgeryCapRadius g₀ < N.epsilon⁻¹) (C q eta r : ℝ)
    (hlambda : 0 < N.connection.scalarCurvature N.center) (heta : 0 < eta) (hr : 0 < r)
    (hq : 0 < q) (hrA : r ≤ g₀.cylindrical_end.radius)
    {y : SurgeryBall.{u} g₀ (surgeryOuterRadius g₀ N.epsilon)}
    (hy : standardSurgeryHeight g₀ (surgeryBallInclusion g₀ _ y) ≤ 0)
    (v w : TangentSpace (𝓡 3) y) :
    (surgeryMetric g₀ N hcut C q eta r hlambda heta hr).inner y v w =
      metricPullbackForm g (surgeryRetainedInverse g₀ N) y v w := by
  have ha : surgeryNeckWeight g₀ N y = 1 := neckCutoff_eq_one (by linarith)
  have hm : surgeryConformalMultiplier g₀ N C q r y = 1 :=
    radialConformalMultiplier_eq_one_retained g₀ C N.epsilon hq hr hrA hy
  rw [surgeryMetric_inner, ha, hm]
  simp

theorem standardSurgeryHeight_collapse (g₀ : StandardInitialMetric) (N : EpsilonNeck g)
    {x : M} (hx : x ∈ N.carrier) (hs : (N.coordinate_inverse x).2 < surgeryCapRadius g₀) :
    standardSurgeryHeight g₀ (surgeryBallInclusion g₀ _ (surgeryCollapse g₀ N x)) =
      (N.coordinate_inverse x).2 := by
  unfold standardSurgeryHeight
  rw [surgeryCollapse_arclength g₀ N hx, max_eq_left (sub_pos.mpr hs).le]
  dsimp [surgeryCapRadius]
  ring

set_option backward.isDefEq.respectTransparency false in
theorem surgeryRetainedInverse_comp_mfderiv (g₀ : StandardInitialMetric) (N : EpsilonNeck g)
    (hcut : surgeryCapRadius g₀ < N.epsilon⁻¹)
    {x : M} (hx : x ∈ N.region (-N.epsilon⁻¹) 1) (v : TangentSpace (𝓡 3) x) :
    mfderiv (𝓡 3) (𝓡 3) (surgeryRetainedInverse g₀ N) (surgeryCollapse g₀ N x)
      (mfderiv (𝓡 3) (𝓡 3) (surgeryCollapse g₀ N) x v) = v := by
  have hc := ((surgeryCollapse_contMDiffOn g₀ N x hx).contMDiffAt
    ((neck_region_isOpen N _ _).mem_nhds hx)).mdifferentiableAt (by simp)
  have hF := (surgeryRetainedInverse_contMDiffAt g₀ N hcut
    (surgeryCollapse_collar_ne_zero g₀ N hx)).mdifferentiableAt (by simp)
  have hinv : surgeryRetainedInverse g₀ N ∘ surgeryCollapse g₀ N =ᶠ[nhds x] id := by
    filter_upwards [(neck_region_isOpen N (-N.epsilon⁻¹) 1).mem_nhds hx] with z hz
    exact surgeryCollapse_left_inverse g₀ N hz
  have hcomp := hinv.mfderiv_eq (I := 𝓡 3) (I' := 𝓡 3)
  rw [mfderiv_comp x hF hc, mfderiv_id] at hcomp
  exact congrArg (fun L => L v) hcomp

set_option backward.isDefEq.respectTransparency false in
theorem surgeryMetric_retained (g₀ : StandardInitialMetric) (N : EpsilonNeck g)
    (hcut : surgeryCapRadius g₀ < N.epsilon⁻¹) (C q eta r : ℝ)
    (hlambda : 0 < N.connection.scalarCurvature N.center) (heta : 0 < eta) (hr : 0 < r)
    (hq : 0 < q) (hrA : r ≤ g₀.cylindrical_end.radius)
    {x : M} (hx : x ∈ N.region (-N.epsilon⁻¹) 0 ∪ N.central_sphere)
    (v w : TangentSpace (𝓡 3) x) :
    (surgeryMetric g₀ N hcut C q eta r hlambda heta hr).inner (surgeryCollapse g₀ N x)
      (mfderiv (𝓡 3) (𝓡 3) (surgeryCollapse g₀ N) x v)
      (mfderiv (𝓡 3) (𝓡 3) (surgeryCollapse g₀ N) x w) = g.inner x v w := by
  have hret := (neck_retained_iff N).mp hx
  have hcollar : x ∈ N.region (-N.epsilon⁻¹) 1 :=
    ⟨hret.1, (N.coordinate_inverse_mem x hret.1).2.1, by linarith [hret.2]⟩
  have hs : (N.coordinate_inverse x).2 < surgeryCapRadius g₀ :=
    lt_of_le_of_lt hret.2 (surgeryCapRadius_pos g₀)
  have hheight : standardSurgeryHeight g₀
      (surgeryBallInclusion g₀ _ (surgeryCollapse g₀ N x)) ≤ 0 := by
    rw [standardSurgeryHeight_collapse g₀ N hret.1 hs]
    exact hret.2
  rw [surgeryMetric_eq_pullback_retained g₀ N hcut C q eta r hlambda heta hr hq hrA hheight,
    metricPullbackForm_apply, surgeryRetainedInverse_comp_mfderiv g₀ N hcut hcollar,
    surgeryRetainedInverse_comp_mfderiv g₀ N hcut hcollar,
    surgeryCollapse_left_inverse g₀ N hcollar]

end PoincareConjecture.M36
