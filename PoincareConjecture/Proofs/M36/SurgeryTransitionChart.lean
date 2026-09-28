import PoincareConjecture.Proofs.M36.CenteredNeckChart
import PoincareConjecture.Proofs.M36.CollapseMetric

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M36

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace E₃ M] [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M}

def centeredSurgeryDomain (N : EpsilonNeck g) (s : ℝ) : Set E₃ :=
  centeredNeckDomain N s ∩ {p | cylinderHeightCovector p + s < 2}

theorem centeredSurgeryDomain_isOpen (N : EpsilonNeck g) (s : ℝ) :
    IsOpen (centeredSurgeryDomain N s) :=
  (centeredNeckDomain_isOpen N s).inter
    (isOpen_lt (cylinderHeightCovector.continuous.add continuous_const) continuous_const)

theorem zero_mem_centeredSurgeryDomain (N : EpsilonNeck g) {s : ℝ}
    (hs : s ∈ Set.Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) (hs₂ : s < 2) :
    0 ∈ centeredSurgeryDomain N s := by
  refine ⟨zero_mem_centeredNeckDomain N hs, ?_⟩
  change cylinderHeightCovector (0 : E₃) + s < 2
  simpa only [map_zero, zero_add] using hs₂

theorem neck_inverse_centeredNeckLift (N : EpsilonNeck g)
    (theta : UnitTwoSphere) (s : ℝ) {p : E₃} (hp : p ∈ centeredNeckDomain N s) :
    N.coordinate_inverse (centeredNeckLift N theta s p) = centeredCylinderLift theta s p :=
  neck_inverse_coordinate N (centeredCylinderLift theta s p) ⟨Set.mem_univ _, hp⟩

theorem centeredNeckLift_before_tip (g₀ : StandardInitialMetric) (N : EpsilonNeck g)
    (theta : UnitTwoSphere) (s : ℝ) {p : E₃} (hp : p ∈ centeredSurgeryDomain N s) :
    (N.coordinate_inverse (centeredNeckLift N theta s p)).2 < surgeryCapRadius g₀ := by
  rw [neck_inverse_centeredNeckLift N theta s hp.1]
  change cylinderHeightCovector p + s < g₀.cylindrical_end.radius + 4
  exact hp.2.trans (by linarith [g₀.cylindrical_end.radius_pos])

noncomputable def centeredSurgeryLift (g₀ : StandardInitialMetric) (N : EpsilonNeck g)
    (theta : UnitTwoSphere) (s : ℝ) :
    E₃ → SurgeryBall.{u} g₀ (surgeryOuterRadius g₀ N.epsilon) :=
  surgeryCollapse g₀ N ∘ centeredNeckLift N theta s

theorem centeredSurgeryLift_zero (g₀ : StandardInitialMetric) (N : EpsilonNeck g)
    (theta : UnitTwoSphere) (s : ℝ) :
    centeredSurgeryLift g₀ N theta s 0 = surgeryCollapse g₀ N (N.coordinate_map (theta, s)) := by
  simp only [centeredSurgeryLift, Function.comp_apply, centeredNeckLift_zero]

theorem centeredSurgeryLift_contMDiffAt (g₀ : StandardInitialMetric) (N : EpsilonNeck g)
    (theta : UnitTwoSphere) (s : ℝ) {p : E₃} (hp : p ∈ centeredSurgeryDomain N s) :
    ContMDiffAt (𝓡 3) (𝓡 3) ∞ (centeredSurgeryLift g₀ N theta s) p :=
  (surgeryCollapse_contMDiffAt_before_tip g₀ N
    (centeredNeckLift_mem N theta s hp.1) (centeredNeckLift_before_tip g₀ N theta s hp)).comp p
      (centeredNeckLift_contMDiffAt N theta s hp.1)

theorem centeredSurgeryLift_inclusion_ne_zero (g₀ : StandardInitialMetric)
    (N : EpsilonNeck g) (theta : UnitTwoSphere) (s : ℝ) {p : E₃}
    (hp : p ∈ centeredSurgeryDomain N s) :
    surgeryBallInclusion g₀ (surgeryOuterRadius g₀ N.epsilon)
      (centeredSurgeryLift g₀ N theta s p) ≠ 0 :=
  surgeryCollapse_inclusion_ne_zero_before_tip g₀ N
    (centeredNeckLift_mem N theta s hp.1) (centeredNeckLift_before_tip g₀ N theta s hp)

theorem centeredSurgeryLift_height (g₀ : StandardInitialMetric) (N : EpsilonNeck g)
    (theta : UnitTwoSphere) (s : ℝ) {p : E₃} (hp : p ∈ centeredSurgeryDomain N s) :
    standardSurgeryHeight g₀ (surgeryBallInclusion g₀ (surgeryOuterRadius g₀ N.epsilon)
      (centeredSurgeryLift g₀ N theta s p)) = cylinderHeightCovector p + s := by
  rw [centeredSurgeryLift, Function.comp_apply,
    standardSurgeryHeight_collapse g₀ N (centeredNeckLift_mem N theta s hp.1)
      (centeredNeckLift_before_tip g₀ N theta s hp),
    neck_inverse_centeredNeckLift N theta s hp.1]
  rfl

theorem surgeryRetainedInverse_centeredSurgeryLift (g₀ : StandardInitialMetric)
    (N : EpsilonNeck g) (theta : UnitTwoSphere) (s : ℝ) {p : E₃}
    (hp : p ∈ centeredSurgeryDomain N s) :
    surgeryRetainedInverse g₀ N (centeredSurgeryLift g₀ N theta s p) =
      centeredNeckLift N theta s p :=
  surgeryCollapse_left_inverse_before_tip g₀ N (centeredNeckLift_mem N theta s hp.1)
    (centeredNeckLift_before_tip g₀ N theta s hp)

theorem surgeryRetainedInverse_centeredSurgeryLift_mfderiv (g₀ : StandardInitialMetric)
    (N : EpsilonNeck g) (hcut : surgeryCapRadius g₀ < N.epsilon⁻¹)
    (theta : UnitTwoSphere) (s : ℝ) {p : E₃} (hp : p ∈ centeredSurgeryDomain N s)
    (v : E₃) :
    mfderiv (𝓡 3) (𝓡 3) (surgeryRetainedInverse g₀ N)
      (centeredSurgeryLift g₀ N theta s p)
      (mfderiv (𝓡 3) (𝓡 3) (centeredSurgeryLift g₀ N theta s) p v) =
        mfderiv (𝓡 3) (𝓡 3) (centeredNeckLift N theta s) p v := by
  have hF := (surgeryRetainedInverse_contMDiffAt g₀ N hcut
    (centeredSurgeryLift_inclusion_ne_zero g₀ N theta s hp)).mdifferentiableAt (by simp)
  have he := (centeredSurgeryLift_contMDiffAt g₀ N theta s hp).mdifferentiableAt (by simp)
  have hinv : surgeryRetainedInverse g₀ N ∘ centeredSurgeryLift g₀ N theta s =ᶠ[𝓝 p]
      centeredNeckLift N theta s := by
    filter_upwards [(centeredSurgeryDomain_isOpen N s).mem_nhds hp] with q hq
    exact surgeryRetainedInverse_centeredSurgeryLift g₀ N theta s hq
  have hd := hinv.mfderiv_eq (I := 𝓡 3) (I' := 𝓡 3)
  rw [mfderiv_comp p hF he] at hd
  exact congrArg (fun D => D v) hd

theorem centeredSurgeryLift_mfderiv_isInvertible (g₀ : StandardInitialMetric)
    (N : EpsilonNeck g) (hcut : surgeryCapRadius g₀ < N.epsilon⁻¹)
    (theta : UnitTwoSphere) (s : ℝ) {p : E₃} (hp : p ∈ centeredSurgeryDomain N s) :
    (mfderiv (𝓡 3) (𝓡 3) (centeredSurgeryLift g₀ N theta s) p).IsInvertible := by
  have hinj : Function.Injective
      (mfderiv (𝓡 3) (𝓡 3) (centeredSurgeryLift g₀ N theta s) p) := by
    intro v w heq
    apply (centeredNeckLift_mfderiv_isInvertible N theta s hp.1).injective
    rw [← surgeryRetainedInverse_centeredSurgeryLift_mfderiv g₀ N hcut theta s hp v,
      ← surgeryRetainedInverse_centeredSurgeryLift_mfderiv g₀ N hcut theta s hp w, heq]
  let D : E₃ →L[ℝ] E₃ := mfderiv (𝓡 3) (𝓡 3) (centeredSurgeryLift g₀ N theta s) p
  have hsurj : Function.Surjective D :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := D.toLinearMap) rfl).mp hinj
  exact ⟨ContinuousLinearEquiv.ofBijective D (LinearMap.ker_eq_bot.mpr hinj)
    (LinearMap.range_eq_top.mpr hsurj), rfl⟩

theorem centeredSurgeryLift_inclusion (g₀ : StandardInitialMetric) (N : EpsilonNeck g)
    (theta : UnitTwoSphere) (s : ℝ) {p : E₃} (hp : p ∈ centeredSurgeryDomain N s) :
    surgeryBallInclusion g₀ (surgeryOuterRadius g₀ N.epsilon)
      (centeredSurgeryLift g₀ N theta s p) =
        adaptedClippedCollapse g₀ (surgeryCapRadius g₀) (centeredCylinderLift theta s p) := by
  rw [centeredSurgeryLift, Function.comp_apply,
    surgeryCollapse_inclusion g₀ N (centeredNeckLift_mem N theta s hp.1),
    neck_inverse_centeredNeckLift N theta s hp.1]

theorem exists_centeredSurgeryLift_zero (g₀ : StandardInitialMetric) (N : EpsilonNeck g)
    (hcut : surgeryCapRadius g₀ < N.epsilon⁻¹)
    {y : SurgeryBall.{u} g₀ (surgeryOuterRadius g₀ N.epsilon)}
    (hy : standardSurgeryHeight g₀
      (surgeryBallInclusion g₀ (surgeryOuterRadius g₀ N.epsilon) y) < 2) :
    ∃ (theta : UnitTwoSphere) (s : ℝ), 0 ∈ centeredSurgeryDomain N s ∧
      centeredSurgeryLift g₀ N theta s 0 = y ∧
      s = standardSurgeryHeight g₀
        (surgeryBallInclusion g₀ (surgeryOuterRadius g₀ N.epsilon) y) := by
  let x := surgeryRetainedInverse g₀ N y
  have hx := surgeryRetainedInverse_mem g₀ N hcut y
  have hs : (N.coordinate_inverse x).2 = standardSurgeryHeight g₀
      (surgeryBallInclusion g₀ (surgeryOuterRadius g₀ N.epsilon) y) :=
    surgeryRetainedInverse_height g₀ N hcut y
  refine ⟨(N.coordinate_inverse x).1, (N.coordinate_inverse x).2,
    zero_mem_centeredSurgeryDomain N (N.coordinate_inverse_mem x hx).2 (hs.trans_lt hy), ?_, hs⟩
  rw [centeredSurgeryLift_zero]
  change surgeryCollapse g₀ N (N.coordinate_map (N.coordinate_inverse x)) = y
  rw [neck_coordinate_inverse N hx]
  exact surgeryCollapse_right_inverse g₀ N hcut y

end PoincareConjecture.M36
