import PoincareConjecture.Proofs.M36.SurgeryMetric
import PoincareConjecture.Proofs.M36.IntrinsicIsometry

set_option autoImplicit false

open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M36

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

theorem neck_retained_subset_collar (N : EpsilonNeck g) :
    N.region (-N.epsilon⁻¹) 0 ∪ N.central_sphere ⊆ N.region (-N.epsilon⁻¹) 1 := by
  intro x hx
  have hret := (neck_retained_iff N).mp hx
  exact ⟨hret.1, (N.coordinate_inverse_mem x hret.1).2.1, by linarith [hret.2]⟩

set_option backward.isDefEq.respectTransparency false in
theorem surgeryCollapse_comp_mfderiv (g₀ : StandardInitialMetric) (N : EpsilonNeck g)
    (hcut : surgeryCapRadius g₀ < N.epsilon⁻¹)
    {y : SurgeryBall.{u} g₀ (surgeryOuterRadius g₀ N.epsilon)}
    (hy : y ∈ surgeryCollapse g₀ N '' N.region (-N.epsilon⁻¹) 1)
    (v : TangentSpace (𝓡 3) y) :
    mfderiv (𝓡 3) (𝓡 3) (surgeryCollapse g₀ N) (surgeryRetainedInverse g₀ N y)
      (mfderiv (𝓡 3) (𝓡 3) (surgeryRetainedInverse g₀ N) y v) = v := by
  obtain ⟨x, hx, rfl⟩ := hy
  have hF := (surgeryRetainedInverse_contMDiffAt g₀ N hcut
    (surgeryCollapse_collar_ne_zero g₀ N hx)).mdifferentiableAt (by simp)
  have hc : MDifferentiableAt (𝓡 3) (𝓡 3) (surgeryCollapse g₀ N)
      (surgeryRetainedInverse g₀ N (surgeryCollapse g₀ N x)) := by
    rw [surgeryCollapse_left_inverse g₀ N hx]
    exact ((surgeryCollapse_contMDiffOn g₀ N x hx).contMDiffAt
      ((neck_region_isOpen N _ _).mem_nhds hx)).mdifferentiableAt (by simp)
  have hinv : surgeryCollapse g₀ N ∘ surgeryRetainedInverse g₀ N =ᶠ[nhds (surgeryCollapse g₀ N x)]
      id := Filter.Eventually.of_forall (surgeryCollapse_right_inverse g₀ N hcut)
  have hcomp := hinv.mfderiv_eq (I := 𝓡 3) (I' := 𝓡 3)
  rw [mfderiv_comp _ hc hF, mfderiv_id] at hcomp
  exact congrArg (fun L => L v) hcomp

set_option backward.isDefEq.respectTransparency false in
theorem surgeryMetric_inverse_retained (g₀ : StandardInitialMetric) (N : EpsilonNeck g)
    (hcut : surgeryCapRadius g₀ < N.epsilon⁻¹) (C q eta r : ℝ)
    (hlambda : 0 < N.connection.scalarCurvature N.center) (heta : 0 < eta) (hr : 0 < r)
    (hq : 0 < q) (hrA : r ≤ g₀.cylindrical_end.radius)
    {y : SurgeryBall.{u} g₀ (surgeryOuterRadius g₀ N.epsilon)}
    (hy : y ∈ surgeryCollapse g₀ N '' (N.region (-N.epsilon⁻¹) 0 ∪ N.central_sphere))
    (v w : TangentSpace (𝓡 3) y) :
    g.inner (surgeryRetainedInverse g₀ N y)
      (mfderiv (𝓡 3) (𝓡 3) (surgeryRetainedInverse g₀ N) y v)
      (mfderiv (𝓡 3) (𝓡 3) (surgeryRetainedInverse g₀ N) y w) =
        (surgeryMetric g₀ N hcut C q eta r hlambda heta hr).inner y v w := by
  obtain ⟨x, hx, rfl⟩ := hy
  have hxC := neck_retained_subset_collar N hx
  have hcomp (z : TangentSpace (𝓡 3) (surgeryCollapse g₀ N x)) :
      mfderiv (𝓡 3) (𝓡 3) (surgeryCollapse g₀ N) x
        (mfderiv (𝓡 3) (𝓡 3) (surgeryRetainedInverse g₀ N) (surgeryCollapse g₀ N x) z) = z := by
    have h := surgeryCollapse_comp_mfderiv g₀ N hcut ⟨x, hxC, rfl⟩ z
    rw [surgeryCollapse_left_inverse g₀ N hxC] at h
    exact h
  have hm := surgeryMetric_retained g₀ N hcut C q eta r hlambda heta hr hq hrA hx
    (mfderiv (𝓡 3) (𝓡 3) (surgeryRetainedInverse g₀ N) (surgeryCollapse g₀ N x) v)
    (mfderiv (𝓡 3) (𝓡 3) (surgeryRetainedInverse g₀ N) (surgeryCollapse g₀ N x) w)
  rw [hcomp, hcomp] at hm
  rw [surgeryCollapse_left_inverse g₀ N hxC]
  exact hm.symm

theorem surgeryMetric_retained_closed_isometry (g₀ : StandardInitialMetric)
    (N : EpsilonNeck g) (hcut : surgeryCapRadius g₀ < N.epsilon⁻¹) (C q eta r : ℝ)
    (hlambda : 0 < N.connection.scalarCurvature N.center) (heta : 0 < eta) (hr : 0 < r)
    (hq : 0 < q) (hrA : r ≤ g₀.cylindrical_end.radius)
    {x y : M} (hx : x ∈ N.region (-N.epsilon⁻¹) 0 ∪ N.central_sphere)
    (hy : y ∈ N.region (-N.epsilon⁻¹) 0 ∪ N.central_sphere) :
    intrinsicEDist (surgeryMetric g₀ N hcut C q eta r hlambda heta hr)
        (surgeryCollapse g₀ N '' (N.region (-N.epsilon⁻¹) 0 ∪ N.central_sphere))
        (surgeryCollapse g₀ N x) (surgeryCollapse g₀ N y) =
      intrinsicEDist g (N.region (-N.epsilon⁻¹) 0 ∪ N.central_sphere) x y := by
  refine intrinsicEDist_image_eq_of_inverse_pullbacks g
    (surgeryMetric g₀ N hcut C q eta r hlambda heta hr)
    (k := surgeryRetainedInverse g₀ N) ?_ ?_ ?_ ?_ ?_ hx hy
  · intro z hz
    have hzC := neck_retained_subset_collar N hz
    exact (surgeryCollapse_contMDiffOn g₀ N z hzC).contMDiffAt
      ((neck_region_isOpen N _ _).mem_nhds hzC)
  · rintro _ ⟨z, hz, rfl⟩
    exact surgeryRetainedInverse_contMDiffAt g₀ N hcut
      (surgeryCollapse_collar_ne_zero g₀ N (neck_retained_subset_collar N hz))
  · intro z hz
    exact surgeryCollapse_left_inverse g₀ N (neck_retained_subset_collar N hz)
  · intro z hz v w
    exact surgeryMetric_retained g₀ N hcut C q eta r hlambda heta hr hq hrA hz v w
  · intro z hz v w
    exact surgeryMetric_inverse_retained g₀ N hcut C q eta r hlambda heta hr hq hrA hz v w

end PoincareConjecture.M36
