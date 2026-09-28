import PoincareConjecture.Proofs.M36.SurgeryMetric
import PoincareConjecture.Proofs.M36.NeckMetricBound
import PoincareConjecture.Proofs.M36.CollapsedPathComparison










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M36

theorem radialConformalMultiplier_le_one (g₀ : StandardInitialMetric)
    {C : ℝ} (hC : 0 ≤ C) (q : ℝ) {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (r : ℝ) (x : StandardCapSpace) :
    radialConformalMultiplier g₀ C q epsilon r x ≤ 1 := by
  have hb := radialTipWeight_bounds g₀ r x
  have hnear := conformalFactor_le_one (q := q) hC hepsilon (standardSurgeryHeight g₀ x)
  have htip := conformalFactor_le_one (q := q) hC hepsilon (g₀.cylindrical_end.radius + 4)
  unfold radialConformalMultiplier
  have hn := mul_le_mul_of_nonneg_left hnear hb.1
  have ht := mul_le_mul_of_nonneg_left htip (sub_nonneg.mpr hb.2)
  nlinarith only [hn, ht]

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

theorem surgeryCollapse_left_inverse_before_tip (g₀ : StandardInitialMetric)
    (N : EpsilonNeck g) {x : M} (hx : x ∈ N.carrier)
    (hs : (N.coordinate_inverse x).2 < surgeryCapRadius g₀) :
    surgeryRetainedInverse g₀ N (surgeryCollapse g₀ N x) = x := by
  unfold surgeryRetainedInverse
  rw [surgeryCollapse_inclusion g₀ N hx, adaptedClippedCollapse_of_lt g₀ _ _ hs,
    adaptedInverseCoordinates_polar g₀ _ (sub_pos.mpr hs)]
  simp only [sub_sub_cancel]
  exact neck_coordinate_inverse N hx

theorem surgeryCollapse_ne_tip_iff (g₀ : StandardInitialMetric) (N : EpsilonNeck g)
    {x : M} (hx : x ∈ N.carrier) :
    surgeryCollapse g₀ N x ≠ surgeryBallTip g₀ (surgeryOuterRadius_pos g₀ N) ↔
      (N.coordinate_inverse x).2 < surgeryCapRadius g₀ := by
  constructor
  · intro hne
    exact lt_of_not_ge (fun hge => hne (surgeryCollapse_tail g₀ N hx hge))
  · intro hs heq
    have hne := adaptedPolarPoint_ne_zero g₀
      ((N.coordinate_inverse x).1, surgeryCapRadius g₀ - (N.coordinate_inverse x).2)
      (sub_pos.mpr hs)
    apply hne
    have h := congrArg (surgeryBallInclusion g₀ (surgeryOuterRadius g₀ N.epsilon)) heq
    rw [surgeryCollapse_inclusion g₀ N hx, adaptedClippedCollapse_of_lt g₀ _ _ hs] at h
    exact h

theorem surgeryCollapse_inclusion_ne_zero_before_tip (g₀ : StandardInitialMetric)
    (N : EpsilonNeck g) {x : M} (hx : x ∈ N.carrier)
    (hs : (N.coordinate_inverse x).2 < surgeryCapRadius g₀) :
    surgeryBallInclusion g₀ (surgeryOuterRadius g₀ N.epsilon) (surgeryCollapse g₀ N x) ≠ 0 := by
  rw [surgeryCollapse_inclusion g₀ N hx, adaptedClippedCollapse_of_lt g₀ _ _ hs]
  exact adaptedPolarPoint_ne_zero g₀ _ (sub_pos.mpr hs)

theorem surgeryRetainedInverse_comp_mfderiv_before_tip (g₀ : StandardInitialMetric)
    (N : EpsilonNeck g) (hcut : surgeryCapRadius g₀ < N.epsilon⁻¹)
    {x : M} (hx : x ∈ N.carrier) (hs : (N.coordinate_inverse x).2 < surgeryCapRadius g₀)
    (v : TangentSpace (𝓡 3) x) :
    mfderiv (𝓡 3) (𝓡 3) (surgeryRetainedInverse g₀ N) (surgeryCollapse g₀ N x)
      (mfderiv (𝓡 3) (𝓡 3) (surgeryCollapse g₀ N) x v) = v := by
  have hc := (surgeryCollapse_contMDiffAt_before_tip g₀ N hx hs).mdifferentiableAt (by simp)
  have hF := (surgeryRetainedInverse_contMDiffAt g₀ N hcut
    (surgeryCollapse_inclusion_ne_zero_before_tip g₀ N hx hs)).mdifferentiableAt (by simp)
  have hregion : x ∈ N.region (-N.epsilon⁻¹) (surgeryCapRadius g₀) :=
    ⟨hx, (N.coordinate_inverse_mem x hx).2.1, hs⟩
  have hinv : surgeryRetainedInverse g₀ N ∘ surgeryCollapse g₀ N =ᶠ[nhds x] id := by
    filter_upwards [(neck_region_isOpen N _ _).mem_nhds hregion] with y hy
    exact surgeryCollapse_left_inverse_before_tip g₀ N hy.1 hy.2.2
  have hcomp := hinv.mfderiv_eq (I := 𝓡 3) (I' := 𝓡 3)
  rw [mfderiv_comp x hF hc, mfderiv_id] at hcomp
  exact congrArg (fun L => L v) hcomp

theorem neck_coordinate_inverse_comp_mfderiv (N : EpsilonNeck g)
    {x : M} (hx : x ∈ N.carrier) (v : TangentSpace (𝓡 3) x) :
    mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map (N.coordinate_inverse x)
      (mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) N.coordinate_inverse x v) = v := by
  have hf := (neck_inverse_contMDiffAt N hx).mdifferentiableAt (by simp)
  have hk := (neck_coordinate_contMDiffAt N
    (N.coordinate_inverse_mem x hx)).mdifferentiableAt (by simp)
  have hinv : N.coordinate_map ∘ N.coordinate_inverse =ᶠ[nhds x] id := by
    filter_upwards [N.carrier_open.mem_nhds hx] with y hy
    exact neck_coordinate_inverse N hy
  have hcomp := hinv.mfderiv_eq (I := 𝓡 3) (I' := 𝓡 3)
  rw [mfderiv_comp x hk hf, mfderiv_id] at hcomp
  exact congrArg (fun L => L v) hcomp

theorem neck_inverse_cylinder_bound (N : EpsilonNeck g)
    {x : M} (hx : x ∈ N.carrier) (v : TangentSpace (𝓡 3) x) :
    (1 - 6 * N.epsilon) * RoundCylinderMetric (N.coordinate_inverse x)
      (mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) N.coordinate_inverse x v)
      (mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) N.coordinate_inverse x v) ≤
      N.connection.scalarCurvature N.center * g.inner x v v := by
  have h := normalizedNeck_dominates_cylinder N (N.coordinate_inverse x)
    (N.coordinate_inverse_mem x hx).2
    (mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) N.coordinate_inverse x v)
  unfold roundCylinderPullback at h
  rw [neck_coordinate_inverse_comp_mfderiv N hx, neck_coordinate_inverse N hx] at h
  exact h

end PoincareConjecture.M36
