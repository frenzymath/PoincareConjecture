import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Metric.Construction.CapTopology

set_option autoImplicit false

open scoped Manifold ContDiff Topology

universe u v

namespace PoincareConjecture.MetricSurgery

theorem mfderiv_injective_of_local_leftInverse
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace StandardCapSpace X] [ChartedSpace StandardCapSpace Y]
    {f : X → Y} {k : Y → X} {x : X}
    (hf : MDifferentiableAt (𝓡 3) (𝓡 3) f x)
    (hk : MDifferentiableAt (𝓡 3) (𝓡 3) k (f x))
    (hinv : k ∘ f =ᶠ[nhds x] id) : Function.Injective (mfderiv (𝓡 3) (𝓡 3) f x) := by
  have hcomp := hinv.mfderiv_eq (I := 𝓡 3) (I' := 𝓡 3)
  rw [mfderiv_comp x hk hf, mfderiv_id] at hcomp
  apply Function.LeftInverse.injective (g := mfderiv (𝓡 3) (𝓡 3) k (f x))
  intro v
  exact congrArg (fun L => L v) hcomp

theorem surgeryBallInclusion_mfderiv_bijective (g₀ : StandardInitialMetric) (L : ℝ)
    [Nonempty (SurgeryBall.{u} g₀ L)] (y : SurgeryBall.{u} g₀ L) :
    Function.Bijective (mfderiv (𝓡 3) (𝓡 3) (surgeryBallInclusion g₀ L) y) := by
  have hy : surgeryBallInclusion g₀ L y ∈ Metric.ball 0 (radialEuclideanRadius g₀ L) :=
    y.down.property
  have hj := (surgeryBallInclusion_contMDiff g₀ L y).mdifferentiableAt (by simp)
  have hc := ((surgeryBallChart_contMDiffOn g₀ L _ hy).contMDiffAt
    (Metric.isOpen_ball.mem_nhds hy)).mdifferentiableAt (by simp)
  have hinj := mfderiv_injective_of_local_leftInverse hj hc
    (Filter.Eventually.of_forall (surgeryBallChart_left_inverse g₀ L))
  let D : StandardCapSpace →L[ℝ] StandardCapSpace :=
    mfderiv (𝓡 3) (𝓡 3) (surgeryBallInclusion g₀ L) y
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := D.toLinearMap) rfl).mp hinj⟩

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

theorem surgeryCollapse_contMDiffAt_before_tip (g₀ : StandardInitialMetric) (N : EpsilonNeck g)
    {x : M} (hx : x ∈ N.carrier) (hs : (N.coordinate_inverse x).2 < surgeryCapRadius g₀) :
    ContMDiffAt (𝓡 3) (𝓡 3) ∞ (surgeryCollapse g₀ N) x := by
  have hball := surgeryCollapse_mapsTo_ball g₀ N hx
  have hchart := (surgeryBallChart_contMDiffOn g₀ _ _ hball).contMDiffAt
    (Metric.isOpen_ball.mem_nhds hball)
  have hclip := (adaptedClippedCollapse_contMDiffOn g₀ _ _ hs).contMDiffAt
    ((isOpen_lt continuous_snd continuous_const).mem_nhds hs)
  exact hchart.comp x (hclip.comp x (neck_inverse_contMDiffAt N hx))

theorem surgeryRetainedInverse_contMDiffAt (g₀ : StandardInitialMetric) (N : EpsilonNeck g)
    (hcut : surgeryCapRadius g₀ < N.epsilon⁻¹)
    {y : SurgeryBall.{u} g₀ (surgeryOuterRadius g₀ N.epsilon)}
    (hy : surgeryBallInclusion g₀ (surgeryOuterRadius g₀ N.epsilon) y ≠ 0) :
    ContMDiffAt (𝓡 3) (𝓡 3) ∞ (surgeryRetainedInverse g₀ N) y := by
  have hy' : surgeryBallInclusion g₀ (surgeryOuterRadius g₀ N.epsilon) y ∈
      ({0}ᶜ : Set StandardCapSpace) := by simpa using hy
  have hQ := ((adaptedInverseCoordinates_contMDiffOn g₀ _ hy').contMDiffAt
    (isOpen_compl_singleton.mem_nhds hy')).comp y
      (surgeryBallInclusion_contMDiff g₀ _ y)
  exact (neck_coordinate_contMDiffAt N
    (surgeryRetainedInverse_coordinate_mem g₀ N hcut y)).comp y
      (hQ.fst.prodMk (contMDiffAt_const.sub hQ.snd))

theorem surgeryRetainedInverse_mfderiv_bijective (g₀ : StandardInitialMetric)
    (N : EpsilonNeck g) (hcut : surgeryCapRadius g₀ < N.epsilon⁻¹)
    {y : SurgeryBall.{u} g₀ (surgeryOuterRadius g₀ N.epsilon)}
    (hy : surgeryBallInclusion g₀ (surgeryOuterRadius g₀ N.epsilon) y ≠ 0) :
    Function.Bijective (mfderiv (𝓡 3) (𝓡 3) (surgeryRetainedInverse g₀ N) y) := by
  have hR : 0 < radialArclength g₀
      ‖surgeryBallInclusion g₀ (surgeryOuterRadius g₀ N.epsilon) y‖ :=
    radialArclength_pos g₀ (norm_pos_iff.mpr hy)
  have hs : (N.coordinate_inverse (surgeryRetainedInverse g₀ N y)).2 < surgeryCapRadius g₀ := by
    rw [surgeryRetainedInverse_height g₀ N hcut]
    linarith
  have hF := (surgeryRetainedInverse_contMDiffAt g₀ N hcut hy).mdifferentiableAt (by simp)
  have hC := (surgeryCollapse_contMDiffAt_before_tip g₀ N
    (surgeryRetainedInverse_mem g₀ N hcut y) hs).mdifferentiableAt (by simp)
  have hinj := mfderiv_injective_of_local_leftInverse hF hC
    (Filter.Eventually.of_forall (surgeryCollapse_right_inverse g₀ N hcut))
  let D : StandardCapSpace →L[ℝ] StandardCapSpace :=
    mfderiv (𝓡 3) (𝓡 3) (surgeryRetainedInverse g₀ N) y
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := D.toLinearMap) rfl).mp hinj⟩

end PoincareConjecture.MetricSurgery
