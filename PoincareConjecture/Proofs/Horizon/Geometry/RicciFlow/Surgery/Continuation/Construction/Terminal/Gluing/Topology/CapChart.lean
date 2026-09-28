import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Gluing.ClosedGraph
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Metric.Standard.Radial.StandardBalls

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.MetricSurgeryResult

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} {K : MetricSurgeryConstants}
  {g₀ : StandardInitialMetric} {I : MetricSurgeryInput K g}
  (R : MetricSurgeryResult g₀ I)

private theorem cap_ball_isOpen :
    IsOpen (g₀.metric.ball 0 (g₀.cylindrical_end.radius + 5)) := by
  rw [MetricSurgery.standard_ball_eq_euclidean g₀
    (by linarith [g₀.cylindrical_end.radius_pos])]
  exact Metric.isOpen_ball

theorem cap_map_mfderiv_bijective {x : StandardCapSpace}
    (hx : x ∈ g₀.metric.ball 0 (g₀.cylindrical_end.radius + 5)) :
    Function.Bijective (mfderiv (𝓡 3) (𝓡 3) R.cap_map x) := by
  have hf := ((R.cap_map_smooth x hx).contMDiffAt
    (cap_ball_isOpen.mem_nhds hx)).mdifferentiableAt (by simp)
  have hg := (R.cap_inverse_smooth _ (mem_image_of_mem _ hx)).mdifferentiableWithinAt
    (by simp)
  have hc := (hg.hasMFDerivWithinAt.comp x (hf.hasMFDerivAt.hasMFDerivWithinAt
    (s := g₀.metric.ball 0 (g₀.cylindrical_end.radius + 5)))
    (mapsTo_image _ _)).hasMFDerivAt (cap_ball_isOpen.mem_nhds hx)
  have heq : R.cap_inverse ∘ R.cap_map =ᶠ[𝓝 x] id := by
    filter_upwards [cap_ball_isOpen.mem_nhds hx] with y hy
    exact R.cap_left_inverse hy
  have hd := hc.mfderiv
  rw [heq.mfderiv_eq (I := 𝓡 3) (I' := 𝓡 3), mfderiv_id] at hd
  have hinj : Function.Injective (mfderiv (𝓡 3) (𝓡 3) R.cap_map x) := by
    intro v w hvw
    have hv := congrArg (fun L => L v) hd
    have hw := congrArg (fun L => L w) hd
    exact hv.trans ((congrArg _ hvw).trans hw.symm)
  let : FiniteDimensional ℝ (TangentSpace (𝓡 3) x) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin 3))
      (TangentSpace (𝓡 3) : StandardCapSpace → Type _) _
  let : FiniteDimensional ℝ (TangentSpace (𝓡 3) (R.cap_map x)) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin 3))
      (TangentSpace (𝓡 3) : R.output.carrier → Type _) _
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (mfderiv (𝓡 3) (𝓡 3) R.cap_map x).toLinearMap) rfl).mp hinj⟩

theorem cap_image_isOpen {V : Set StandardCapSpace} (hV : IsOpen V)
    (hsub : V ⊆ g₀.metric.ball 0 (g₀.cylindrical_end.radius + 5)) :
    IsOpen (R.cap_map '' V) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro _ ⟨x, hx, rfl⟩
  have hs := (R.cap_map_smooth x (hsub hx)).contMDiffAt
    (cap_ball_isOpen.mem_nhds (hsub hx))
  rw [← Poincare.map_nhds_eq_of_contMDiffAt_mfderiv_bijective hs
    (R.cap_map_mfderiv_bijective (hsub hx))]
  exact Filter.image_mem_map (hV.mem_nhds hx)

def capEuclideanRadius (_R : MetricSurgeryResult g₀ I) : ℝ :=
  MetricSurgery.radialEuclideanRadius g₀ (g₀.cylindrical_end.radius + 4)

theorem capEuclideanRadius_pos : 0 < R.capEuclideanRadius :=
  (MetricSurgery.radialEuclideanRadius_pos_iff g₀ _).mpr
    (by linarith [g₀.cylindrical_end.radius_pos])

theorem capEuclidean_closedBall_subset :
    Metric.closedBall (0 : StandardCapSpace) R.capEuclideanRadius ⊆
      g₀.metric.ball 0 (g₀.cylindrical_end.radius + 5) := by
  change Metric.closedBall 0 (MetricSurgery.radialEuclideanRadius g₀
    (g₀.cylindrical_end.radius + 4)) ⊆ _
  rw [← MetricSurgery.standard_closed_ball_eq_euclidean g₀
    (by linarith [g₀.cylindrical_end.radius_pos])]
  intro x hx
  exact hx.trans_lt ((ENNReal.ofReal_lt_ofReal_iff
    (by linarith [g₀.cylindrical_end.radius_pos])).mpr (by linarith))

theorem capEuclidean_closedBall_image :
    R.cap_map '' Metric.closedBall 0 R.capEuclideanRadius =
      closure (R.cap_map '' g₀.metric.ball 0 (g₀.cylindrical_end.radius + 4)) := by
  rw [← R.cap_closed_image]
  congr 1
  exact (MetricSurgery.standard_closed_ball_eq_euclidean g₀
    (by linarith [g₀.cylindrical_end.radius_pos])).symm

theorem capEuclidean_sphere_image :
    R.cap_map '' Metric.sphere 0 R.capEuclideanRadius =
      R.collapse '' I.neck.central_sphere := by
  have hball : g₀.metric.ball 0 (g₀.cylindrical_end.radius + 4) =
      Metric.ball 0 R.capEuclideanRadius :=
    MetricSurgery.standard_ball_eq_euclidean g₀
      (by linarith [g₀.cylindrical_end.radius_pos])
  have hopen : IsOpen (R.cap_map '' g₀.metric.ball 0 (g₀.cylindrical_end.radius + 4)) := by
    rw [hball]
    exact R.cap_image_isOpen Metric.isOpen_ball
      (Metric.ball_subset_closedBall.trans R.capEuclidean_closedBall_subset)
  rw [R.cap_boundary, frontier, hopen.interior_eq, ← R.capEuclidean_closedBall_image, hball]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨mem_image_of_mem _ (Metric.sphere_subset_closedBall hx), ?_⟩
    rintro ⟨z, hz, hzx⟩
    have hzx' : z = x := R.cap_left_inverse.injOn
      (R.capEuclidean_closedBall_subset (Metric.ball_subset_closedBall hz))
      (R.capEuclidean_closedBall_subset (Metric.sphere_subset_closedBall hx)) hzx
    subst z
    exact (not_lt_of_ge (Metric.mem_sphere.mp hx).ge) (Metric.mem_ball.mp hz)
  · rintro ⟨⟨x, hx, rfl⟩, hout⟩
    refine ⟨x, ?_, rfl⟩
    apply Metric.mem_sphere.mpr
    exact le_antisymm (Metric.mem_closedBall.mp hx)
      (le_of_not_gt (fun hlt => hout (mem_image_of_mem _ (Metric.mem_ball.mpr hlt))))

def closedCapHomeomorph :
    Metric.closedBall (0 : StandardCapSpace) R.capEuclideanRadius ≃ₜ
      closure (R.cap_map '' g₀.metric.ball 0 (g₀.cylindrical_end.radius + 4)) where
  toFun x := ⟨R.cap_map x.val, R.capEuclidean_closedBall_image ▸ mem_image_of_mem _ x.property⟩
  invFun y := ⟨R.cap_inverse y.val, by
    obtain ⟨x, hx, hxy⟩ := R.capEuclidean_closedBall_image.superset y.property
    rw [← hxy, R.cap_left_inverse (R.capEuclidean_closedBall_subset hx)]
    exact hx⟩
  left_inv x := Subtype.ext (R.cap_left_inverse (R.capEuclidean_closedBall_subset x.property))
  right_inv y := by
    apply Subtype.ext
    apply R.cap_right_inverse
    exact image_mono R.capEuclidean_closedBall_subset
      (R.capEuclidean_closedBall_image.superset y.property)
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (R.cap_map_smooth.continuousOn.mono R.capEuclidean_closedBall_subset).domRestrict
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply (R.cap_inverse_smooth.continuousOn.mono ?_).domRestrict
    rw [← R.capEuclidean_closedBall_image]
    exact image_mono R.capEuclidean_closedBall_subset

end PoincareConjecture.MetricSurgeryResult
