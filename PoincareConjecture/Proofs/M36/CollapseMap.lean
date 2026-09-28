import PoincareConjecture.Proofs.M36.AdaptedPolar
import PoincareConjecture.Proofs.M36.OutputSpace
import PoincareConjecture.Proofs.M36.NeckCoordinates









set_option autoImplicit false

open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M36

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

abbrev surgeryCapRadius (g₀ : StandardInitialMetric) : ℝ :=
  g₀.cylindrical_end.radius + 4

noncomputable abbrev surgeryOuterRadius (g₀ : StandardInitialMetric) (epsilon : ℝ) : ℝ :=
  surgeryCapRadius g₀ + epsilon⁻¹

theorem surgeryCapRadius_pos (g₀ : StandardInitialMetric) : 0 < surgeryCapRadius g₀ := by
  linarith [g₀.cylindrical_end.radius_pos]

theorem surgeryOuterRadius_pos (g₀ : StandardInitialMetric) (N : EpsilonNeck g) :
    0 < surgeryOuterRadius g₀ N.epsilon :=
  add_pos (surgeryCapRadius_pos g₀) (inv_pos.mpr N.epsilon_pos)

noncomputable instance surgeryNeckBallNonempty (g₀ : StandardInitialMetric)
    (N : EpsilonNeck g) :
    Nonempty (SurgeryBall.{u} g₀ (surgeryOuterRadius g₀ N.epsilon)) :=
  ⟨surgeryBallTip g₀ (surgeryOuterRadius_pos g₀ N)⟩

theorem adaptedClippedCollapse_of_lt (g₀ : StandardInitialMetric) (S : ℝ)
    (z : StandardCylinderSpace) (hz : z.2 < S) :
    adaptedClippedCollapse g₀ S z = adaptedPolarPoint g₀ (z.1, S - z.2) :=
  clippedRadialCollapse_of_lt g₀ S _ hz

theorem adaptedClippedCollapse_inverse (g₀ : StandardInitialMetric) (S : ℝ)
    (x : StandardCapSpace) :
    adaptedClippedCollapse g₀ S
      ((adaptedInverseCoordinates g₀ x).1, S - (adaptedInverseCoordinates g₀ x).2) = x := by
  have hR : 0 ≤ radialArclength g₀ ‖x‖ := by
    simpa only [radialArclength_zero] using
      (radialArclength_strictMono g₀).monotone (norm_nonneg x)
  have heq : adaptedClippedCollapse g₀ S
      ((adaptedInverseCoordinates g₀ x).1, S - (adaptedInverseCoordinates g₀ x).2) =
      adaptedPolarPoint g₀ (adaptedInverseCoordinates g₀ x) := by
    simp only [adaptedClippedCollapse, clippedRadialCollapse, adaptedPolarPoint,
      adaptedInverseCoordinates, sub_sub_cancel, max_eq_left hR]
  rw [heq]
  by_cases hx : x = 0
  · subst x
    simp [adaptedPolarPoint, adaptedInverseCoordinates, radialArclength_zero,
      radialPolarPoint_zero]
  · exact adaptedPolarPoint_inverse g₀ x hx

noncomputable def surgeryCollapse (g₀ : StandardInitialMetric) (N : EpsilonNeck g) :
    M → SurgeryBall.{u} g₀ (surgeryOuterRadius g₀ N.epsilon) :=
  fun x => surgeryBallChart g₀ (surgeryOuterRadius g₀ N.epsilon)
    (adaptedClippedCollapse g₀ (surgeryCapRadius g₀) (N.coordinate_inverse x))

noncomputable def surgeryRetainedInverse (g₀ : StandardInitialMetric) (N : EpsilonNeck g) :
    SurgeryBall.{u} g₀ (surgeryOuterRadius g₀ N.epsilon) → M :=
  fun y => N.coordinate_map
    ((adaptedInverseCoordinates g₀
      (surgeryBallInclusion g₀ (surgeryOuterRadius g₀ N.epsilon) y)).1,
      surgeryCapRadius g₀ - (adaptedInverseCoordinates g₀
        (surgeryBallInclusion g₀ (surgeryOuterRadius g₀ N.epsilon) y)).2)

theorem surgeryCollapse_mapsTo_ball (g₀ : StandardInitialMetric) (N : EpsilonNeck g)
    {x : M} (hx : x ∈ N.carrier) :
    adaptedClippedCollapse g₀ (surgeryCapRadius g₀) (N.coordinate_inverse x) ∈
      Metric.ball 0 (radialEuclideanRadius g₀ (surgeryOuterRadius g₀ N.epsilon)) := by
  rw [Metric.mem_ball, dist_zero_right]
  apply (radialArclength_strictMono g₀).lt_iff_lt.mp
  rw [adaptedClippedCollapse_arclength, radialArclength_euclideanRadius]
  apply max_lt
  · have hs := (N.coordinate_inverse_mem x hx).2.1
    dsimp [surgeryOuterRadius]
    linarith
  · exact surgeryOuterRadius_pos g₀ N

theorem surgeryCollapse_inclusion (g₀ : StandardInitialMetric) (N : EpsilonNeck g)
    {x : M} (hx : x ∈ N.carrier) :
    surgeryBallInclusion g₀ (surgeryOuterRadius g₀ N.epsilon) (surgeryCollapse g₀ N x) =
      adaptedClippedCollapse g₀ (surgeryCapRadius g₀) (N.coordinate_inverse x) :=
  surgeryBallChart_right_inverse g₀ _ (surgeryCollapse_mapsTo_ball g₀ N hx)

theorem surgeryCollapse_continuousOn (g₀ : StandardInitialMetric) (N : EpsilonNeck g) :
    ContinuousOn (surgeryCollapse g₀ N) N.carrier :=
  (surgeryBallChart_contMDiffOn g₀ _).continuousOn.comp
    ((adaptedClippedCollapse_continuous g₀ _).comp_continuousOn
      N.coordinate_inverse_smooth.continuousOn)
    (fun _ hx => surgeryCollapse_mapsTo_ball g₀ N hx)

theorem surgeryCollapse_contMDiffOn (g₀ : StandardInitialMetric) (N : EpsilonNeck g) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (surgeryCollapse g₀ N)
      (N.region (-N.epsilon⁻¹) 1) := by
  apply (surgeryBallChart_contMDiffOn g₀ _).comp
    ((adaptedClippedCollapse_contMDiffOn g₀ _).comp
      (N.coordinate_inverse_smooth.mono (neck_region_subset N _ _)) ?_) ?_
  · intro x hx
    exact lt_trans hx.2.2 (by dsimp [surgeryCapRadius]; linarith [g₀.cylindrical_end.radius_pos])
  · intro x hx
    exact surgeryCollapse_mapsTo_ball g₀ N hx.1

theorem surgeryCollapse_left_inverse (g₀ : StandardInitialMetric) (N : EpsilonNeck g) :
    Set.LeftInvOn (surgeryRetainedInverse g₀ N) (surgeryCollapse g₀ N)
      (N.region (-N.epsilon⁻¹) 1) := by
  intro x hx
  have hs : (N.coordinate_inverse x).2 < surgeryCapRadius g₀ :=
    lt_trans hx.2.2 (by dsimp [surgeryCapRadius]; linarith [g₀.cylindrical_end.radius_pos])
  unfold surgeryRetainedInverse
  rw [surgeryCollapse_inclusion g₀ N hx.1, adaptedClippedCollapse_of_lt g₀ _ _ hs,
    adaptedInverseCoordinates_polar g₀ _ (sub_pos.mpr hs)]
  simp only [sub_sub_cancel]
  exact neck_coordinate_inverse N hx.1

theorem surgeryRetainedInverse_coordinate_mem (g₀ : StandardInitialMetric)
    (N : EpsilonNeck g) (hcut : surgeryCapRadius g₀ < N.epsilon⁻¹)
    (y : SurgeryBall.{u} g₀ (surgeryOuterRadius g₀ N.epsilon)) :
    ((adaptedInverseCoordinates g₀
      (surgeryBallInclusion g₀ (surgeryOuterRadius g₀ N.epsilon) y)).1,
      surgeryCapRadius g₀ - (adaptedInverseCoordinates g₀
        (surgeryBallInclusion g₀ (surgeryOuterRadius g₀ N.epsilon) y)).2) ∈
      Set.univ ×ˢ Set.Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
  have hR := surgeryBallInclusion_radial_lt g₀ _ y
  have hnonneg : 0 ≤ radialArclength g₀
      ‖surgeryBallInclusion g₀ (surgeryOuterRadius g₀ N.epsilon) y‖ := by
    simpa only [radialArclength_zero] using
      (radialArclength_strictMono g₀).monotone (norm_nonneg _)
  refine ⟨Set.mem_univ _, ?_, ?_⟩ <;> dsimp [adaptedInverseCoordinates] <;>
    dsimp [surgeryOuterRadius] at hR <;> linarith

theorem surgeryRetainedInverse_mem (g₀ : StandardInitialMetric) (N : EpsilonNeck g)
    (hcut : surgeryCapRadius g₀ < N.epsilon⁻¹)
    (y : SurgeryBall.{u} g₀ (surgeryOuterRadius g₀ N.epsilon)) :
    surgeryRetainedInverse g₀ N y ∈ N.carrier :=
  neck_coordinate_mem N _ (surgeryRetainedInverse_coordinate_mem g₀ N hcut y)

theorem surgeryCollapse_right_inverse (g₀ : StandardInitialMetric) (N : EpsilonNeck g)
    (hcut : surgeryCapRadius g₀ < N.epsilon⁻¹) :
    Function.RightInverse (surgeryRetainedInverse g₀ N) (surgeryCollapse g₀ N) := by
  intro y
  apply (surgeryBallInclusion_isOpenEmbedding g₀ _).injective
  rw [surgeryCollapse_inclusion g₀ N (surgeryRetainedInverse_mem g₀ N hcut y)]
  unfold surgeryRetainedInverse
  rw [neck_inverse_coordinate N _ (surgeryRetainedInverse_coordinate_mem g₀ N hcut y),
    adaptedClippedCollapse_inverse]

theorem surgeryCollapse_arclength (g₀ : StandardInitialMetric) (N : EpsilonNeck g)
    {x : M} (hx : x ∈ N.carrier) :
    radialArclength g₀
      ‖surgeryBallInclusion g₀ (surgeryOuterRadius g₀ N.epsilon) (surgeryCollapse g₀ N x)‖ =
      max (surgeryCapRadius g₀ - (N.coordinate_inverse x).2) 0 := by
  rw [surgeryCollapse_inclusion g₀ N hx, adaptedClippedCollapse_arclength]

theorem surgeryCollapse_tail (g₀ : StandardInitialMetric) (N : EpsilonNeck g)
    {x : M} (hx : x ∈ N.carrier)
    (hs : surgeryCapRadius g₀ ≤ (N.coordinate_inverse x).2) :
    surgeryCollapse g₀ N x = surgeryBallTip g₀ (surgeryOuterRadius_pos g₀ N) := by
  apply (surgeryBallInclusion_isOpenEmbedding g₀ _).injective
  rw [surgeryCollapse_inclusion g₀ N hx, adaptedClippedCollapse_tail g₀ _ _ hs]
  rfl

theorem surgeryCollapse_collar_ne_zero (g₀ : StandardInitialMetric) (N : EpsilonNeck g)
    {x : M} (hx : x ∈ N.region (-N.epsilon⁻¹) 1) :
    surgeryBallInclusion g₀ (surgeryOuterRadius g₀ N.epsilon) (surgeryCollapse g₀ N x) ≠ 0 := by
  have hs : (N.coordinate_inverse x).2 < surgeryCapRadius g₀ :=
    lt_trans hx.2.2 (by dsimp [surgeryCapRadius]; linarith [g₀.cylindrical_end.radius_pos])
  rw [surgeryCollapse_inclusion g₀ N hx.1, adaptedClippedCollapse_of_lt g₀ _ _ hs]
  exact adaptedPolarPoint_ne_zero g₀ _ (sub_pos.mpr hs)

theorem surgeryRetainedInverse_contMDiffOn (g₀ : StandardInitialMetric) (N : EpsilonNeck g)
    (hcut : surgeryCapRadius g₀ < N.epsilon⁻¹) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (surgeryRetainedInverse g₀ N)
      (surgeryCollapse g₀ N '' N.region (-N.epsilon⁻¹) 1) := by
  have hQ := (adaptedInverseCoordinates_contMDiffOn g₀).comp
    (surgeryBallInclusion_contMDiff g₀ (surgeryOuterRadius g₀ N.epsilon)).contMDiffOn
    (show Set.MapsTo (surgeryBallInclusion g₀ (surgeryOuterRadius g₀ N.epsilon))
        (surgeryCollapse g₀ N '' N.region (-N.epsilon⁻¹) 1) {0}ᶜ from by
      rintro _ ⟨x, hx, rfl⟩
      simpa using surgeryCollapse_collar_ne_zero g₀ N hx)
  exact N.coordinate_map_smooth.comp
    ((contMDiff_fst.comp_contMDiffOn hQ).prodMk
      (contMDiffOn_const.sub (contMDiff_snd.comp_contMDiffOn hQ)))
    (fun y _ => surgeryRetainedInverse_coordinate_mem g₀ N hcut y)

end PoincareConjecture.M36
