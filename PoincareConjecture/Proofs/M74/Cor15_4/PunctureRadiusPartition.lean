import PoincareConjecture.Proofs.M74.Cor15_4.PuncturedSphereStandardEnd

set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.SurgeryBallEmbedding

variable {A : GeneralizedSliceCarrier.{u}} (B : SurgeryBallEmbedding A)
  (d : Diffeomorph (𝓡 3) (𝓡 3) A.carrier ThreeSphere ∞)

theorem image_closedBall_isClosed {r : ℝ} (hr2 : r < 2) :
    IsClosed (B.map '' Metric.closedBall (0 : StandardCapSpace) r) :=
  ((isCompact_closedBall (0 : StandardCapSpace) r).image_of_continuousOn
    (B.map_smooth.continuousOn.mono (closedBall_subset_ball hr2))).isClosed

theorem radiusExterior_subset_punctureChart_source {r : ℝ} (hr : 0 < r) :
    (B.map '' Metric.closedBall (0 : StandardCapSpace) r)ᶜ ⊆ (B.punctureChart d).source := by
  intro x hx
  apply B.map_ball_compl_subset_punctureChart_source d hr
  exact fun hxball => hx (image_mono ball_subset_closedBall hxball)

theorem punctureChart_radiusExterior_isOpen {r : ℝ} (hr : 0 < r) (hr2 : r < 2) :
    IsOpen ((B.punctureChart d) '' (B.map '' Metric.closedBall (0 : StandardCapSpace) r)ᶜ) :=
  (B.punctureChart d).isOpen_image_of_subset_source (B.image_closedBall_isClosed hr2).isOpen_compl
    (B.radiusExterior_subset_punctureChart_source d hr)

private theorem radius_sphere_mem_ball {r : ℝ} (hr2 : r < 2)
    {x : StandardCapSpace} (hx : x ∈ sphere 0 r) : x ∈ ball 0 2 := by
  rw [mem_ball_zero_iff, mem_sphere_zero_iff_norm.mp hx]
  exact hr2

theorem radiusSphere_image_mem_source {r : ℝ} (hr : 0 < r) (hr2 : r < 2)
    {x : StandardCapSpace} (hx : x ∈ sphere 0 r) :
    B.map x ∈ (B.punctureChart d).source := by
  apply (B.map_mem_punctureChart_source_iff d (radius_sphere_mem_ball hr2 hx)).mpr
  apply norm_pos_iff.mp
  rwa [mem_sphere_zero_iff_norm.mp hx]

theorem punctureChart_radiusSides_disjoint {r : ℝ} (hr : 0 < r) :
    Disjoint ((B.punctureChart d) ''
      ((B.map '' ball (0 : StandardCapSpace) r) \ {B.map 0}))
      ((B.punctureChart d) '' (B.map '' Metric.closedBall (0 : StandardCapSpace) r)ᶜ) := by
  apply Set.disjoint_left.mpr
  rintro y ⟨a, ⟨ha, hane⟩, hay⟩ ⟨b, hb, hby⟩
  have has : a ∈ (B.punctureChart d).source := by
    simpa only [B.punctureChart_source d, mem_compl_iff] using hane
  have hab := (B.punctureChart d).injOn has
    (B.radiusExterior_subset_punctureChart_source d hr hb) (hay.trans hby.symm)
  subst b
  exact hb (image_mono ball_subset_closedBall ha)

theorem punctureChart_radiusSides_union {r : ℝ} (hr : 0 < r) (hr2 : r < 2) :
    ((B.punctureChart d) ''
      ((B.map '' ball (0 : StandardCapSpace) r) \ {B.map 0})) ∪
      ((B.punctureChart d) '' (B.map '' Metric.closedBall (0 : StandardCapSpace) r)ᶜ) =
        ((B.punctureChart d) '' (B.map '' sphere (0 : StandardCapSpace) r))ᶜ := by
  ext y
  constructor
  · rintro (⟨a, ⟨⟨x, hx, hxa⟩, hane⟩, hay⟩ | ⟨a, ha, hay⟩) hy
    · obtain ⟨_, ⟨z, hz, rfl⟩, hzy⟩ := hy
      have has : a ∈ (B.punctureChart d).source := by
        simpa only [B.punctureChart_source d, mem_compl_iff] using hane
      have haz := (B.punctureChart d).injOn has (B.radiusSphere_image_mem_source d hr hr2 hz)
        (hay.trans hzy.symm)
      have hxz := B.left_inverse.injOn (ball_subset_ball hr2.le hx)
        (radius_sphere_mem_ball hr2 hz) (hxa.trans haz)
      subst z
      have := mem_ball_zero_iff.mp hx
      rw [mem_sphere_zero_iff_norm.mp hz] at this
      exact lt_irrefl _ this
    · obtain ⟨_, ⟨z, hz, rfl⟩, hzy⟩ := hy
      have haz := (B.punctureChart d).injOn
        (B.radiusExterior_subset_punctureChart_source d hr ha)
        (B.radiusSphere_image_mem_source d hr hr2 hz) (hay.trans hzy.symm)
      exact ha (haz ▸ mem_image_of_mem B.map (sphere_subset_closedBall hz))
  · intro hy
    have hyt : y ∈ (B.punctureChart d).target := by simp
    have has := (B.punctureChart d).map_target hyt
    have hay := (B.punctureChart d).right_inv hyt
    by_cases ha : (B.punctureChart d).symm y ∈ B.map '' Metric.closedBall (0 : StandardCapSpace) r
    · obtain ⟨x, hx, hxa⟩ := ha
      have hn : ‖x‖ < r := by
        apply lt_of_le_of_ne (mem_closedBall_zero_iff.mp hx)
        intro heq
        apply hy
        exact ⟨B.map x, ⟨x, mem_sphere_zero_iff_norm.mpr heq, rfl⟩,
          (congrArg (B.punctureChart d) hxa).trans hay⟩
      left
      refine ⟨(B.punctureChart d).symm y, ⟨⟨x, mem_ball_zero_iff.mpr hn, hxa⟩, ?_⟩, hay⟩
      simpa only [B.punctureChart_source d, mem_compl_iff] using has
    · exact Or.inr ⟨_, ha, hay⟩

theorem map_mem_radiusExterior_iff {r : ℝ} (hr2 : r < 2)
    {x : StandardCapSpace} (hx : x ∈ ball 0 2) :
    B.map x ∈ (B.map '' Metric.closedBall (0 : StandardCapSpace) r)ᶜ ↔ r < ‖x‖ := by
  constructor
  · intro h
    by_contra hn
    exact h ⟨x, mem_closedBall_zero_iff.mpr (le_of_not_gt hn), rfl⟩
  · rintro h ⟨y, hy, heq⟩
    have hxy : y = x := B.left_inverse.injOn (closedBall_subset_ball hr2 hy) hx heq
    subst y
    exact (not_le_of_gt h) (mem_closedBall_zero_iff.mp hy)

end PoincareConjecture.SurgeryBallEmbedding
