import PoincareConjecture.Proofs.M74.Cor15_4.PuncturedSphereCollar
import PoincareConjecture.Proofs.M74.Cor15_4.PuncturedSphereExterior
import PoincareConjecture.Proofs.M74.ServiceMirror

set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.SurgeryBallEmbedding

open M25.Topology3D

variable {A : GeneralizedSliceCarrier.{u}} (B : SurgeryBallEmbedding A)
  (d : Diffeomorph (𝓡 3) (𝓡 3) A.carrier ThreeSphere ∞)

private theorem sphere_mem_ball {x : StandardCapSpace} (hx : x ∈ sphere 0 1) :
    x ∈ ball 0 2 := by
  rw [mem_ball_zero_iff, mem_sphere_zero_iff_norm.mp hx]
  norm_num

private theorem sphere_image_mem_source {x : StandardCapSpace} (hx : x ∈ sphere 0 1) :
    B.map x ∈ (B.punctureChart d).source := by
  apply (B.map_mem_punctureChart_source_iff d (sphere_mem_ball hx)).mpr
  intro h
  have := mem_sphere_zero_iff_norm.mp hx
  simp [h] at this

theorem punctureCollar_central_image :
    B.punctureCollar d '' (univ ×ˢ {0}) =
      B.punctureChart d '' (B.map '' sphere (0 : StandardCapSpace) 1) := by
  ext y
  constructor
  · rintro ⟨⟨q, s⟩, ⟨_, hs⟩, rfl⟩
    have hs0 : s = 0 := hs
    subst s
    exact ⟨B.map q.1, ⟨q.1, q.2, rfl⟩, by simp [punctureCollar]⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨(⟨x, hx⟩, 0), ⟨mem_univ _, mem_singleton 0⟩, by simp [punctureCollar]⟩

theorem punctureChart_image_puncturedBall_isOpen {r : ℝ} (hr : r ≤ 2) :
    IsOpen ((B.punctureChart d) ''
      ((B.map '' ball (0 : StandardCapSpace) r) \ {B.map 0})) := by
  apply (B.punctureChart d).isOpen_image_of_subset_source
    ((B.map_ball_isOpen hr).sdiff isClosed_singleton)
  intro x hx
  simpa only [B.punctureChart_source d, mem_compl_iff] using hx.2

theorem punctureChart_interior_disjoint_exterior :
    Disjoint ((B.punctureChart d) ''
      ((B.map '' ball (0 : StandardCapSpace) 1) \ {B.map 0}))
      ((B.punctureChart d) '' B.closedBallᶜ) := by
  apply Set.disjoint_left.mpr
  rintro y ⟨a, ⟨ha, hane⟩, hay⟩ ⟨b, hb, hby⟩
  have has : a ∈ (B.punctureChart d).source := by
    simpa only [B.punctureChart_source d, mem_compl_iff] using hane
  have hab := (B.punctureChart d).injOn has
    (B.closedBall_compl_subset_punctureChart_source d hb) (hay.trans hby.symm)
  subst b
  exact hb (image_mono ball_subset_closedBall ha)

theorem punctureChart_interior_union_exterior :
    ((B.punctureChart d) ''
      ((B.map '' ball (0 : StandardCapSpace) 1) \ {B.map 0})) ∪
      ((B.punctureChart d) '' B.closedBallᶜ) =
        (B.punctureCollar d '' (univ ×ˢ {0}))ᶜ := by
  rw [B.punctureCollar_central_image d]
  ext y
  constructor
  · rintro (⟨a, ⟨⟨x, hx, hxa⟩, hane⟩, hay⟩ | ⟨a, ha, hay⟩) hy
    · obtain ⟨_, ⟨z, hz, rfl⟩, hzy⟩ := hy
      have has : a ∈ (B.punctureChart d).source := by
        simpa only [B.punctureChart_source d, mem_compl_iff] using hane
      have haz := (B.punctureChart d).injOn has (B.sphere_image_mem_source d hz)
        (hay.trans hzy.symm)
      have hxz := B.left_inverse.injOn (ball_subset_ball (by norm_num) hx)
        (sphere_mem_ball hz) (hxa.trans haz)
      subst z
      have := mem_ball_zero_iff.mp hx
      rw [mem_sphere_zero_iff_norm.mp hz] at this
      exact (lt_irrefl _ this)
    · obtain ⟨_, ⟨z, hz, rfl⟩, hzy⟩ := hy
      have haz := (B.punctureChart d).injOn
        (B.closedBall_compl_subset_punctureChart_source d ha)
        (B.sphere_image_mem_source d hz) (hay.trans hzy.symm)
      exact ha (haz ▸ mem_image_of_mem B.map (sphere_subset_closedBall hz))
  · intro hy
    have hyt : y ∈ (B.punctureChart d).target := by simp
    have has := (B.punctureChart d).map_target hyt
    have hay := (B.punctureChart d).right_inv hyt
    by_cases ha : (B.punctureChart d).symm y ∈ B.closedBall
    · obtain ⟨x, hx, hxa⟩ := ha
      have hn : ‖x‖ < 1 := by
        apply lt_of_le_of_ne (mem_closedBall_zero_iff.mp hx)
        intro heq
        apply hy
        exact ⟨B.map x, ⟨x, mem_sphere_zero_iff_norm.mpr heq, rfl⟩,
          (congrArg (B.punctureChart d) hxa).trans hay⟩
      left
      refine ⟨(B.punctureChart d).symm y, ⟨⟨x, mem_ball_zero_iff.mpr hn, hxa⟩, ?_⟩, hay⟩
      simpa only [B.punctureChart_source d, mem_compl_iff] using has
    · exact Or.inr ⟨_, ha, hay⟩

theorem punctureCollar_positive_mem_exterior (q : UnitTwoSphere) {s : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) 1) :
    B.punctureCollar d (q, s) ∈ (B.punctureChart d) '' B.closedBallᶜ := by
  exact mem_image_of_mem _ (B.radial_mem_complement q ⟨by linarith [hs.1],
    by linarith [hs.2]⟩)

theorem schoenflies_side_eq_neg_one {δ : ℝ} (D : SchoenfliesData (B.punctureCollar d) δ) :
    D.side = -1 :=
  B.punctureCollar_side_eq_neg_one d D.side D.side_sq D.inside_bounded D.collar_inside

theorem schoenflies_inside_eq_exterior {δ : ℝ}
    (D : SchoenfliesData (B.punctureCollar d) δ) :
    D.inside = (B.punctureChart d) '' B.closedBallᶜ := by
  let U := (B.punctureChart d) ''
    ((B.map '' ball (0 : StandardCapSpace) 1) \ {B.map 0})
  let V := (B.punctureChart d) '' B.closedBallᶜ
  let S := B.punctureCollar d '' (univ ×ˢ {0})
  have hU : IsOpen U := B.punctureChart_image_puncturedBall_isOpen d (by norm_num)
  have hV : IsOpen V := B.punctureChart_image_closedBall_compl_isOpen d
  have hUV : Disjoint U V := B.punctureChart_interior_disjoint_exterior d
  have hcover : U ∪ V = Sᶜ := B.punctureChart_interior_union_exterior d
  have hins : D.inside ⊆ U ∪ V := by
    rw [hcover]
    intro x hx hxs
    exact Set.disjoint_left.mp D.inside_disjoint hx hxs
  obtain ⟨x, hx⟩ := exists_norm_eq StandardCapSpace (by norm_num : (0 : ℝ) ≤ 1)
  let q : UnitTwoSphere := ⟨x, mem_sphere_zero_iff_norm.mpr hx⟩
  have hpV : B.punctureCollar d (q, 1 / 2) ∈ V :=
    B.punctureCollar_positive_mem_exterior d q (by norm_num)
  have hpD : B.punctureCollar d (q, 1 / 2) ∈ D.inside := by
    apply D.collar_inside
    refine ⟨(q, -(1 / 2)), ⟨mem_univ _, by norm_num⟩, ?_⟩
    rw [B.schoenflies_side_eq_neg_one d D]
    norm_num
  have hDV : D.inside ⊆ V := D.inside_connected.isPreconnected.subset_right_of_subset_union
    hU hV hUV hins ⟨_, hpD, hpV⟩
  let T := univ \ (D.inside ∪ S)
  have hTU : T ⊆ U := by
    apply D.outside_connected.isPreconnected.subset_left_of_subset_union hU hV hUV
    · intro y hy
      rw [hcover]
      exact fun hys => hy.2 (Or.inr hys)
    · have hnU : B.punctureCollar d (q, -(1 / 2)) ∈ U := by
        rw [show U = B.punctureCollar d '' (univ ×ˢ Ioo (-1) 0) from
          (B.punctureCollar_negative_image d).symm]
        exact mem_image_of_mem _ ⟨mem_univ _, by norm_num⟩
      refine ⟨B.punctureCollar d (q, -(1 / 2)), ⟨mem_univ _, ?_⟩, hnU⟩
      rintro (hD | hS)
      · exact Set.disjoint_left.mp hUV hnU (hDV hD)
      · have hnotS : B.punctureCollar d (q, -(1 / 2)) ∈ Sᶜ := by
          rw [← hcover]
          exact Or.inl hnU
        exact hnotS hS
  apply subset_antisymm hDV
  intro y hy
  by_contra hyD
  have hyS : y ∈ Sᶜ := by
    rw [← hcover]
    exact Or.inr hy
  have hyT : y ∈ T := ⟨mem_univ _, fun h => h.elim hyD hyS⟩
  exact Set.disjoint_left.mp hUV (hTU hyT) hy

end PoincareConjecture.SurgeryBallEmbedding
