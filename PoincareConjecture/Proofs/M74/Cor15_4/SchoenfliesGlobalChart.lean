import PoincareConjecture.Proofs.M74.Cor15_4.PunctureRadiusPartition
import PoincareConjecture.Proofs.M74.Cor15_4.ShiftedPunctureCollar

set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.SurgeryBallEmbedding

open M74 M25.Topology3D

variable {A : GeneralizedSliceCarrier.{u}} (B : SurgeryBallEmbedding A)
  (d : Diffeomorph (𝓡 3) (𝓡 3) A.carrier ThreeSphere ∞)

theorem shiftedPunctureCollar_central_image :
    B.shiftedPunctureCollar d '' (univ ×ˢ {0}) =
      B.punctureChart d '' (B.map '' sphere (0 : StandardCapSpace) (3 / 2)) := by
  ext y
  constructor
  · rintro ⟨⟨q, s⟩, ⟨_, hs⟩, rfl⟩
    have hs0 : s = 0 := hs
    subst s
    refine ⟨B.map ((3 / 2 : ℝ) • q.1), ⟨_, ?_, rfl⟩, ?_⟩
    · rw [mem_sphere_zero_iff_norm, norm_smul, mem_sphere_zero_iff_norm.mp q.2]
      norm_num
    · norm_num [shiftedPunctureCollar, shiftCollar, shiftCollarParam, punctureCollar]
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    let q : UnitTwoSphere := ⟨(2 / 3 : ℝ) • x, by
      rw [mem_sphere_zero_iff_norm, norm_smul, mem_sphere_zero_iff_norm.mp hx]
      norm_num⟩
    refine ⟨(q, 0), ⟨mem_univ _, mem_singleton 0⟩, ?_⟩
    norm_num [shiftedPunctureCollar, shiftCollar, shiftCollarParam, punctureCollar, q, smul_smul]

theorem shiftedPunctureCollar_positive_mem_radiusExterior (q : UnitTwoSphere) {s : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) 1) :
    B.shiftedPunctureCollar d (q, s) ∈
      B.punctureChart d '' (B.map '' Metric.closedBall (0 : StandardCapSpace) (3 / 2))ᶜ := by
  have hs1 : s ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hs.1], hs.2⟩
  have ht := shiftCollarParam_mem hs1
  have hh : 1 / 2 < shiftCollarParam s :=
    (lt_div_iff₀ (by linarith [hs.1] : 0 < 2 + s)).mpr (by linarith [hs.1])
  have hn : ‖(1 + shiftCollarParam s) • q.1‖ = 1 + shiftCollarParam s := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith [ht.1]),
      mem_sphere_zero_iff_norm.mp q.2, mul_one]
  apply mem_image_of_mem
  apply (B.map_mem_radiusExterior_iff (by norm_num) (mem_ball_zero_iff.mpr ?_)).mpr
  · change 3 / 2 < ‖(1 + shiftCollarParam s) • q.1‖
    rw [hn]
    linarith
  · change ‖(1 + shiftCollarParam s) • q.1‖ < 2
    rw [hn]
    linarith [ht.2]

theorem shiftedSchoenflies_inside_eq_radiusExterior {δ : ℝ}
    (D : SchoenfliesData (B.shiftedPunctureCollar d) δ) :
    D.inside = B.punctureChart d ''
      (B.map '' Metric.closedBall (0 : StandardCapSpace) (3 / 2))ᶜ := by
  let U := (B.punctureChart d) ''
    ((B.map '' ball (0 : StandardCapSpace) (3 / 2)) \ {B.map 0})
  let V := (B.punctureChart d) '' (B.map '' Metric.closedBall (0 : StandardCapSpace) (3 / 2))ᶜ
  let S := B.shiftedPunctureCollar d '' (univ ×ˢ {0})
  have hU : IsOpen U := B.punctureChart_image_puncturedBall_isOpen d (by norm_num)
  have hV : IsOpen V := B.punctureChart_radiusExterior_isOpen d (by norm_num) (by norm_num)
  have hUV : Disjoint U V := B.punctureChart_radiusSides_disjoint d (by norm_num)
  have hcover : U ∪ V = Sᶜ := by
    rw [show S = B.punctureChart d '' (B.map '' sphere (0 : StandardCapSpace) (3 / 2)) from
      B.shiftedPunctureCollar_central_image d]
    exact B.punctureChart_radiusSides_union d (by norm_num) (by norm_num)
  have hins : D.inside ⊆ U ∪ V := by
    rw [hcover]
    intro x hx hxs
    exact Set.disjoint_left.mp D.inside_disjoint hx hxs
  obtain ⟨x, hx⟩ := exists_norm_eq StandardCapSpace (by norm_num : (0 : ℝ) ≤ 1)
  let q : UnitTwoSphere := ⟨x, mem_sphere_zero_iff_norm.mpr hx⟩
  have hpV : B.shiftedPunctureCollar d (q, 1 / 2) ∈ V :=
    B.shiftedPunctureCollar_positive_mem_radiusExterior d q (by norm_num)
  have hpD : B.shiftedPunctureCollar d (q, 1 / 2) ∈ D.inside := by
    apply D.collar_inside
    refine ⟨(q, -(1 / 2)), ⟨mem_univ _, by norm_num⟩, ?_⟩
    rw [B.shiftedSchoenflies_side_eq_neg_one d D]
    norm_num
  have hDV : D.inside ⊆ V := D.inside_connected.isPreconnected.subset_right_of_subset_union
    hU hV hUV hins ⟨_, hpD, hpV⟩
  let T := univ \ (D.inside ∪ S)
  have hTU : T ⊆ U := by
    apply D.outside_connected.isPreconnected.subset_left_of_subset_union hU hV hUV
    · intro y hy
      rw [hcover]
      exact fun hys => hy.2 (Or.inr hys)
    · have hnU : B.shiftedPunctureCollar d (q, -(1 / 2)) ∈ U := by
        rw [show U = B.shiftedPunctureCollar d '' (univ ×ˢ Ioo (-1) 0) from
          (B.shiftedPunctureCollar_negative_image d).symm]
        exact mem_image_of_mem _ ⟨mem_univ _, by norm_num⟩
      refine ⟨B.shiftedPunctureCollar d (q, -(1 / 2)), ⟨mem_univ _, ?_⟩, hnU⟩
      rintro (hD | hS)
      · exact Set.disjoint_left.mp hUV hnU (hDV hD)
      · have hnotS : B.shiftedPunctureCollar d (q, -(1 / 2)) ∈ Sᶜ := by
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

theorem shiftedSchoenflies_chart_image_univ {δ : ℝ}
    (D : SchoenfliesData (B.shiftedPunctureCollar d) δ) :
    D.chart '' ball (0 : StandardCapSpace) D.radius = univ := by
  rw [D.chart_image, B.shiftedSchoenflies_inside_eq_radiusExterior d D]
  apply eq_univ_of_forall
  intro y
  by_cases hyS : y ∈ B.shiftedPunctureCollar d '' (univ ×ˢ {0})
  · obtain ⟨⟨q, s⟩, ⟨_, hs⟩, rfl⟩ := hyS
    have hs0 : s = 0 := hs
    subst s
    exact Or.inr ⟨(q, 0), ⟨mem_univ _, by norm_num⟩, by simp⟩
  · rw [B.shiftedPunctureCollar_central_image d] at hyS
    have hyUV : y ∈ B.punctureChart d ''
        ((B.map '' ball (0 : StandardCapSpace) (3 / 2)) \ {B.map 0}) ∪
        B.punctureChart d '' (B.map '' Metric.closedBall (0 : StandardCapSpace) (3 / 2))ᶜ := by
      rw [B.punctureChart_radiusSides_union d (by norm_num) (by norm_num)]
      exact hyS
    rcases hyUV with hyU | hyV
    · rw [← B.shiftedPunctureCollar_negative_image d] at hyU
      obtain ⟨p, hp, rfl⟩ := hyU
      right
      refine ⟨(p.1, -p.2), ⟨mem_univ _, by constructor <;> linarith [hp.2.1, hp.2.2]⟩, ?_⟩
      rw [B.shiftedSchoenflies_side_eq_neg_one d D]
      simp
    · exact Or.inl hyV

end PoincareConjecture.SurgeryBallEmbedding
