import PoincareConjecture.Proofs.M25.Topology3D.Space3.CollarCoordinates
import PoincareConjecture.Proofs.M25.Topology3D.Space3.BallRegionSides












set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D



theorem ball_collar_halves (ψ : UnitTwoSphere × ℝ → E3) (hψ : IsCollarEmbedding ψ)
    (B : BallNeighborhoodChart E3 E3)
    (hboundary : B.boundary = ψ '' (univ ×ˢ {0})) :
    (ψ '' (univ ×ˢ Ioo (-1) 0) ⊆ B.inside ∧
      ψ '' (univ ×ˢ Ioo 0 1) ⊆ B.closedRegionᶜ) ∨
    (ψ '' (univ ×ˢ Ioo (-1) 0) ⊆ B.closedRegionᶜ ∧
      ψ '' (univ ×ˢ Ioo 0 1) ⊆ B.inside) := by
  let N := ψ '' (univ ×ˢ Ioo (-1) 0)
  let P := ψ '' (univ ×ˢ Ioo 0 1)
  let U := ψ '' (univ ×ˢ Ioo (-1) 1)
  have hdim : 1 < Module.rank ℝ E3 :=
    Module.one_lt_rank_of_one_lt_finrank (by simp [E3])
  have hS : IsPreconnected (univ : Set UnitTwoSphere) := by
    let : PreconnectedSpace UnitTwoSphere := Subtype.preconnectedSpace
      (isPreconnected_sphere hdim (0 : E3) 1)
    exact isPreconnected_univ
  have hN : IsPreconnected N := (hS.prod isPreconnected_Ioo).image ψ
    (hψ.1.continuousOn.mono fun p hp => ⟨hp.1, hp.2.1, hp.2.2.trans zero_lt_one⟩)
  have hP : IsPreconnected P := (hS.prod isPreconnected_Ioo).image ψ
    (hψ.1.continuousOn.mono fun p hp => ⟨hp.1, (by norm_num : (-1 : ℝ) < 0).trans hp.2.1,
      hp.2.2⟩)
  have hnot (p : UnitTwoSphere × ℝ) (hp : p.2 ∈ Ioo (-1) 1) (hp0 : p.2 ≠ 0) :
      ψ p ∉ B.boundary := by
    rw [hboundary]
    rintro ⟨q, hq, heq⟩
    have hq0 : q.2 = 0 := hq.2
    have hqfull : q ∈ (univ ×ˢ Ioo (-1) 1 : Set (UnitTwoSphere × ℝ)) := by
      refine ⟨mem_univ _, ?_⟩
      rw [hq0]
      norm_num
    have hpq := hψ.2.1 ⟨mem_univ _, hp⟩ hqfull heq.symm
    exact hp0 ((congrArg Prod.snd hpq).trans hq0)
  have hcover (y : E3) (hy : y ∉ B.boundary) : y ∈ B.inside ∪ B.closedRegionᶜ := by
    by_cases hin : y ∈ B.inside
    · exact Or.inl hin
    · right
      intro hclosed
      rw [← B.inside_union_boundary] at hclosed
      exact hclosed.elim hin hy
  have hNcover : N ⊆ B.inside ∪ B.closedRegionᶜ := by
    rintro y ⟨p, hp, rfl⟩
    exact hcover _ (hnot p ⟨hp.2.1, hp.2.2.trans zero_lt_one⟩ hp.2.2.ne)
  have hPcover : P ⊆ B.inside ∪ B.closedRegionᶜ := by
    rintro y ⟨p, hp, rfl⟩
    exact hcover _ (hnot p ⟨(by norm_num : (-1 : ℝ) < 0).trans hp.2.1,
      hp.2.2⟩ hp.2.1.ne')
  have hIO : Disjoint B.inside B.closedRegionᶜ := Set.disjoint_left.mpr fun _ hin hout =>
    hout (image_mono ball_subset_closedBall hin)
  have hNside := hN.subset_or_subset B.inside_open B.closedRegion_compact.isClosed.isOpen_compl
    hIO hNcover
  have hPside := hP.subset_or_subset B.inside_open B.closedRegion_compact.isClosed.isOpen_compl
    hIO hPcover
  have hhalf (y : E3) (hy : y ∈ U) (hyB : y ∉ B.boundary) : y ∈ N ∪ P := by
    obtain ⟨p, hp, rfl⟩ := hy
    have hp0 : p.2 ≠ 0 := by
      intro hz
      apply hyB
      rw [hboundary]
      exact ⟨p, ⟨mem_univ _, hz⟩, rfl⟩
    rcases lt_or_gt_of_ne hp0 with hn | hp'
    · exact Or.inl ⟨p, ⟨hp.1, hp.2.1, hn⟩, rfl⟩
    · exact Or.inr ⟨p, ⟨hp.1, hp', hp.2.2⟩, rfl⟩
  obtain ⟨x, hx⟩ := NormedSpace.sphere_nonempty (E := E3) (x := 0) |>.mpr zero_le_one
  let q : UnitTwoSphere := ⟨x, hx⟩
  have hqB : ψ (q, 0) ∈ B.boundary := by
    rw [hboundary]
    exact ⟨(q, 0), ⟨mem_univ _, rfl⟩, rfl⟩
  have hqU : ψ (q, 0) ∈ U := ⟨(q, 0), ⟨mem_univ _, by norm_num⟩, rfl⟩
  have hsides := B.boundary_subset_closure_sides hqB
  have hU : IsOpen U := collar_image_open ψ hψ
  obtain ⟨yi, hyiU, hyi⟩ := mem_closure_iff.mp hsides.1 U hU hqU
  obtain ⟨yo, hyoU, hyo⟩ := mem_closure_iff.mp hsides.2 U hU hqU
  have hyihalf : yi ∈ N ∪ P := hhalf yi hyiU
    (fun hbd => Set.disjoint_left.mp B.inside_disjoint_boundary hyi hbd)
  have hyohalf : yo ∈ N ∪ P := hhalf yo hyoU
    (fun hbd => hyo (image_mono sphere_subset_closedBall hbd))
  change (N ⊆ B.inside ∧ P ⊆ B.closedRegionᶜ) ∨
    (N ⊆ B.closedRegionᶜ ∧ P ⊆ B.inside)
  rcases hNside with hNi | hNo <;> rcases hPside with hPi | hPo
  · exact (Set.disjoint_left.mp hIO
      (hyohalf.elim (fun h => hNi h) (fun h => hPi h)) hyo).elim
  · exact Or.inl ⟨hNi, hPo⟩
  · exact Or.inr ⟨hNo, hPi⟩
  · exact (Set.disjoint_left.mp hIO hyi
      (hyihalf.elim (fun h => hNo h) (fun h => hPo h))).elim



theorem exists_ball_collar_orientation (ψ : UnitTwoSphere × ℝ → E3)
    (hψ : IsCollarEmbedding ψ) (B : BallNeighborhoodChart E3 E3)
    (hboundary : B.boundary = ψ '' (univ ×ˢ {0})) :
    ∃ side : ℝ, side * side = 1 ∧
      (fun p : UnitTwoSphere × ℝ => ψ (p.1, side * p.2)) ''
        (univ ×ˢ Ioo (-1) 0) ⊆ B.inside ∧
      (fun p : UnitTwoSphere × ℝ => ψ (p.1, side * p.2)) ''
        (univ ×ˢ Ioo 0 1) ⊆ B.closedRegionᶜ := by
  rcases ball_collar_halves ψ hψ B hboundary with ⟨hN, hP⟩ | ⟨hN, hP⟩
  · refine ⟨1, by norm_num, ?_, ?_⟩
    · simpa only [one_mul, Prod.eta] using hN
    · simpa only [one_mul, Prod.eta] using hP
  · refine ⟨-1, by norm_num, ?_, ?_⟩
    · rintro y ⟨⟨q, s⟩, ⟨_, hs⟩, rfl⟩
      simp only [neg_one_mul]
      exact hP ⟨(q, -s), ⟨mem_univ _, by constructor <;> linarith [hs.1, hs.2]⟩, rfl⟩
    · rintro y ⟨⟨q, s⟩, ⟨_, hs⟩, rfl⟩
      simp only [neg_one_mul]
      exact hN ⟨(q, -s), ⟨mem_univ _, by constructor <;> linarith [hs.1, hs.2]⟩, rfl⟩

end PoincareConjecture.M25.Topology3D
