import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.Projective.PunctureBall
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.Projective.BallComplement
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.SphereCharts.AntipodalNeighborhood
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Separation.ComplementaryDomain
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.Coordinates.Affine











set_option autoImplicit false

open Set TopologicalSpace Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.ClosedModels

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "CylModel" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

variable {M : Type u} [TopologicalSpace M] [ChartedSpace E3 M]
  [T2Space M]



theorem exists_projective_complementary_collar
    (U V : Opens M) {p : RealProjectiveThree}
    (S : StandardPuncturedProjectiveCover M p (U : Set M))
    (a : UnitThreeSphere) (ha : Quotient.mk' a = p)
    (hcompact : IsCompact ((U : Set M) ∪ V)) :
    ∃ (δ : ℝ) (b : OpenPartialHomeomorph E3 UnitThreeSphere)
        (c : OpenPartialHomeomorph RoundCylinderSpace M),
      0 < δ ∧ b.source = univ ∧ b 0 = a ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ b b.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ b.symm b.target ∧
      Disjoint (b '' Metric.closedBall 0 1) (Neg.neg '' (b '' Metric.closedBall 0 1)) ∧
      c.source = univ ×ˢ Ioo (-δ) δ ∧ c.target ⊆ (U : Set M) ∩ V ∧
      ContMDiffOn CylModel (𝓡 3) ∞ c c.source ∧
      ContMDiffOn (𝓡 3) CylModel ∞ c.symm c.target ∧
      (∀ z ∈ c.source, c z = S.cover (b (Real.exp z.2 • (z.1 : E3)))) ∧
      let K := S.cover '' ProjectiveGluing.antipodalBallComplement b
      let L := ((U : Set M) ∪ V) \ interior K
      IsCompact L ∧ L ⊆ V ∧ closure (interior L) = L ∧
      frontier L = range (fun q : UnitTwoSphere => c (q, 0)) ∧
      (∀ y ∈ c.target, y ∈ L ↔ (c.symm y).2 ≤ 0) ∧
      (∀ y ∈ c.target, y ∈ interior L ↔ (c.symm y).2 < 0) := by
  let A := ((U : Set M) ∪ V) \ V
  have hA : IsCompact A := hcompact.diff V.isOpen
  have hAU : A ⊆ U := fun x hx => hx.1.resolve_right hx.2
  obtain ⟨b, hbs, hb0, hb, hbi, hBB, havoid⟩ :=
    S.exists_puncture_ball_avoiding_compact a ha hA hAU
  have henclose : A ⊆
      S.cover '' (b '' Metric.closedBall 0 1 ∪ Neg.neg '' (b '' Metric.closedBall 0 1))ᶜ := by
    intro x hx
    obtain ⟨y, hyp, hyx⟩ := S.image_eq.symm.subset (hAU hx)
    have hyb : y ∉ b '' Metric.closedBall 0 1 := fun hy => havoid y hy hyp (hyx ▸ hx)
    have hnyp : Quotient.mk' (-y) ≠ p :=
      (PuncturedProjectiveSphere.antipode ⟨y, hyp⟩).property
    have hnyx : S.cover (-y) = x :=
      ((S.fibers (-y) y hnyp hyp).mpr (Or.inr rfl)).trans hyx
    refine ⟨y, ?_, hyx⟩
    rintro (hy | ⟨z, hz, hzy⟩)
    · exact hyb hy
    · have hny : -y ∈ b '' Metric.closedBall 0 1 := by
        rw [← hzy, neg_neg]
        exact hz
      exact havoid (-y) hny hnyp (hnyx ▸ hx)
  have hbs₁ : Metric.closedBall (0 : E3) 1 ⊆ b.source := by rw [hbs]; exact subset_univ _
  obtain ⟨hKcompact, hKi, hKregular, _, _, _⟩ :=
    ProjectiveGluing.projectiveBallComplement_topology S a ha b hbs₁ hb0 hBB
  let K := S.cover '' ProjectiveGluing.antipodalBallComplement b
  let Y := (U : Set M) ∪ V
  let L := Y \ interior K
  have hKU : K ⊆ U := by
    rintro _ ⟨x, hx, rfl⟩
    exact S.image_eq.subset ⟨x,
      ProjectiveGluing.antipodalBallComplement_avoids_puncture a ha b hb0 hx, rfl⟩
  have hKY : K ⊆ Y := hKU.trans subset_union_left
  have hY : IsClopen Y := ⟨hcompact.isClosed, U.isOpen.union V.isOpen⟩
  obtain ⟨hLcompact, hLi, hLregular, hLf⟩ :=
    Poincare.Topology.complementary_domain hY hcompact hKcompact hKY hKregular
  have hLV : L ⊆ V := Poincare.Topology.complementary_domain_subset
    (hKi.symm ▸ henclose)
  obtain ⟨δ, hδ, hsδ, hBBδ⟩ :=
    SphereCharts.exists_exponential_antipodal_ball_neighborhood b hbs₁ hBB
  have hball : Metric.ball (0 : E3) (Real.exp δ) ⊆
      Metric.closedBall 0 (Real.exp (2 * δ)) :=
    Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall
      (Real.exp_le_exp.mpr (by linarith)))
  obtain ⟨c, hcs, hc, hci, hcf, hcfront, hcside, hcinterior, hct⟩ :=
    ProjectiveGluing.exists_projectiveBallComplement_collar S a ha b hb hbi hb0 hδ
      (hball.trans hsδ) (hBBδ.mono (image_mono hball) (image_mono (image_mono hball)))
  have hzero (q : UnitTwoSphere) : (q, (0 : ℝ)) ∈ c.source :=
    hcs.symm ▸ ⟨mem_univ _, neg_lt_zero.mpr hδ, hδ⟩
  let W : Opens RoundCylinderSpace :=
    ⟨c.source ∩ c ⁻¹' (V : Set M),
      c.continuousOn.isOpen_inter_preimage c.open_source V.isOpen⟩
  have hzeroW (q : UnitTwoSphere) : (q, (0 : ℝ)) ∈ W := by
    refine ⟨hzero q, hLV ?_⟩
    apply hLcompact.isClosed.frontier_subset
    rw [hLf, hcfront]
    exact mem_range_self q
  obtain ⟨η, hη, hηW⟩ := CylinderGluing.exists_cylinder_collar W hzeroW
  let ε := min η δ
  have hε : 0 < ε := lt_min hη hδ
  let d := c.restrOpen (univ ×ˢ Ioo (-ε) ε) (isOpen_univ.prod isOpen_Ioo)
  have hslab : univ ×ˢ Ioo (-ε) ε ⊆ c.source := by
    intro z hz
    rw [hcs]
    exact ⟨mem_univ _, abs_lt.mp ((abs_lt.mpr hz.2).trans_le (min_le_right _ _))⟩
  have hds : d.source = univ ×ˢ Ioo (-ε) ε := inter_eq_right.mpr hslab
  have hdt : d.target ⊆ (U : Set M) ∩ V := by
    intro y hy
    have hzW := hηW (c.symm y)
      ((abs_lt.mpr hy.2.2).trans_le (min_le_left _ _))
    have hzV : c (c.symm y) ∈ V := hzW.2
    change c (c.symm y) ∈ (V : Set M) at hzV
    rw [c.right_inv hy.1] at hzV
    exact ⟨hct hy.1, hzV⟩
  refine ⟨ε, b, d, hε, hbs, hb0, hb, hbi, hBB, hds, hdt,
    hc.mono inter_subset_left, hci.mono inter_subset_left,
    (fun z hz => hcf z hz.1), hLcompact, hLV, hLregular, ?_, ?_, ?_⟩
  · exact hLf.trans hcfront
  · intro y hy
    change (y ∈ Y ∧ y ∉ interior K) ↔ (c.symm y).2 ≤ 0
    rw [and_iff_right (show y ∈ Y from Or.inl (hct hy.1))]
    change (y ∉ interior (S.cover '' ProjectiveGluing.antipodalBallComplement b)) ↔ _
    rw [hcinterior y hy.1, not_lt]
  · intro y hy
    rw [hLi]
    change (y ∈ Y ∧ y ∉ K) ↔ (c.symm y).2 < 0
    rw [and_iff_right (show y ∈ Y from Or.inl (hct hy.1))]
    change (y ∉ S.cover '' ProjectiveGluing.antipodalBallComplement b) ↔ _
    rw [hcside y hy.1, not_le]

end PoincareConjecture.ClosedModels
