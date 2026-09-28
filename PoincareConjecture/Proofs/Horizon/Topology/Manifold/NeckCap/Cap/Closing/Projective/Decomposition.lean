import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.Projective.PunctureBall
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.ProjectiveCoordinates
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.ModelCoordinates
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.Projective.BallComplement
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.SphereCharts.AntipodalNeighborhood
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.CollarMatching
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Separation.ComplementaryDomain

noncomputable section
set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.CapCertificate

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "CylModel" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace E3 M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M}

omit [T2Space M] in

theorem exists_two_cap_projective_enclosing_ball (C D : CapCertificate g)
    (S : StandardPuncturedProjectiveCover M C.puncture C.carrier)
    (a : UnitThreeSphere) (ha : Quotient.mk' a = C.puncture)
    (hcompact : IsCompact (C.carrier ∪ D.carrier)) :
    ∃ b : OpenPartialHomeomorph E3 UnitThreeSphere,
      b.source = univ ∧ b 0 = a ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ b b.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ b.symm b.target ∧
      Disjoint (b '' Metric.closedBall 0 1) (Neg.neg '' (b '' Metric.closedBall 0 1)) ∧
      (C.carrier ∪ D.carrier) \ D.carrier ⊆
        S.cover '' (b '' Metric.closedBall 0 1 ∪ Neg.neg '' (b '' Metric.closedBall 0 1))ᶜ := by
  let K := (C.carrier ∪ D.carrier) \ D.carrier
  have hK : IsCompact K := hcompact.diff D.carrier_open
  have hKC : K ⊆ C.carrier := fun x hx => hx.1.resolve_right hx.2
  obtain ⟨b, hbs, hb0, hb, hbi, hdis, havoid⟩ :=
    S.exists_puncture_ball_avoiding_compact a ha hK hKC
  refine ⟨b, hbs, hb0, hb, hbi, hdis, ?_⟩
  intro x hx
  obtain ⟨y, hyp, hyx⟩ := S.image_eq.symm.subset (hKC hx)
  have hyb : y ∉ b '' Metric.closedBall 0 1 := fun hy => havoid y hy hyp (hyx ▸ hx)
  have hnyp : Quotient.mk' (-y) ≠ C.puncture :=
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

theorem exists_two_cap_projective_matching_ball (C D : CapCertificate g)
    (S : StandardPuncturedProjectiveCover M C.puncture C.carrier)
    (a : UnitThreeSphere) (ha : Quotient.mk' a = C.puncture)
    (hD : D.model_kind = .euclidean)
    (hcompact : IsCompact (C.carrier ∪ D.carrier)) :
    ∃ (r : ℝ) (b : OpenPartialHomeomorph E3 UnitThreeSphere)
        (v : OpenPartialHomeomorph E3 M),
      0 < r ∧ Metric.closedBall 0 1 ⊆ b.source ∧
      Metric.closedBall 0 1 ⊆ v.source ∧ b 0 = a ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ b b.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ b.symm b.target ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ v v.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ v.symm v.target ∧
      Disjoint (b '' Metric.closedBall 0 1) (Neg.neg '' (b '' Metric.closedBall 0 1)) ∧
      Disjoint (v '' Metric.ball 0 1) (S.cover '' ProjectiveGluing.antipodalBallComplement b) ∧
      C.carrier ∪ D.carrier =
        S.cover '' ProjectiveGluing.antipodalBallComplement b ∪ v '' Metric.closedBall 0 1 ∧
      ∀ (q : UnitTwoSphere) (t : ℝ), |t| < r →
        Real.exp t • (q : E3) ∈ b.source ∧
        Real.exp t • (q : E3) ∈ v.source ∧
        S.cover (b (Real.exp t • (q : E3))) = v (Real.exp t • (q : E3)) := by
  obtain ⟨b, hbs, hb0, hb, hbi, hBB, henclose⟩ :=
    C.exists_two_cap_projective_enclosing_ball D S a ha hcompact
  have hbs₁ : Metric.closedBall (0 : E3) 1 ⊆ b.source := by rw [hbs]; exact subset_univ _
  obtain ⟨hKcompact, hKi, hKregular, _, _, _⟩ :=
    ProjectiveGluing.projectiveBallComplement_topology S a ha b hbs₁ hb0 hBB
  let K := S.cover '' ProjectiveGluing.antipodalBallComplement b
  let Y := C.carrier ∪ D.carrier
  let L := Y \ interior K
  have hKC : K ⊆ C.carrier := by
    rintro _ ⟨x, hx, rfl⟩
    exact S.image_eq.subset ⟨x,
      ProjectiveGluing.antipodalBallComplement_avoids_puncture a ha b hb0 hx, rfl⟩
  have hKY : K ⊆ Y := hKC.trans subset_union_left
  have hY : IsClopen Y := ⟨hcompact.isClosed, C.carrier_open.union D.carrier_open⟩
  obtain ⟨hLcompact, hLi, hLregular, hLf⟩ :=
    Poincare.Topology.complementary_domain hY hcompact hKcompact hKY hKregular
  have hLD : L ⊆ D.carrier := Poincare.Topology.complementary_domain_subset
    (hKi.symm ▸ henclose)
  obtain ⟨e, hes, het, he, hei⟩ := D.exists_euclidean_coordinates hD
  obtain ⟨δ, hδ, hsδ, hBBδ⟩ :=
    SphereCharts.exists_exponential_antipodal_ball_neighborhood b hbs₁ hBB
  have hball : Metric.ball (0 : E3) (Real.exp δ) ⊆
      Metric.closedBall 0 (Real.exp (2 * δ)) :=
    Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall
      (Real.exp_le_exp.mpr (by linarith)))
  obtain ⟨c, hcs, hc, hci, hcf, hcfront, _, hcinterior, hct⟩ :=
    ProjectiveGluing.exists_projectiveBallComplement_collar S a ha b hb hbi hb0 hδ
      (hball.trans hsδ) (hBBδ.mono (image_mono hball) (image_mono (image_mono hball)))
  have hzero (q : UnitTwoSphere) : (q, (0 : ℝ)) ∈ c.source := by
    rw [hcs]
    exact ⟨mem_univ _, neg_lt_zero.mpr hδ, hδ⟩
  let W : TopologicalSpace.Opens RoundCylinderSpace := ⟨(c.trans e).source, (c.trans e).open_source⟩
  have hzeroW (q : UnitTwoSphere) : (q, (0 : ℝ)) ∈ W := by
    refine ⟨hzero q, ?_⟩
    change c (q, 0) ∈ e.source
    apply hes.symm ▸ hLD
    apply hLcompact.isClosed.frontier_subset
    rw [hLf, hcfront]
    exact mem_range_self q
  obtain ⟨η, hη, hηW⟩ := CylinderGluing.exists_cylinder_collar W hzeroW
  let ε := min η δ
  have hε : 0 < ε := lt_min hη hδ
  let d := c.restrOpen (univ ×ˢ Ioo (-ε) ε) (isOpen_univ.prod isOpen_Ioo)
  have hds : univ ×ˢ Ioo (-ε) ε ⊆ d.source := by
    intro z hz
    refine ⟨?_, hz⟩
    rw [hcs]
    exact ⟨mem_univ _, abs_lt.mp ((abs_lt.mpr hz.2).trans_le (min_le_right _ _))⟩
  have hdt : d.target ⊆ e.source := by
    intro y hy
    have hzW := hηW (c.symm y)
      ((abs_lt.mpr hy.2.2).trans_le (min_le_left _ _))
    have hzsource : c (c.symm y) ∈ e.source := hzW.2
    simpa only [c.right_inv hy.1] using hzsource
  have hdside (y : M) (hy : y ∈ d.target) : y ∈ L ↔ (d.symm y).2 ≤ 0 := by
    change (y ∈ Y ∧ y ∉ interior K) ↔ (c.symm y).2 ≤ 0
    rw [and_iff_right (show y ∈ Y from Or.inl (hct hy.1)), hcinterior y hy.1, not_lt]
  obtain ⟨r, v, hr, hre, hvs, _, hv, hvi, hvL, hmatch⟩ :=
    Poincare.Manifold.Schoenflies.ball_neighborhood_matching_collar_in_coordinates e het he hei
      hLcompact (hes.symm ▸ hLD) hLregular d (hc.mono inter_subset_left)
      (hci.mono inter_subset_left) hε hds hdt (hLf.trans hcfront) hdside
  have hvopen : v '' Metric.ball 0 1 = Y \ K := by
    rw [v.image_ball_eq_interior hvs hvL]
    exact hLi
  refine ⟨r, b, v, hr, hbs₁, hvs, hb0, hb, hbi, hv, hvi, hBB, ?_, ?_, ?_⟩
  · rw [hvopen]
    exact disjoint_sdiff_left
  · rw [hvL]
    apply Subset.antisymm
    · intro x hx
      by_cases hxK : x ∈ K
      · exact Or.inl hxK
      · exact Or.inr ⟨hx, fun hi => hxK (interior_subset hi)⟩
    · exact union_subset hKY sdiff_subset
  · intro q t ht
    obtain ⟨hsource, hvalue⟩ := hmatch (q, t) ht
    have htc : (q, t) ∈ c.source := by
      rw [hcs]
      exact ⟨mem_univ _, abs_lt.mp (ht.trans (hre.trans_le (min_le_right _ _)))⟩
    exact ⟨hbs.symm ▸ mem_univ _, hsource, (hcf _ htc).symm.trans hvalue.symm⟩

end PoincareConjecture.CapCertificate
