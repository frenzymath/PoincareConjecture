import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.ClosedModels.ProjectiveComplement
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.Projective.CompactRegion
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.BallExtension.MatchingBoundary
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.EssentialSphere.Embedding
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Closing.Projective.Certificate
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Closing.Projective.DoubleCertificate

set_option autoImplicit false

open Set TopologicalSpace Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.ClosedModels

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "CylModel" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

variable {M : Type u} [TopologicalSpace M] [ChartedSpace E3 M]
  [IsManifold (𝓡 3) ∞ M] [T2Space M]

theorem nonempty_projective_pair_certificate
    (U V : Opens M) {p q : RealProjectiveThree}
    (S : StandardPuncturedProjectiveCover M p (U : Set M))
    (T : StandardPuncturedProjectiveCover M q (V : Set M))
    (hcompact : IsCompact ((U : Set M) ∪ V))
    (hcomponent : ∃ x : M, (U : Set M) ∪ V = connectedComponent x) :
    ∃ kind : ClosedComponentKind,
      Nonempty (ClosedComponentCertificate kind ((U : Set M) ∪ V)) := by
  classical
  obtain ⟨a, ha⟩ := Quotient.mk'_surjective p
  obtain ⟨δ, b, c, hδ, hbs, hb0, hb, hbi, hBB, hcs, hct, hc, hci, hcf,
    hLcompact, hLV, hLregular, hLfront, hLside, hLiSide⟩ :=
    exists_projective_complementary_collar U V S a ha hcompact
  let K := S.cover '' ProjectiveGluing.antipodalBallComplement b
  let Y : Opens M := ⟨(U : Set M) ∪ V, U.isOpen.union V.isOpen⟩
  let L := (Y : Set M) \ interior K
  change frontier L = range (fun q : UnitTwoSphere => c (q, 0)) at hLfront
  change ∀ y ∈ c.target, y ∈ L ↔ (c.symm y).2 ≤ 0 at hLside
  have hbs₁ : Metric.closedBall (0 : E3) 1 ⊆ b.source := by rw [hbs]; exact subset_univ _
  obtain ⟨hKcompact, _, hKregular, _, _, _⟩ :=
    ProjectiveGluing.projectiveBallComplement_topology S a ha b hbs₁ hb0 hBB
  have hKY : K ⊆ Y := by
    rintro _ ⟨x, hx, rfl⟩
    exact Or.inl (S.image_eq.subset ⟨x,
      ProjectiveGluing.antipodalBallComplement_avoids_puncture a ha b hb0 hx, rfl⟩)
  obtain ⟨_, hLi, _, hLf⟩ := Poincare.Topology.complementary_domain
    (show IsClopen (Y : Set M) from ⟨hcompact.isClosed, Y.isOpen⟩)
    hcompact hKcompact hKY hKregular
  have hzero (q : UnitTwoSphere) : (q, (0 : ℝ)) ∈ c.source :=
    hcs.symm ▸ ⟨mem_univ _, neg_lt_zero.mpr hδ, hδ⟩
  have hzeroImage : c '' (univ ×ˢ ({0} : Set ℝ)) = frontier L := by
    rw [hLfront]
    ext x
    constructor
    · rintro ⟨⟨q, t⟩, ⟨_, ht⟩, rfl⟩
      have ht0 : t = 0 := ht
      subst t
      exact mem_range_self q
    · rintro ⟨q, rfl⟩
      exact ⟨(q, 0), ⟨mem_univ _, rfl⟩, rfl⟩
  have hLY : L ⊆ Y := sdiff_subset
  have hYL : (Y : Set M) = K ∪ L := by
    apply Subset.antisymm
    · intro x hx
      by_cases hxK : x ∈ K
      · exact Or.inl hxK
      · exact Or.inr ⟨hx, fun hi => hxK (interior_subset hi)⟩
    · exact union_subset hKY hLY
  rcases ProjectiveGluing.compact_sphere_region_model T hLcompact hLV hLregular
      (fun q : UnitTwoSphere => c (q, 0))
      (Poincare.isSmoothEmbedding_collar_center c hc hci hzero) hLfront.symm with hball | hprojective
  · obtain ⟨v, hvs, hv, hvi, hvL⟩ := hball
    have hzeroBall : c '' (univ ×ˢ ({0} : Set ℝ)) = v '' Metric.sphere 0 1 := by
      rw [v.image_sphere_eq_frontier hvs hvL]
      exact hzeroImage
    have hpositive (q : UnitTwoSphere) (t : ℝ) (ht : 0 < t) (htδ : t < δ) :
        c (q, t) ∉ v '' Metric.closedBall 0 1 := by
      rw [hvL]
      have hz : (q, t) ∈ c.source := hcs.symm ▸ ⟨mem_univ _, by constructor <;> linarith⟩
      intro hmem
      have h := (hLside _ (c.map_source hz)).mp hmem
      rw [c.left_inv hz] at h
      exact (not_le_of_gt ht) h
    obtain ⟨r, v', hr, hrδ, hvs', _, hv', hvi', hvL', hmatch⟩ :=
      Poincare.exists_ball_neighborhood_matching_boundary_collar v hvs hv hvi c hc hci
        hδ hcs.ge hzeroBall hpositive
    have hv'L : v' '' Metric.closedBall 0 1 = L := hvL'.trans hvL
    have hdis : Disjoint (v' '' Metric.ball 0 1) K := by
      rw [v'.image_ball_eq_interior hvs' hv'L, hLi]
      exact disjoint_left.mpr (fun _ hx hy => hx.2 hy)
    have hcover : (Y : Set M) = K ∪ v' '' Metric.closedBall 0 1 := by rw [hv'L]; exact hYL
    have hmatching (q : UnitTwoSphere) (t : ℝ) (ht : |t| < r) :
        Real.exp t • (q : E3) ∈ b.source ∧ Real.exp t • (q : E3) ∈ v'.source ∧
        S.cover (b (Real.exp t • (q : E3))) = v' (Real.exp t • (q : E3)) := by
      have hz : (q, t) ∈ c.source := hcs.symm ▸ ⟨mem_univ _, abs_lt.mp (ht.trans hrδ)⟩
      exact ⟨hbs.symm ▸ mem_univ _, (hmatch (q, t) ht).1,
        (hcf (q, t) hz).symm.trans (hmatch (q, t) ht).2.symm⟩
    obtain ⟨P, _, _⟩ := ProjectiveGluing.exists_smooth_cover_of_matching_ball S a ha b
      hbs₁ hb hbi hb0 hBB v' hvs' hv' hvi' hr hmatching hdis Y hcover
    exact ⟨.realProjectiveThree, P.nonempty_closedComponentCertificate Y hcompact hcomponent⟩
  · obtain ⟨SL⟩ := hprojective
    obtain ⟨_, _, SK, _⟩ :=
      ProjectiveGluing.exists_punctured_cover_ball_complement S a ha b hbs₁ hb hbi hb0 hBB
    have hdis : Disjoint (interior L) (interior K) := by
      rw [hLi]
      exact disjoint_left.mpr (fun _ hx hy => hx.2 (interior_subset hy))
    have hKside (y : M) (hy : y ∈ c.target) : y ∈ interior K ↔ 0 < (c.symm y).2 := by
      have hyY : y ∈ Y := Or.inl (hct hy).1
      have heq : y ∈ interior K ↔ y ∉ L := by
        change y ∈ interior K ↔ ¬ (y ∈ Y ∧ y ∉ interior K)
        simp only [hyY, true_and, not_not]
      rw [heq, hLside y hy, not_le]
    have hcover : interior L ∪ interior K ∪ c '' (univ ×ˢ ({0} : Set ℝ)) = (Y : Set M) := by
      rw [hzeroImage, hLi, hLf, hKcompact.isClosed.frontier_eq]
      apply Subset.antisymm
      · exact union_subset (union_subset sdiff_subset (interior_subset.trans hKY))
          (sdiff_subset.trans hKY)
      · intro x hx
        by_cases hxK : x ∈ K
        · by_cases hxi : x ∈ interior K
          · exact Or.inl (Or.inr hxi)
          · exact Or.inr ⟨hxK, hxi⟩
        · exact Or.inl (Or.inl ⟨hx, hxK⟩)
    exact ⟨.realProjectiveThreeConnectedSum,
      SmoothProjectiveDoubleModel.nonempty_closedComponentCertificate_of_collar_in_open
        Y hcompact hcomponent SL SK (interior_subset.trans hLY) (interior_subset.trans hKY)
        hdis c hc hci hδ hcs.ge (fun _ hy => Or.inl (hct hy).1) hLiSide hKside hcover⟩

end PoincareConjecture.ClosedModels
