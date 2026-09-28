import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.ClosedModels.ProjectiveComplement
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.CollarMatching
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Closing.Projective.Certificate












set_option autoImplicit false

open Set TopologicalSpace Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.ClosedModels

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {M : Type u} [TopologicalSpace M] [ChartedSpace E3 M]
  [IsManifold (𝓡 3) ∞ M] [T2Space M]



theorem nonempty_mixed_pair_certificate
    (U V : Opens M) {p : RealProjectiveThree}
    (S : StandardPuncturedProjectiveCover M p (U : Set M))
    (e : OpenPartialHomeomorph M E3) (hes : e.source = (V : Set M))
    (het : e.target = univ)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    (hcompact : IsCompact ((U : Set M) ∪ V))
    (hcomponent : ∃ x : M, (U : Set M) ∪ V = connectedComponent x) :
    Nonempty (ClosedComponentCertificate .realProjectiveThree ((U : Set M) ∪ V)) := by
  classical
  obtain ⟨a, ha⟩ := Quotient.mk'_surjective p
  obtain ⟨δ, b, c, hδ, hbs, hb0, hb, hbi, hBB, hcs, hct, hc, hci, hcf,
    hLcompact, hLV, hLregular, hLfront, hLside, _⟩ :=
    exists_projective_complementary_collar U V S a ha hcompact
  let K := S.cover '' ProjectiveGluing.antipodalBallComplement b
  let Y : Opens M := ⟨(U : Set M) ∪ V, U.isOpen.union V.isOpen⟩
  let L := (Y : Set M) \ interior K
  have hbs₁ : Metric.closedBall (0 : E3) 1 ⊆ b.source := by rw [hbs]; exact subset_univ _
  obtain ⟨hKcompact, _, hKregular, _, _, _⟩ :=
    ProjectiveGluing.projectiveBallComplement_topology S a ha b hbs₁ hb0 hBB
  have hKY : K ⊆ Y := by
    rintro _ ⟨x, hx, rfl⟩
    exact Or.inl (S.image_eq.subset ⟨x,
      ProjectiveGluing.antipodalBallComplement_avoids_puncture a ha b hb0 hx, rfl⟩)
  obtain ⟨_, hLi, _, _⟩ := Poincare.Topology.complementary_domain
    (show IsClopen (Y : Set M) from ⟨hcompact.isClosed, Y.isOpen⟩)
    hcompact hKcompact hKY hKregular
  obtain ⟨r, v, hr, hrδ, hvs, _, hv, hvi, hvL, hmatch⟩ :=
    Poincare.Manifold.Schoenflies.ball_neighborhood_matching_collar_in_coordinates e het he hei
      hLcompact (hes.symm ▸ hLV) hLregular c hc hci hδ hcs.ge
      (fun y hy => hes.symm ▸ (hct hy).2) hLfront hLside
  change v '' Metric.closedBall 0 1 = L at hvL
  have hdis : Disjoint (v '' Metric.ball 0 1) K := by
    rw [v.image_ball_eq_interior hvs hvL, hLi]
    exact disjoint_left.mpr (fun _ hx hy => hx.2 hy)
  have hcover : (Y : Set M) = K ∪ v '' Metric.closedBall 0 1 := by
    rw [hvL]
    apply Subset.antisymm
    · intro x hx
      by_cases hxK : x ∈ K
      · exact Or.inl hxK
      · exact Or.inr ⟨hx, fun hi => hxK (interior_subset hi)⟩
    · exact union_subset hKY sdiff_subset
  have hmatching (q : UnitTwoSphere) (t : ℝ) (ht : |t| < r) :
      Real.exp t • (q : E3) ∈ b.source ∧ Real.exp t • (q : E3) ∈ v.source ∧
      S.cover (b (Real.exp t • (q : E3))) = v (Real.exp t • (q : E3)) := by
    have hz : (q, t) ∈ c.source := hcs.symm ▸ ⟨mem_univ _, abs_lt.mp (ht.trans hrδ)⟩
    exact ⟨hbs.symm ▸ mem_univ _, (hmatch (q, t) ht).1,
      (hcf (q, t) hz).symm.trans (hmatch (q, t) ht).2.symm⟩
  obtain ⟨P, _, _⟩ := ProjectiveGluing.exists_smooth_cover_of_matching_ball S a ha b
    hbs₁ hb hbi hb0 hBB v hvs hv hvi hr hmatching hdis Y hcover
  exact P.nonempty_closedComponentCertificate Y hcompact hcomponent

end PoincareConjecture.ClosedModels
