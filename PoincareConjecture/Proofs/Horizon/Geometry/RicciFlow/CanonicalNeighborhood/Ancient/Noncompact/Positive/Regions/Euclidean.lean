import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.SmoothDomain.EmbeddingSupplement
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Positive.Regions.Smooth
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.SmoothEmbedding.LocalDiffeomorph
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cylinder.Sphere

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.NoncompactKappa.Positive.SoulNeckRegion

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 3 M}
  {S : RiemannianMetric.PointSoulData (K.flow.metric 0)} {epsilon D R : ℝ}
  (G : SoulNeckRegion K S epsilon D R)

theorem closure_euclidean_inside :
    closure (S.euclidean.symm '' G.inside) =
      S.euclidean.symm '' closure G.inside :=
  (S.euclidean.symm.toHomeomorph.image_closure G.inside).symm

theorem interior_euclidean_closed_side :
    interior (S.euclidean.symm '' closure G.inside) =
      S.euclidean.symm '' G.inside := by
  exact (S.euclidean.symm.toHomeomorph.image_interior (closure G.inside)).symm.trans
    (congrArg (fun A => S.euclidean.symm '' A) G.interior_closure_inside)

theorem frontier_euclidean_inside :
    frontier (S.euclidean.symm '' G.inside) =
      S.euclidean.symm '' G.neck.terminal_neck.central_sphere := by
  exact (S.euclidean.symm.toHomeomorph.image_frontier G.inside).symm.trans
    (congrArg (fun A => S.euclidean.symm '' A) G.inside_frontier)

theorem nonempty_smoothDomain_euclidean_inside :
    Nonempty (Poincare.Manifold.SmoothDomain 3 (S.euclidean.symm '' G.inside)) := by
  let e := S.euclidean.toHomeomorph.toOpenPartialHomeomorph
  have hcharts : ∀ a : S.euclidean.symm '' closure G.inside,
      ∃ f : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 3))
          (EuclideanSpace ℝ (Fin 3)),
        a.val ∈ f.source ∧
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ f f.source ∧
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ f.symm f.target ∧
        f.IsImage (S.euclidean.symm '' closure G.inside) {y | 0 ≤ y 0} := by
    intro a
    have ha : S.euclidean a.val ∈ closure G.inside := by
      obtain ⟨x, hx, heq⟩ := a.property
      rw [← heq, S.euclidean.apply_symm_apply]
      exact hx
    obtain ⟨f, haf, hf, hfi, himg⟩ := G.exists_closed_side_halfspace_chart ⟨_, ha⟩
    refine ⟨e.trans f, ⟨mem_univ _, haf⟩, ?_, ?_, ?_⟩
    · exact hf.comp S.euclidean.contMDiff.contMDiffOn (fun x hx => hx.2)
    · exact S.euclidean.symm.contMDiff.comp_contMDiffOn
        (hfi.mono (fun x hx => hx.1))
    · intro x hx
      change 0 ≤ f (S.euclidean x) 0 ↔ x ∈ S.euclidean.symm '' closure G.inside
      refine (himg hx.2).trans ?_
      constructor
      · intro h
        exact ⟨S.euclidean x, h, S.euclidean.symm_apply_apply x⟩
      · rintro ⟨y, hy, heq⟩
        change S.euclidean x ∈ closure G.inside
        rw [← heq, S.euclidean.apply_symm_apply]
        exact hy
  choose amb hamb using hcharts
  obtain ⟨CS, _, _, _, hman, hemb⟩ :=
    Poincare.Manifold.exists_smooth_embedding_of_halfspace_charts
      (n := 2) (by simp) (S.euclidean.symm '' closure G.inside) amb hamb
  let := CS
  let := hman
  have hc := G.compact_side.image S.euclidean.symm.continuous
  have hconn := G.inside_connected.closure.image S.euclidean.symm
    S.euclidean.symm.continuous.continuousOn
  simpa only [G.interior_euclidean_closed_side] using
    Poincare.Manifold.nonempty_smoothDomain_interior (n := 2) hc hconn hemb

theorem euclidean_boundary_isSmoothEmbedding :
    Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞
      (fun p : UnitTwoSphere =>
        S.euclidean.symm (G.neck.terminal_neck.coordinate_map (p, 0))) := by
  exact G.neck.terminal_neck.centralSphere_isSmoothEmbedding.comp_localDiffeomorph
    S.euclidean.symm.isLocalDiffeomorph
    (S.euclidean.symm.injective.comp
      G.neck.terminal_neck.centralSphere_isSmoothEmbedding.isEmbedding.injective)

theorem range_euclidean_boundary :
    range (fun p : UnitTwoSphere =>
      S.euclidean.symm (G.neck.terminal_neck.coordinate_map (p, 0))) =
      frontier (S.euclidean.symm '' G.inside) := by
  rw [G.frontier_euclidean_inside, ← G.neck.terminal_neck.centralSphere_range,
    ← range_comp]
  rfl

end PoincareConjecture.NoncompactKappa.Positive.SoulNeckRegion
