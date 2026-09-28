import PoincareConjecture.Proofs.M25.Topology3D.Space3.HorizontalTubeChart
import PoincareConjecture.Proofs.M25.Topology3D.Space3.BallNeighborhoodNesting

set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

theorem exists_innermost_family_tube
    (S : Set E3) (u : UnitTwoSphere) (t d : ℝ) (_hd : 0 < d)
    (m : ℕ) (hm : 0 < m) (B : Fin m → BallNeighborhoodChart E2 E2)
    (hdisjoint : Pairwise (fun i j : Fin m =>
      Disjoint (B i).boundary (B j).boundary))
    (Phi : ℝ → Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞)
    (hPhi : ContDiff ℝ ∞ (fun p : ℝ × E2 => Phi p.1 p.2))
    (hinverse : ContDiff ℝ ∞ (fun p : ℝ × E2 => (Phi p.1).symm p.2))
    (hlevel : ∀ z ∈ Ioo (t - d) (t + d), ∀ p : E2,
      (heightPlaneCoordinates u).symm (Phi z p, z) ∈ S ↔
        p ∈ (⋃ i : Fin m, (B i).boundary)) :
    ∃ i : Fin m,
      (B i).closedRegion ∩ (⋃ j : Fin m, (B j).boundary) = (B i).boundary ∧
      let T := horizontalTubeChart Phi hPhi hinverse u (B i)
      closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ T.source ∧
      ContDiffOn ℝ ∞ T T.source ∧ ContDiffOn ℝ ∞ T.symm T.target ∧
      (∀ p : E2 × ℝ, ⟪(u : E3), T p⟫_ℝ = p.2) ∧
      (∀ x ∈ closedBall (0 : E2) 1, ∀ z ∈ Ioo (t - d) (t + d),
        T (x, z) ∈ S ↔ x ∈ sphere (0 : E2) 1) := by
  let : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have hdim : 1 < Module.rank ℝ E2 :=
    Module.one_lt_rank_of_one_lt_finrank (by simp [E2])
  obtain ⟨i, _hinside, hinner⟩ := BallNeighborhoodChart.exists_innermost B
    (fun j => (B j).boundary_connected hdim) (fun _ _ hij => hdisjoint hij)
  refine ⟨i, hinner, horizontalTubeChart_closedBall_subset_source Phi hPhi hinverse u (B i),
    horizontalTubeChart_contDiffOn Phi hPhi hinverse u (B i),
    horizontalTubeChart_symm_contDiffOn Phi hPhi hinverse u (B i),
    horizontalTubeChart_height Phi hPhi hinverse u (B i), ?_⟩
  intro x hx z hz
  rw [horizontalTubeChart_apply, hlevel z hz]
  have hxregion : (B i).chart x ∈ (B i).closedRegion := ⟨x, hx, rfl⟩
  constructor
  · intro hy
    have hboundary : (B i).chart x ∈ (B i).boundary :=
      hinner ▸ (show (B i).chart x ∈ (B i).closedRegion ∩
        (⋃ j : Fin m, (B j).boundary) from ⟨hxregion, hy⟩)
    obtain ⟨y, hy, heq⟩ := hboundary
    have hxy : y = x := (B i).chart.injOn
      ((B i).closedBall_subset_source (sphere_subset_closedBall hy))
      ((B i).closedBall_subset_source hx) heq
    exact hxy ▸ hy
  · intro hx
    exact mem_iUnion.mpr ⟨i, ⟨x, hx, rfl⟩⟩

end PoincareConjecture.M25.Topology3D
