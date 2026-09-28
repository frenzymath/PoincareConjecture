import PoincareConjecture.Proofs.M25.Topology3D.Space3.HorizontalTubeChart
import PoincareConjecture.Proofs.M25.Topology3D.Space3.RegularInnermostDisc

set_option autoImplicit false

open Set Metric Function
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

theorem exists_regular_collar_innermost_tube (hP : PlanarSchoenfliesService)
    (ψ : UnitTwoSphere × ℝ → E3) (hψ : IsCollarEmbedding ψ)
    (u : UnitTwoSphere) (t : ℝ)
    (hreg : ∀ q : UnitTwoSphere, ⟪(u : E3), ψ (q, 0)⟫_ℝ = t →
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun p : UnitTwoSphere => ⟪(u : E3), ψ (p, 0)⟫_ℝ) q ≠ 0)
    (x₀ : collarHeightLevel ψ (u : E3) t) :
    ∃ x : collarHeightLevel ψ (u : E3) t, ∃ d > (0 : ℝ),
      ∃ e : OpenPartialHomeomorph (E2 × ℝ) E3,
        closedBall 0 1 ×ˢ (univ : Set ℝ) ⊆ e.source ∧
        ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
        (∀ p : E2 × ℝ, ⟪(u : E3), e p⟫_ℝ = p.2) ∧
        (fun p : E2 => e (p, t)) '' sphere 0 1 =
          ((↑) : collarHeightLevel ψ (u : E3) t → E3) '' connectedComponent x ∧
        ∀ p ∈ closedBall (0 : E2) 1, ∀ z ∈ Ioo (t - d) (t + d),
          e (p, z) ∈ range (fun q : UnitTwoSphere => ψ (q, 0)) ↔ p ∈ sphere 0 1 := by
  obtain ⟨x, B, hB, _, hBclosed⟩ :=
    exists_regular_collar_innermost_disc hP ψ hψ u t hreg x₀
  have hregI : ∀ q : UnitTwoSphere, ⟪(u : E3), ψ (q, 0)⟫_ℝ ∈ Icc t t →
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun p : UnitTwoSphere => ⟪(u : E3), ψ (p, 0)⟫_ℝ) q ≠ 0 := by
    intro q hq
    exact hreg q (le_antisymm hq.2 hq.1)
  obtain ⟨d, hd, _, Φ, hΦ, hi, hzero, _, hmem⟩ :=
    exists_regular_collar_horizontal_transport ψ hψ u t t le_rfl hregI
  have hm : (t + t) / 2 = t := by ring
  simp only [hm] at hzero hmem
  let e := horizontalTubeChart Φ hΦ hi u B
  let lift : E2 → E3 := fun p => (heightPlaneCoordinates u).symm (p, t)
  have hlift : Injective lift := by
    intro p q hpq
    exact congrArg Prod.fst ((heightPlaneCoordinates u).symm.injective hpq)
  have hbase (p : E2) : e (p, t) = lift (B.chart p) := by
    change (heightPlaneCoordinates u).symm (Φ t (B.chart p), t) = _
    rw [hzero]
  have hboundary : (fun p : E2 => e (p, t)) '' sphere 0 1 =
      lift '' B.boundary := by
    change _ = lift '' (B.chart '' sphere 0 1)
    simp only [image_image, hbase]
  have hinitial (p : E2) (hp : p ∈ closedBall 0 1) :
      lift (B.chart p) ∈ range (fun q : UnitTwoSphere => ψ (q, 0)) ↔
        p ∈ sphere 0 1 := by
    constructor
    · intro hps
      have hb : lift (B.chart p) ∈ lift '' B.boundary := by
        rw [← hBclosed]
        exact ⟨⟨B.chart p, ⟨p, hp, rfl⟩, rfl⟩, hps⟩
      have hpB : B.chart p ∈ B.boundary := hlift.mem_set_image.mp hb
      obtain ⟨q, hq, hqp⟩ := hpB
      have heq := B.chart.injOn (B.closedBall_subset_source (sphere_subset_closedBall hq))
        (B.closedBall_subset_source hp) hqp
      simpa only [heq] using hq
    · intro hpbd
      have hb : lift (B.chart p) ∈ lift '' B.boundary :=
        ⟨B.chart p, ⟨p, hpbd, rfl⟩, rfl⟩
      rw [← hBclosed] at hb
      exact hb.2
  refine ⟨x, d, hd, e, horizontalTubeChart_closedBall_subset_source Φ hΦ hi u B,
    horizontalTubeChart_contDiffOn Φ hΦ hi u B,
    horizontalTubeChart_symm_contDiffOn Φ hΦ hi u B,
    horizontalTubeChart_height Φ hΦ hi u B, hboundary.trans hB, ?_⟩
  intro p hp z hz
  change (heightPlaneCoordinates u).symm (Φ z (B.chart p), z) ∈
    range (fun q : UnitTwoSphere => ψ (q, 0)) ↔ _
  exact (hmem z hz (B.chart p)).trans (hinitial p hp)

end PoincareConjecture.M25.Topology3D
