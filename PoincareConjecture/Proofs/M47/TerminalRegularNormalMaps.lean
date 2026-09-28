import PoincareConjecture.Proofs.M47.TerminalSourcePhysicalMaps










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)



theorem terminalSource_regular_normal_maps
    {F : SurgeryFlowData.{u}} {base Q tau : ℝ}
    (U : TopologicalSpace.Opens (F.slice base).carrier) (p0 : U)
    (e : SurgeryFlowCylinder F (F.slice base) base Q (Icc (-tau) 0) U)
    (h0 : (0 : ℝ) ∈ Icc (-tau) 0) (g : RiemannianMetric 3 U)
    (center : (F.slice base).carrier) (hp0 : p0.val = center) :
    let j := terminalSourceNormal_terminalMap U p0 e h0
    (∀ z : U, j z = z.val) →
    (∀ z (v w : TangentSpace (𝓡 3) z), g.inner z v w = Q * (F.metric base).inner (j z)
      (mfderiv (𝓡 3) (𝓡 3) j z v) (mfderiv (𝓡 3) (𝓡 3) j z w)) →
    ∀ {a Rbig R rho : ℝ} {m : ℕ}
      (cover : TerminalSourceIndexedChartCover g p0 a R rho m),
    0 < a → a ≤ Rbig → R ≤ Rbig → ∀ hrho : 0 < rho, 2 * rho < R →
    (F.metric base).ball (j p0) (6 * Rbig / Real.sqrt Q) ⊆ j.target →
    (∀ i, ∀ z ∈ Metric.closedBall (0 : E) (2 * rho), ∀ v,
      (1 / 4 : ℝ) * ‖v‖ ^ 2 ≤ g.pullbackCoefficients (cover.chart i).chart z v v ∧
        g.pullbackCoefficients (cover.chart i).chart z v v ≤ (9 / 4 : ℝ) * ‖v‖ ^ 2) →
    let h : RiemannianMetric 3 (F.slice base).carrier :=
      M13.scaleSmoothMetric (F.metric base) Q e.scale_pos
    let D := terminalSourceCountableDomain rho
    let C := Poincare.connectedComponentOpens E center
    let p : C := ⟨center, mem_connectedComponent⟩
    letI := terminalSourceComponentMetricSpace h center
    ∃ maps : Fin (m + 1) → D → C,
      (∀ i z, (maps i z).val = j ((cover.chart i).chart z.val)) ∧
      maps 0 (terminalSourceCountableZero hrho) = p ∧
      (∀ i, Topology.IsOpenEmbedding (maps i) ∧
        IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (maps i)) ∧
      (∀ i z z', (1 / 2 : ℝ) * dist z z' ≤ dist (maps i z) (maps i z') ∧
        dist (maps i z) (maps i z') ≤ (3 / 2 : ℝ) * dist z z') ∧
      (∀ i z, dist p (maps i z) ≤ a + R) ∧
      (∀ i (z : D) (v w : TangentSpace (𝓡 3) z),
        (h.connectedComponentMetric center).inner (maps i z)
          (mfderiv (𝓡 3) (𝓡 3) (maps i) z v) (mfderiv (𝓡 3) (𝓡 3) (maps i) z w) =
        g.inner ((cover.chart i).chart z.val)
          (mfderiv (𝓡 3) (𝓡 3) (fun y : D => (cover.chart i).chart y.val) z v)
          (mfderiv (𝓡 3) (𝓡 3) (fun y : D => (cover.chart i).chart y.val) z w)) ∧
      ∃ core : Set D, IsCompact core ∧
        (∀ z : D, z ∈ core ↔ z.val ∈ Metric.closedBall (0 : E) (rho / 4)) ∧
        Metric.ball p a ⊆ ⋃ i, maps i '' core := by
  let j := terminalSourceNormal_terminalMap U p0 e h0
  dsimp only
  intro hmap hmetric a Rbig R rho m cover ha haR hRR hrho hrhoR hcover hquadratic
  let h : RiemannianMetric 3 (F.slice base).carrier :=
    M13.scaleSmoothMetric (F.metric base) Q e.scale_pos
  have hsource := (terminalSourceNormal_terminal_map U p0 e h0).1
  have hm (z : U) (v w : TangentSpace (𝓡 3) z) :
      g.inner z v w = h.inner (j z)
        (mfderiv (𝓡 3) (𝓡 3) j z v) (mfderiv (𝓡 3) (𝓡 3) j z w) := hmetric z v w
  have hc : h.ball (j p0) (6 * Rbig) ⊆ j.target := by
    rw [terminalSourceNormal_scaled_ball]
    exact hcover
  have hresult := terminalSource_exists_physical_stage_maps g h j hsource hm p0 cover
    ha haR hRR hrho hrhoR hc hquadratic
  have hcenter : j.toPartialEquiv p0 = center := (hmap p0).trans hp0
  cases hcenter
  exact hresult

end PoincareConjecture.M47
