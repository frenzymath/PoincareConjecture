import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Core.OrientedCollar
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Core.RadialNeighborhood
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.EssentialSphere.SupportedCollar

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.CapCertificate

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace E3 M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M} (C : CapCertificate g)

theorem exists_euclidean_core_collar_filling (hkind : C.model_kind = .euclidean) :
    ∃ b : OpenPartialHomeomorph E3 M,
      Metric.closedBall 0 1 ⊆ b.source ∧
      C.closed_core ⊆ b.target ∧ b.target ⊆ C.carrier ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ b b.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ b.symm b.target ∧
      b '' Metric.closedBall 0 1 = C.closed_core ∧
      b '' Metric.ball 0 1 = C.core ∧
      b '' Metric.sphere 0 1 = C.boundary_sphere ∧
      ∃ r : ℝ, 0 < r ∧ r < C.epsilon⁻¹ ∧
        ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
          (∀ p : RoundCylinderSpace, |p.2| < r →
            Real.exp p.2 • (p.1 : E3) ∈ b.source ∧
            b (Real.exp p.2 • (p.1 : E3)) =
              C.boundary_neck.coordinate_map (p.1, σ * p.2)) ∧
          Metric.ball 0 (Real.exp r) ⊆ b.source ∧
          b '' Metric.ball 0 (Real.exp r) = C.closed_core ∪
            (fun p : RoundCylinderSpace => C.boundary_neck.coordinate_map (p.1, σ * p.2)) ''
              (univ ×ˢ Ioo 0 r) := by
  obtain ⟨b, hs, ht, hcap, hb, hbi, hclosed, _, hsphere, hboundary⟩ :=
    C.exists_euclidean_core_boundary_filling hkind
  obtain ⟨δ, hδ, hδC, σ, hσ, e, hes, het, he, hei, hezero, hepos, _, heq⟩ :=
    C.exists_outward_ball_coordinate_collar b hs hb hbi hclosed hsphere hboundary
  obtain ⟨r, F, hr, hrδ, _, hFball, hF, _⟩ :=
    Poincare.exists_ambient_extension_of_outward_sphere_collar e he hei hδ hes hezero
      (fun q t ht htδ => hepos q t ⟨ht, htδ⟩) δ hδ
  let c := F.toHomeomorph.toOpenPartialHomeomorph.trans b
  have hcs : Metric.closedBall (0 : E3) 1 ⊆ c.source := by
    intro x hx
    exact ⟨mem_univ _, hs (hFball ▸ mem_image_of_mem F hx)⟩
  have hct : c.target = b.target := by simp [c]
  have hcimage : c '' Metric.closedBall 0 1 = C.closed_core := by
    change (b ∘ F) '' Metric.closedBall 0 1 = C.closed_core
    calc
      (b ∘ F) '' Metric.closedBall 0 1 = b '' (F '' Metric.closedBall 0 1) :=
        (image_image (⇑b) (⇑F) (Metric.closedBall 0 1)).symm
      _ = C.closed_core := by rw [hFball, hclosed]
  have hcollar (p : RoundCylinderSpace) (hp : |p.2| < r) :
      Real.exp p.2 • (p.1 : E3) ∈ c.source ∧
      c (Real.exp p.2 • (p.1 : E3)) =
        C.boundary_neck.coordinate_map (p.1, σ * p.2) := by
    have hpe : p ∈ e.source := hes ⟨mem_univ _, abs_lt.mp (hp.trans hrδ)⟩
    constructor
    · refine ⟨mem_univ _, ?_⟩
      change F (Real.exp p.2 • (p.1 : E3)) ∈ b.source
      rw [hF p hp]
      exact het (e.map_source hpe)
    · change b (F (Real.exp p.2 • (p.1 : E3))) = _
      rw [hF p hp, heq p hpe]
  refine ⟨c, hcs, hct.symm ▸ ht, hct.symm ▸ hcap, ?_, ?_, hcimage, ?_, ?_,
    r, hr, hrδ.trans hδC, σ, hσ, hcollar,
    C.ball_image_eq_closed_core_union_collar c hcs hcimage hr σ hcollar⟩
  · exact hb.comp F.contMDiff.contMDiffOn inter_subset_right
  · exact F.symm.contMDiff.comp_contMDiffOn (hbi.mono inter_subset_left)
  · rw [c.image_ball_eq_interior hcs hcimage, ← C.core_eq_interior_closed_core]
  · rw [c.image_sphere_eq_frontier hcs hcimage,
      C.closed_core_compact.isClosed.frontier_eq, ← C.core_eq_interior_closed_core,
      ← C.boundary_eq_closed_core_diff_core]

end PoincareConjecture.CapCertificate
