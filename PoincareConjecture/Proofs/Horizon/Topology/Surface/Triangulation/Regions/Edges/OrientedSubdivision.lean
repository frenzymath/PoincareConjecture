


import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Edges.OrientedGraphs








set_option autoImplicit false
open Set
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.Topology.Surface
namespace FiniteChartRegionDecomposition

universe u
variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
variable (D : FiniteChartRegionDecomposition (M := M))



theorem exists_oriented_edge_graph_subdivision (e : D.EdgeIndex) (q : D.regions)
    (hq : q = D.regionLeft e ∨ q = D.regionRight e)
    (C : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M)
    (hC : ContMDiffOn (𝓡 2) (𝓡 2) ∞ C C.source)
    (hCinv : ContMDiffOn (𝓡 2) (𝓡 2) ∞ C.symm C.target)
    {a b : ℝ} (hab : a < b) (hparam : Icc a b ⊆ Ioo (0 : ℝ) 1)
    (hchart : (D.edge e.1 e.2).map '' Icc a b ⊆ C.target) :
    ∃ (n : ℕ) (c : Fin (n + 1) → ℝ),
      0 < n ∧ StrictMono c ∧ c 0 = a ∧ c (Fin.last n) = b ∧
      (∀ i, c i ∈ Ioo (0 : ℝ) 1) ∧
      ∀ i : Fin n, ∃ (A : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] (ℝ × ℝ))
        (G : OpenPartialHomeomorph ℝ ℝ) (h : ℝ → ℝ) (l r α β δ : ℝ),
        l < c i.castSucc ∧ c i.succ < r ∧ G.source = Ioo l r ∧
        G.source ⊆ (D.edge e.1 e.2).map ⁻¹' C.target ∧
        StrictMonoOn G G.source ∧ ContDiffOn ℝ ∞ G G.source ∧
        ContDiffOn ℝ ∞ G.symm G.target ∧ ContDiffOn ℝ ∞ h G.target ∧
        (∀ x ∈ G.target, A.symm (x, h x) ∈ C.source) ∧
        (∀ t ∈ G.source, A (C.symm ((D.edge e.1 e.2).map t)) = (G t, h (G t))) ∧
        (∀ t ∈ G.source, (D.edge e.1 e.2).map t = C (A.symm (G t, h (G t)))) ∧
        (∀ t ∈ Icc (c i.castSucc) (c i.succ),
          0 < (A (deriv (C.symm ∘ (D.edge e.1 e.2).map) t)).1) ∧
        G '' Icc (c i.castSucc) (c i.succ) = Icc (G (c i.castSucc)) (G (c i.succ)) ∧
        Icc (G (c i.castSucc)) (G (c i.succ)) ⊆ G.target ∧
        α < G (c i.castSucc) ∧ G (c i.succ) < β ∧ 0 < δ ∧
        ∀ x ∈ Ioo α β, ∀ z : ℝ, |z| < δ →
          A.symm (x, h x + z) ∈ C.source ∧
          (C (A.symm (x, h x + z)) ∈ chartDiskBoundaryUnion D.centers D.radius ↔ z = 0) ∧
          (C (A.symm (x, h x + z)) ∈ connectedComponentIn
            (chartDiskBoundaryUnion D.centers D.radius)ᶜ q ↔ 0 < z) ∧
          (0 ≤ z → C (A.symm (x, h x + z)) ∈ closure (connectedComponentIn
            (chartDiskBoundaryUnion D.centers D.radius)ᶜ q)) := by
  obtain ⟨n, c, hn, hc, hfirst, hlast, hcuts, hpieces⟩ :=
    D.exists_edge_graph_subdivision e C hC hCinv hab hparam hchart
  refine ⟨n, c, hn, hc, hfirst, hlast, hcuts, ?_⟩
  intro i
  obtain ⟨v, L, G, f, l, r, _, hL, hl, hr, hGs, hGC, _, hmono, hG, hGinv,
    hf, _, hgraph, himage, hIG, hpositive, _, hsource, _⟩ := hpieces i
  have hsource' (x : ℝ) (hx : x ∈ G.target) : L.symm (x, f x) ∈ C.source := by
    have hs := (hsource (mem_image_of_mem (fun t => collarParameterEquiv.symm (t, f t)) hx)).2
    change (collarParameterEquiv.trans L.symm) (collarParameterEquiv.symm (x, f x)) ∈ C.source at hs
    simpa only [ContinuousLinearEquiv.trans_apply, collarParameterEquiv.apply_symm_apply] using hs
  have hmap (t : ℝ) (ht : t ∈ G.source) :
      (D.edge e.1 e.2).map t = C (L.symm (G t, f (G t))) := by
    rw [← hgraph t ht, L.symm_apply_apply, C.right_inv (hGC ht)]
  obtain ⟨A, h, α, β, δ, hfst, hh, hAsource, hAmap, hα, hβ, hδ, htube⟩ :=
    D.exists_graph_frame_into_incident_region e q hq C L G f
      (hc Fin.castSucc_lt_succ).le hl hr (hcuts i.castSucc).1 (hcuts i.succ).2
      hGs hmono hf hsource' hmap
  refine ⟨A, G, h, l, r, α, β, δ, hl, hr, hGs, hGC, hmono, hG, hGinv, hh,
    hAsource, ?_, hAmap, ?_, himage, hIG, hα, hβ, hδ, htube⟩
  · intro t ht
    rw [hAmap t ht, C.left_inv (hAsource _ (G.map_source ht)), A.apply_symm_apply]
  · intro t ht
    rw [hfst, hL]
    exact hpositive t ht

end FiniteChartRegionDecomposition
end PoincareConjecture.Topology.Surface
