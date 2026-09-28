import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.Extension.Interval
import PoincareConjecture.Proofs.Horizon.Topology.Plane.Curves.Graphs.Subdivision
import PoincareConjecture.Proofs.Horizon.Topology.Plane.Curves.Graphs.Coordinates
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Edges.Coordinates

set_option autoImplicit false
open Set
open scoped ContDiff Topology Manifold
open Poincare.Topology.Plane.Curves

namespace PoincareConjecture.Topology.Surface

universe u
variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]

noncomputable def linearGraphCoordinates
    (C : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M)
    (L : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] (ℝ × ℝ)) :
    OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M :=
  (collarParameterEquiv.trans L.symm).toHomeomorph.toOpenPartialHomeomorph.trans C

omit [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M] in
theorem linearGraphCoordinates_apply
    (C : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M)
    (L : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] (ℝ × ℝ)) (z : EuclideanSpace ℝ (Fin 2)) :
    linearGraphCoordinates C L z = C (L.symm (collarParameterEquiv z)) := rfl

omit [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M] in

theorem linearGraphCoordinates_affineChartSegment
    (C : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M)
    (L : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] (ℝ × ℝ))
    (z w : EuclideanSpace ℝ (Fin 2)) (t : ℝ) :
    linearGraphCoordinates C L (affineChartSegment z w t) =
      C (affineChartSegment (L.symm (collarParameterEquiv z))
        (L.symm (collarParameterEquiv w)) t) := by
  simp only [linearGraphCoordinates_apply, affineChartSegment, map_add, map_smul, map_sub]

omit [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M] in
theorem linearGraphCoordinates_target
    (C : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M)
    (L : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] (ℝ × ℝ)) :
    (linearGraphCoordinates C L).target = C.target := by
  ext z
  simp [linearGraphCoordinates]

omit [T2Space M] [IsManifold (𝓡 2) ∞ M] in
theorem linearGraphCoordinates_contMDiff
    (C : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M)
    (L : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] (ℝ × ℝ))
    (hC : ContMDiffOn (𝓡 2) (𝓡 2) ∞ C C.source)
    (hCinv : ContMDiffOn (𝓡 2) (𝓡 2) ∞ C.symm C.target) :
    ContMDiffOn (𝓡 2) (𝓡 2) ∞ (linearGraphCoordinates C L)
      (linearGraphCoordinates C L).source ∧
    ContMDiffOn (𝓡 2) (𝓡 2) ∞ (linearGraphCoordinates C L).symm
      (linearGraphCoordinates C L).target := by
  let A := collarParameterEquiv.trans L.symm
  constructor
  · exact hC.comp A.contDiff.contMDiff.contMDiffOn (fun _ hz => hz.2)
  · exact A.symm.contDiff.contMDiff.comp_contMDiffOn (hCinv.mono (fun _ hz => hz.1))

namespace FiniteChartRegionDecomposition

variable (D : FiniteChartRegionDecomposition (M := M))

omit [T2Space M] in

theorem exists_edge_coordinate_extension (e : D.EdgeIndex)
    (C : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M)
    (hCinv : ContMDiffOn (𝓡 2) (𝓡 2) ∞ C.symm C.target)
    {a b : ℝ} (hab : a ≤ b)
    (hchart : (D.edge e.1 e.2).map '' Icc a b ⊆ C.target) :
    ∃ (g : ℝ → EuclideanSpace ℝ (Fin 2)) (l r : ℝ),
      ContDiff ℝ ∞ g ∧ l < a ∧ b < r ∧
      Ioo l r ⊆ (D.edge e.1 e.2).map ⁻¹' C.target ∧
      EqOn g (C.symm ∘ (D.edge e.1 e.2).map) (Ioo l r) := by
  exact Poincare.Analysis.exists_global_contDiff_near_interval
    (C.open_target.preimage (D.edge_contMDiff e).continuous)
    (D.edge_coordinate_contDiffOn e C hCinv) hab
    (fun t ht => hchart ⟨t, ht, rfl⟩)

omit [T2Space M] in

theorem exists_edge_graph_subdivision (e : D.EdgeIndex)
    (C : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M)
    (hC : ContMDiffOn (𝓡 2) (𝓡 2) ∞ C C.source)
    (hCinv : ContMDiffOn (𝓡 2) (𝓡 2) ∞ C.symm C.target)
    {a b : ℝ} (hab : a < b) (hparam : Icc a b ⊆ Ioo (0 : ℝ) 1)
    (hchart : (D.edge e.1 e.2).map '' Icc a b ⊆ C.target) :
    ∃ (n : ℕ) (c : Fin (n + 1) → ℝ),
      0 < n ∧ StrictMono c ∧ c 0 = a ∧ c (Fin.last n) = b ∧
      (∀ i, c i ∈ Ioo (0 : ℝ) 1) ∧
      ∀ i : Fin n, ∃ (v : EuclideanSpace ℝ (Fin 2))
        (L : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] (ℝ × ℝ))
        (G : OpenPartialHomeomorph ℝ ℝ) (h : ℝ → ℝ) (l r : ℝ),
        v ≠ 0 ∧ (∀ z, L z = (inner ℝ v z, inner ℝ (quarterTurn v) z)) ∧
        l < c i.castSucc ∧ c i.succ < r ∧ G.source = Ioo l r ∧
        G.source ⊆ (D.edge e.1 e.2).map ⁻¹' C.target ∧
        (∀ t ∈ G.source, G t = inner ℝ v (C.symm ((D.edge e.1 e.2).map t))) ∧
        StrictMonoOn G G.source ∧
        ContDiffOn ℝ ∞ G G.source ∧ ContDiffOn ℝ ∞ G.symm G.target ∧
        ContDiffOn ℝ ∞ h G.target ∧
        (∀ t ∈ G.target,
          h t = inner ℝ (quarterTurn v) (C.symm ((D.edge e.1 e.2).map (G.symm t)))) ∧
        (∀ t ∈ G.source, L (C.symm ((D.edge e.1 e.2).map t)) = (G t, h (G t))) ∧
        G '' Icc (c i.castSucc) (c i.succ) = Icc (G (c i.castSucc)) (G (c i.succ)) ∧
        Icc (G (c i.castSucc)) (G (c i.succ)) ⊆ G.target ∧
        (∀ t ∈ Icc (c i.castSucc) (c i.succ),
          0 < inner ℝ v (deriv (C.symm ∘ (D.edge e.1 e.2).map) t)) ∧
        (fun t => L (C.symm ((D.edge e.1 e.2).map t))) ''
          Icc (c i.castSucc) (c i.succ) =
            (fun t => (t, h t)) '' Icc (G (c i.castSucc)) (G (c i.succ)) ∧
        (fun t => collarParameterEquiv.symm (t, h t)) ''
          G.target ⊆ (linearGraphCoordinates C L).source ∧
        (D.edge e.1 e.2).map '' Icc (c i.castSucc) (c i.succ) =
          (fun t => linearGraphCoordinates C L (collarParameterEquiv.symm (t, h t))) ''
            Icc (G (c i.castSucc)) (G (c i.succ)) := by
  obtain ⟨g, l₀, r₀, hg, hl₀, hr₀, hdomain, heq⟩ :=
    D.exists_edge_coordinate_extension e C hCinv hab.le hchart
  have hI : Icc a b ⊆ Ioo l₀ r₀ :=
    fun t ht => ⟨hl₀.trans_le ht.1, ht.2.trans_lt hr₀⟩
  have hderiv := heq.deriv isOpen_Ioo
  have hregular (t : ℝ) (ht : t ∈ Icc a b) : deriv g t ≠ 0 := by
    rw [hderiv (hI ht)]
    exact D.edge_coordinate_deriv_ne_zero e C hC hCinv (hdomain (hI ht))
  obtain ⟨n, c, v, hn, hmono, hzero, hlast, hv⟩ :=
    exists_finite_strictMono_projection_subdivision hg hab hregular
  have hcbounds (i : Fin (n + 1)) : c i ∈ Icc a b := by
    rw [← hzero, ← hlast]
    exact ⟨hmono.monotone (Fin.zero_le i), hmono.monotone (Fin.le_last i)⟩
  refine ⟨n, c, hn, hmono, hzero, hlast, fun i => hparam (hcbounds i), ?_⟩
  intro i
  have hpiece : Icc (c i.castSucc) (c i.succ) ⊆ Icc a b :=
    Icc_subset_Icc (hcbounds i.castSucc).1 (hcbounds i.succ).2
  have hstep : c i.castSucc < c i.succ := hmono Fin.castSucc_lt_succ
  obtain ⟨l₁, r₁, G₀, L, h, hl₁, hr₁, hsource, hG, hL, hGmono,
    hGsmooth, hGinvsmooth, hhformula, hhsmooth, hgraph, hGimage, _, _⟩ :=
      exists_graph_coordinates_of_positive_projection hg hstep.le (hv i).2.2.1
  let G := G₀.restrOpen (Ioo l₀ r₀) isOpen_Ioo
  have hGsource : G.source = Ioo (max l₁ l₀) (min r₁ r₀) := by
    change G₀.source ∩ Ioo l₀ r₀ = _
    rw [hsource, Ioo_inter_Ioo]
  have hl : max l₁ l₀ < c i.castSucc :=
    max_lt hl₁ (hl₀.trans_le (hcbounds i.castSucc).1)
  have hr : c i.succ < min r₁ r₀ :=
    lt_min hr₁ ((hcbounds i.succ).2.trans_lt hr₀)
  have hpieceG : Icc (c i.castSucc) (c i.succ) ⊆ G.source := by
    rw [hGsource]
    exact fun t ht => ⟨hl.trans_le ht.1, ht.2.trans_lt hr⟩
  have hGeq (t : ℝ) (ht : t ∈ G.source) :
      G t = inner ℝ (v i) (C.symm ((D.edge e.1 e.2).map t)) := by
    change G₀ t = _
    rw [hG, heq ht.2]
    rfl
  have hactual (t : ℝ) (ht : t ∈ G.source) :
      L (C.symm ((D.edge e.1 e.2).map t)) = (G t, h (G t)) := by
    change L ((C.symm ∘ (D.edge e.1 e.2).map) t) = _
    rw [← heq ht.2]
    exact hgraph t ht.1
  have himage : G '' Icc (c i.castSucc) (c i.succ) =
      Icc (G (c i.castSucc)) (G (c i.succ)) := hGimage
  have htarget : Icc (G (c i.castSucc)) (G (c i.succ)) ⊆ G.target := by
    rw [← himage]
    rintro _ ⟨t, ht, rfl⟩
    exact G.map_source (hpieceG ht)
  have hcoord : (fun t => L (C.symm ((D.edge e.1 e.2).map t))) ''
      Icc (c i.castSucc) (c i.succ) =
        (fun t => (t, h t)) '' Icc (G (c i.castSucc)) (G (c i.succ)) := by
    rw [← himage, image_image]
    exact image_congr (fun t ht => hactual t (hpieceG ht))
  refine ⟨v i, L, G, h, max l₁ l₀, min r₁ r₀, (hv i).1, hL, hl, hr,
    hGsource, (fun t ht => hdomain ht.2), hGeq, ?_, ?_, ?_, ?_, ?_, hactual,
    himage, htarget, ?_, hcoord, ?_, ?_⟩
  · intro s hs t ht hst
    simpa only [G, OpenPartialHomeomorph.coe_restrOpen, hG] using hGmono hs.1 ht.1 hst
  · exact hGsmooth.mono (fun _ ht => ht.1)
  · exact hGinvsmooth.mono (fun _ ht => ht.1)
  · exact hhsmooth.mono (fun _ ht => ht.1)
  · intro t ht
    exact (hhformula t).trans
      (congrArg (fun z => inner ℝ (quarterTurn (v i)) z) (heq (G.map_target ht).2))
  · intro t ht
    rw [← hderiv (hI (hpiece ht))]
    exact (hv i).2.2.1 t ht
  · rintro z ⟨t, ht, rfl⟩
    have hinverse : L (C.symm ((D.edge e.1 e.2).map (G.symm t))) = (t, h t) := by
      simpa only [G.right_inv ht] using hactual (G.symm t) (G.map_target ht)
    refine ⟨mem_univ _, ?_⟩
    change L.symm (collarParameterEquiv (collarParameterEquiv.symm (t, h t))) ∈ C.source
    rw [collarParameterEquiv.apply_symm_apply, ← hinverse, L.symm_apply_apply]
    exact C.map_target (hdomain (G.map_target ht).2)
  · rw [← himage, image_image]
    apply image_congr
    intro t ht
    rw [linearGraphCoordinates_apply, collarParameterEquiv.apply_symm_apply,
      ← hactual t (hpieceG ht), L.symm_apply_apply]
    exact (C.right_inv (hdomain (hpieceG ht).2)).symm

end FiniteChartRegionDecomposition
end PoincareConjecture.Topology.Surface
