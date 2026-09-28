import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.Cuts.BoundaryCycleRanks
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.Cuts.BoundaryCircleChains
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.VertexTriangleIncidence
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Mathlib.SurfaceEulerValuation

set_option autoImplicit false
open Set Metric Geometry
open PreAbstractSimplicialComplex.ModTwoCochains

namespace Geometry.SimplicialComplex

variable {E β : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype β]

open Classical in
theorem surfaceEulerCount_le_two_sub_boundary_circle_count
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hconn : IsConnected K.space)
    (hlinks : ∀ v ∈ K.vertices, IsConnected (K.link v).space)
    (L : β → SimplicialComplex ℝ E) (hLK : ∀ i, L i ≤ K)
    (hdis : Pairwise (fun i j ↦ Disjoint (L i).space (L j).space))
    (gamma : ∀ i, sphere (0 : Fin 2 → ℝ) 1 ≃ₜ (L i).space)
    (hgamma : ∀ i, (gamma i).IsFinitePL)
    (hcofaces : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard =
        if ∃ i, s ∈ (L i).faces then 1 else 2) :
    K.surfaceEulerCount ≤ 2 - (Nat.card β : ℤ) := by
  classical
  let : Fintype K.faces := hK.fintype
  let : Fintype K.vertices := (K.finite_vertices_of_finite_faces hK).fintype
  let KA := K.vertexAbstractComplex.toPreAbstractSimplicialComplex
  let B (i : β) (e : Edge KA) : Prop :=
    e.val.map (Function.Embedding.subtype _) ∈ (L i).faces
  have hL (i : β) : (L i).faces.Finite := hK.subset (hLK i)
  have htri := K.vertex_triangleGraph_connected
    (K.triangleGraph_connected_of_isConnected hK
      (fun s hs ↦ by
        obtain ⟨t, ht, htc, hst⟩ := hpure s hs
        exact ⟨t, ht, hst, htc⟩)
      hconn (fun v hv ↦ by simpa only [K.faceLink_singleton_eq_link] using hlinks v hv))
  have hgraph := K.connected_edgeGraph_of_isConnected hK hconn
  have hcofaces' (e : Edge KA) :
      (triangleCofaces KA e).card = if ∃ i, B i e then 1 else 2 := by
    rw [K.triangleCofaces_card_eq_original]
    exact hcofaces _ e.property.1 (by simpa only [Finset.card_map] using e.property.2)
  have hdis' : ∀ i j, i ≠ j → ∀ e, B i e → ¬ B j e := by
    intro i j hij e hei hej
    obtain ⟨v, hv⟩ := (L i).nonempty_of_mem_faces hei
    exact Set.disjoint_left.mp (hdis hij)
      ((L i).convexHull_subset_space hei (subset_convexHull ℝ _ hv))
      ((L j).convexHull_subset_space hej (subset_convexHull ℝ _ hv))
  have hne (i : β) : ∃ e, B i e :=
    K.exists_boundary_circle_marked_edge (L i) (hLK i) (hL i) (gamma i) (hgamma i)
  have hcycle (i : β) : (vertexCoboundary KA).dualMap (markedEdgeChain KA (B i)) = 0 := by
    obtain ⟨_, _, _, hdegree, _⟩ :=
      PoincareConjecture.M76.Dehn.Annuli.circle_incidence (L i) (hL i) (gamma i) (hgamma i)
    exact K.boundary_circle_markedEdgeChain_cycle (L i) (hLK i) hdegree
  have h0 := (vertexCoboundary KA).finrank_range_add_finrank_ker
  rw [K.vertexAbstractComplex.finrank_ker_vertexCoboundary hgraph,
    Module.finrank_pi] at h0
  have h1 := (vertexCoboundary KA).dualMap.finrank_range_add_finrank_ker
  rw [LinearMap.finrank_range_dualMap_eq_finrank_range, Subspace.dual_finrank_eq,
    Module.finrank_pi] at h1
  have hcount : Nat.card K.vertices + Nat.card (Triangle KA) + Nat.card β ≤
      Nat.card (Edge KA) + 2 := by
    cases isEmpty_or_nonempty β with
    | inr hβ =>
      let : Nonempty β := hβ
      have hbound := boundaryCycle_rank_bound KA B hdis' hne hcycle hcofaces' htri
      simp only [Nat.card_eq_fintype_card] at hbound ⊢
      omega
    | inl hβ =>
      let : IsEmpty β := hβ
      have htwo (e : Edge KA) : (triangleCofaces KA e).card = 2 := by
        rw [hcofaces', if_neg (by rintro ⟨i, _⟩; exact isEmptyElim i)]
      have h2 := (edgeCoboundary KA).dualMap.finrank_range_add_finrank_ker
      rw [finrank_boundary2_ker_of_two_cofaces KA htwo htri,
        Subspace.dual_finrank_eq, Module.finrank_pi] at h2
      have hTZ : LinearMap.range (edgeCoboundary KA).dualMap ≤
          LinearMap.ker (vertexCoboundary KA).dualMap := by
        rintro _ ⟨c, rfl⟩
        apply LinearMap.ext
        intro f
        change c (edgeCoboundary KA (vertexCoboundary KA f)) = 0
        rw [edgeCoboundary_vertexCoboundary, map_zero]
      have hle := Submodule.finrank_mono hTZ
      simp only [Nat.card_eq_fintype_card, Fintype.card_eq_zero] at ⊢
      omega
  rw [K.surfaceEulerCount_eq_vertex_counts]
  change (Nat.card K.vertices : ℤ) - Nat.card (Edge KA) + Nat.card (Triangle KA) ≤ _
  omega

end Geometry.SimplicialComplex
