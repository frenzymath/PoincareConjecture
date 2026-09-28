import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.Cuts.RimComponents
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.Cuts.TwoBandConnected
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.SourceAnnulusSquares



set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn.Annuli

open Classical in



theorem exists_connected_cut_band_assignment
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (N : Bool → Set E) (hN : ∀ b, IsClosed (N b))
    (hdisN : Disjoint (N false) (N true))
    (hconn : IsPreconnected (K.space ∪ ⋃ b, N b))
    (c : ∀ b, squareAnnulus 1 (1 / 8) ≃ₜ N b)
    (hcut : ∀ b x, (c b x : E) ∈ K.space ↔
      depth 1 x = -(1 / 8 : ℝ) ∨ depth 1 x = 1 / 8)
    (B : Bool × Bool → SimplicialComplex ℝ E) (hBK : ∀ i, B i ≤ K)
    (gamma : ∀ i, sphere (0 : Fin 2 → ℝ) 1 ≃ₜ (B i).space)
    (hgamma : ∀ i, (gamma i).IsFinitePL)
    (hlevel : ∀ i x, (c i.1 x : E) ∈ (B i).space ↔
      depth 1 x = if i.2 then (1 / 8 : ℝ) else -(1 / 8 : ℝ)) :
    ∃ r : Bool → Bool → K.vertexAbstractComplex.edgeGraph.ConnectedComponent,
      (∀ b s, B (b, s) ≤ K.edgeComponentComplex (r b s)) ∧
      (twoBandGraph r).Connected ∧
      ∀ C, ∃ b s, r b s = C := by
  classical
  let : Finite K.vertices := (K.finite_vertices_of_finite_faces hK).to_subtype
  have hBconn (i : Bool × Bool) : IsConnected (B i).space :=
    (circle_incidence (B i) (hK.subset (hBK i)) (gamma i) (hgamma i)).2.2.1
  obtain ⟨r₀, hr₀, _⟩ := exists_rim_component_assignment K hK B hBK hBconn
  let r := fun b s ↦ r₀ (b, s)
  have hgraph : (twoBandGraph r).Connected := by
    apply twoBandGraph_connected_of_closed_cover
      (fun C ↦ (K.edgeComponentComplex C).space) N r
      (fun C ↦ ((K.edgeComponentComplex C).isCompact_space_of_finite
        (hK.subset (K.edgeComponentComplex_le C))).isClosed) hN
      (fun C ↦ (K.edgeComponentComplex_isPathConnected C).nonempty)
      K.pairwise_disjoint_edgeComponentComplex_space hdisN ?_ ?_
    · intro C b hmeet
      obtain ⟨x, hxC, hxN⟩ := hmeet
      let p := (c b).symm ⟨x, hxN⟩
      have hp : (c b p : E) = x := congrArg Subtype.val ((c b).apply_symm_apply _)
      have hxK := SimplicialComplex.space_subset_of_le (K.edgeComponentComplex_le C) hxC
      have hd := (hcut b p).mp (hp ▸ hxK)
      have H (s : Bool) (hs : depth 1 p = if s then (1 / 8 : ℝ) else -(1 / 8 : ℝ)) :
          C = r b s := by
        have hxB : x ∈ (B (b, s)).space := hp ▸ (hlevel (b, s) p).mpr hs
        exact ((mem_component_of_assigned_rim_iff K (B (b, s)) (r b s) C
          (hr₀ (b, s)) hxB).mp hxC).symm
      exact hd.elim (fun hd ↦ Or.inl (H false hd)) (fun hd ↦ Or.inr (H true hd))
    · simpa only [K.iUnion_edgeComponentComplex_space] using hconn
  exact ⟨r, fun b s ↦ hr₀ (b, s), hgraph, twoBandGraph_components_hit r hgraph⟩

end PoincareConjecture.M76.Dehn.Annuli
