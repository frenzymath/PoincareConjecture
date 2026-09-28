import PoincareConjecture.Proofs.M76.Dehn.OriginalStageMarkedCycle
import PoincareConjecture.Proofs.M76.Dehn.OriginalStagePolygonDisk
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.MarkedPolygonDiskNormalization
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLComposition












set_option autoImplicit false

universe v w z

open Set Metric Geometry
open PoincareConjecture.M76.Dehn

namespace Geometry.OriginalPLTower

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1

variable {G : Type v} {M : Type w} {ι : Type z}
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [DecidableEq G] [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M V3} {S : SimplicialComplex ℝ V2}
  {f : V2 → M} {r : M → ℝ} {C : Set M}






theorem Stage.exists_marked_terminal_boundary_disk (st : Stage e S f r C)
    (hSD : S.space = D) {R : Set M} {N : Set st.Carrier} (hN : IsClosed N)
    (hDN : st.sourceMap '' S.space ⊆ N) (hNR : N ⊆ st.projection ⁻¹' R)
    (Fmark : Set M) (hFmark : Fmark ⊆ frontier R) (gamma : C(Q, Fmark))
    (hpair : ∀ x : Q, f x.val = (gamma x : M))
    (a : C(N, N))
    (H : (ContinuousMap.id N).HomotopyRel a (Subtype.val ⁻¹' (st.sourceMap '' S.space)))
    (ha : range a = Subtype.val ⁻¹' (st.sourceMap '' S.space))
    (F : st.Carrier → G)
    (hFPL : ∀ i, LocallyPiecewiseAffineOn (F ∘ (st.charts i).symm) (st.charts i).target)
    (K A : SimplicialComplex ℝ G) (hK : K.faces.Finite) (hAK : A ≤ K)
    (hfull : ∀ s ∈ K.faces, (∀ p ∈ s, p ∈ A.vertices) → s ∈ A.faces)
    (Jmodel : N ≃ₜ K.space) (g : G → N)
    (hJF : ∀ x : N, (Jmodel x : G) = F x)
    (hg : ∀ z : K.space, (g z : st.Carrier) = (Jmodel.symm z : st.Carrier))
    (hgPL : PolyhedralPLInCharts st.charts (fun z => (g z : st.Carrier)) K.space)
    (hAs : A.space = F '' frontier N)
    (hstars : ∀ p ∈ K.vertices, ∃ B : OpenPartialHomeomorph st.Carrier V3,
      MapsTo (fun z => (g z : st.Carrier)) (K.closedStar p).space B.source ∧
      (K.closedStar p).AffineOnFaces (fun z => B (g z)) ∧
      (B.source ⊆ N ∨ ∃ (ell : V3 →ᴬ[ℝ] ℝ) (v : V3),
        ell.contLinear v = 1 ∧ ∀ y ∈ B.source, y ∈ N ↔ 0 ≤ ell (B y)))
    (hterminal : ∀ (Y : Type (max w v)) [TopologicalSpace Y]
      [T2Space Y] [ConnectedSpace Y] (p : Y → st.Carrier),
      IsCoveringMap p → (∀ x, (p ⁻¹' {x}).ncard = 2) → False)
    {base : Fmark} (p : Path base (gamma squareRimBase))
    (J : Subgroup (FundamentalGroup Fmark base))
    (houtside : p.whiskeredLoopClass (squareRimLoop.map gamma.continuous) ∉ J) :
    ∃ (j : V2 → st.Carrier) (rim : C(Q, Fmark)) (q : Path base (rim squareRimBase)),
      PolyhedralPLInCharts st.charts j D ∧
      Topology.IsEmbedding (fun x : D => j x) ∧ MapsTo j D (frontier N) ∧
      (∀ x : Q, st.projection (j x) = (rim x : M)) ∧
      (∀ x : D, j x ∈ j '' Q ↔ (x : V2) ∈ Q) ∧
      q.whiskeredLoopClass (squareRimLoop.map rim.continuous) ∉ J := by
  classical
  obtain ⟨L, hLA, mark, _, hmark, _, _, B, hLB, v, c, q, hc, hout⟩ :=
    st.exists_original_marked_cycle hSD hN hDN hNR Fmark hFmark gamma hpair
      F hFPL K A hK hAK Jmodel hJF hAs p J houtside
  obtain ⟨n, P, hlen, hvertices, hbase, hinj, hP, _, hPL⟩ :=
    L.exists_polygon_of_geometric_cycle c hc
  have hu : (squareRimBase : V2) ∈ S.space :=
    hSD.symm.subset (sphere_subset_closedBall squareRimBase.property)
  have hfu : f squareRimBase ∈ frontier R := by
    rw [hpair squareRimBase]
    exact hFmark (gamma squareRimBase).property
  obtain ⟨b, b', hb, _, hbb', _⟩ := st.relative_region_polygon_disks
    hN hDN hNR hu hfu a H ha K hK A hAK hfull Jmodel F g hJF hg hAs hstars
    hterminal B P hP hinj (hPL.trans hLB)
  obtain ⟨eb, d, rim, q', _, hd, hemb, himage, hrim, _, hmarkrim, _, hout'⟩ :=
    exists_marked_normalized_polygon_disk L c P hlen hvertices hbase hP hinj hPL
      hb mark q J hout
  have hbA : b ⊆ A.space := (subset_union_left.trans hbb'.subset).trans
    (SimplicialComplex.space_subset_of_le (A.edgeComponentComplex_le B))
  have hdA : MapsTo d D A.space :=
    fun x hx => hbA (himage.subset (mem_image_of_mem d hx))
  have hdK : MapsTo d D K.space :=
    fun x hx => SimplicialComplex.space_subset_of_le hAK (hdA hx)
  let j : V2 → st.Carrier := fun x => g (d x)
  have hjPL : PolyhedralPLInCharts st.charts j D := by
    obtain ⟨T, hT, hTs, hTf⟩ := hd
    have hdT : FinitePiecewiseAffineOn d T.space := ⟨T, hT, rfl, hTf⟩
    have h := hgPL.comp_finitePiecewiseAffineOn T hT hdT
      (fun x hx => hdK (hTs.subset hx))
    exact hTs ▸ h
  have hginj : InjOn (fun z => (g z : st.Carrier)) K.space := by
    intro x hx y hy heq
    have hback : Jmodel.symm ⟨x, hx⟩ = Jmodel.symm ⟨y, hy⟩ :=
      Subtype.ext ((hg ⟨x, hx⟩).symm.trans (heq.trans (hg ⟨y, hy⟩)))
    exact congrArg Subtype.val (Jmodel.symm.injective hback)
  let : CompactSpace D := isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : V2) 1)
  have hjemb : Topology.IsEmbedding (fun x : D => j x) :=
    (hjPL.continuousOn.domRestrict.isClosedEmbedding (fun x y hxy =>
      hemb.injective (hginj (hdK x.property) (hdK y.property) hxy))).isEmbedding
  have hfront (z : G) (hz : z ∈ K.space) :
      (g z : st.Carrier) ∈ frontier N ↔ z ∈ A.space := by
    rw [hAs]
    exact PoincareConjecture.M76.original_model_mem_image_iff Jmodel F g hJF hg
      hN.frontier_subset ⟨z, hz⟩
  refine ⟨j, rim, q', hjPL, hjemb, fun x hx => (hfront _ (hdK hx)).mpr (hdA hx),
    ?_, ?_, hout'⟩
  · intro x
    rw [hmarkrim x, hmark]
    change st.projection (g (d x)) = st.projection (Jmodel.symm _)
    rw [hrim x]
    exact congrArg st.projection (hg ⟨eb x,
      SimplicialComplex.space_subset_of_le hAK (hLA (hPL (eb x).property))⟩)
  · intro x
    constructor
    · rintro ⟨y, hy, heq⟩
      have hxy : (⟨y, sphere_subset_closedBall hy⟩ : D) = x := hjemb.injective heq
      exact (congrArg Subtype.val hxy) ▸ hy
    · intro hx
      exact mem_image_of_mem j hx

end Geometry.OriginalPLTower
