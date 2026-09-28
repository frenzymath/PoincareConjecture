import PoincareConjecture.Proofs.M76.Rigidity.EmbeddedParameterCoordinates
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Polyhedra.Mathlib.PolyhedralPLSelection
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLNeighborhoodExtension
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProtectedPLDiagram









set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

variable {X Y ι κ : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  {e : ι → OpenPartialHomeomorph X V3}
  {d : κ → OpenPartialHomeomorph Y V3}

private theorem ChartwisePLMap.local_extension_coordinates
    {P : Set X} {f : C(P, (univ : Set Y))} (hf : ChartwisePLMap e d f) (x : P) :
    ∃ (i : ι) (j : κ) (U : Set V3) (G : V3 → V3),
      IsOpen U ∧ (x : X) ∈ (e i).source ∧ e i x ∈ U ∧ U ⊆ (e i).target ∧
      MapsTo G U (d j).target ∧ LocallyPiecewiseAffineOn G U ∧
      ∀ z ∈ U, ∀ hz : (e i).symm z ∈ P,
        (f ⟨(e i).symm z, hz⟩ : Y) ∈ (d j).source ∧
        G z = d j (f ⟨(e i).symm z, hz⟩) := by
  obtain ⟨i, j, K, V, F, hK, hV, hxV, _, hVi, hVK, _, _, hF, hvalue⟩ :=
    hf.coordinates x (mem_univ _)
  obtain ⟨G, W, hW, hKW, hG, hGF⟩ := hF.exists_locallyPiecewiseAffine_extension
  obtain ⟨O, hO, hOV⟩ := isOpen_induced_iff.mp hV
  let A : Set V3 := (e i).target ∩ (e i).symm ⁻¹' O
  have hA : IsOpen A := (e i).symm.continuousOn.isOpen_inter_preimage
    (e i).open_target hO
  let U : Set V3 := A ∩ (W ∩ G ⁻¹' (d j).target)
  have hU : IsOpen U := hA.inter
    (hG.continuousOn.isOpen_inter_preimage hW (d j).open_target)
  have hxi := hVi hxV
  have hxK : e i x ∈ K.space := hVK ⟨x, hxV, rfl⟩
  have hxvalue := hvalue x hxi hxK
  have hxG : G (e i x) = d j (f x) := (hGF hxK).trans hxvalue.2
  refine ⟨i, j, U, G, hU, hxi, ?_, fun _ hz => hz.1.1,
    fun _ hz => hz.2.2, hG.mono hU (fun _ hz => hz.2.1), ?_⟩
  · refine ⟨⟨(e i).map_source hxi, ?_⟩, hKW hxK, ?_⟩
    · change (e i).symm (e i x) ∈ O
      rw [(e i).left_inv hxi]
      change x ∈ Subtype.val ⁻¹' O
      rwa [hOV]
    · change G (e i x) ∈ (d j).target
      rw [hxG]
      exact (d j).map_source hxvalue.1
  · intro z hz hp
    have hlocal : (⟨(e i).symm z, hp⟩ : P) ∈ V := by
      rw [← hOV]
      exact hz.1.2
    have hzK : z ∈ K.space := by
      have h := hVK ⟨⟨(e i).symm z, hp⟩, hlocal, rfl⟩
      change e i ((e i).symm z) ∈ K.space at h
      rwa [(e i).right_inv hz.1.1] at h
    have h := hvalue ⟨(e i).symm z, hp⟩ ((e i).map_target hz.1.1) (by
      rwa [(e i).right_inv hz.1.1])
    refine ⟨h.1, (hGF hzK).trans ?_⟩
    simpa only [(e i).right_inv hz.1.1] using h.2



theorem ChartwisePLMap.closed_paste [T2Space Y]
    {P : Set X} (hP : IsClosed P)
    {old g : C((univ : Set X), (univ : Set Y))}
    (hold : ChartwisePLMap e d old)
    {f : C(P, (univ : Set Y))} (hf : ChartwisePLMap e d f)
    (hgin : ∀ x : P, g ⟨x, mem_univ _⟩ = f x)
    (hgout : ∀ x : (univ : Set X), (x : X) ∉ P → g x = old x) :
    ChartwisePLMap e d g := by
  classical
  apply chartwisePLMap_of_embedded_polyhedral_parameters (E := V3) e d
    hold.source_domain hold.target_domain g
  intro x
  have hex : ∃ (i : ι) (j : κ) (U : Set V3) (G : V3 → V3),
      IsOpen U ∧ (x : X) ∈ (e i).source ∧ e i x ∈ U ∧ U ⊆ (e i).target ∧
      MapsTo G U (d j).target ∧ LocallyPiecewiseAffineOn G U ∧
      ∀ z ∈ U, (g ⟨(e i).symm z, mem_univ _⟩ : Y) =
        old ⟨(e i).symm z, mem_univ _⟩ ∨
        (g ⟨(e i).symm z, mem_univ _⟩ : Y) = (d j).symm (G z) := by
    by_cases hx : (x : X) ∈ P
    · obtain ⟨i, j, U, G, hU, hxi, hxU, hUt, hGt, hG, hvalue⟩ :=
        hf.local_extension_coordinates ⟨x, hx⟩
      refine ⟨i, j, U, G, hU, hxi, hxU, hUt, hGt, hG, ?_⟩
      intro z hz
      by_cases hp : (e i).symm z ∈ P
      · right
        rw [hgin ⟨(e i).symm z, hp⟩, (hvalue z hz hp).2,
          (d j).left_inv (hvalue z hz hp).1]
      · exact Or.inl (congrArg Subtype.val (hgout _ hp))
    · obtain ⟨i, j, U, G, hU, hxi, hxU, hUt, hGt, hG, _⟩ :=
        hold.local_extension_coordinates x
      let W := U ∩ ((e i).target ∩ (e i).symm ⁻¹' Pᶜ)
      have hW : IsOpen W := hU.inter
        ((e i).symm.continuousOn.isOpen_inter_preimage (e i).open_target hP.isOpen_compl)
      refine ⟨i, j, W, G, hW, hxi, ?_, fun _ hz => hUt hz.1,
        fun _ hz => hGt hz.1, hG.mono hW inter_subset_left, ?_⟩
      · refine ⟨hxU, (e i).map_source hxi, ?_⟩
        change (e i).symm (e i x) ∉ P
        rwa [(e i).left_inv hxi]
      · intro z hz
        exact Or.inl (congrArg Subtype.val (hgout _ hz.2.2))
  obtain ⟨i, j, U, G, _, hxi, hxU, hUt, hGt, hG, hselect⟩ := hex
  obtain ⟨K, hK, hxK, hKU, hGK⟩ := hG (e i x) hxU
  let q (z : V3) : (univ : Set X) := ⟨(e i).symm z, mem_univ _⟩
  have hKt : K.space ⊆ (e i).target := hKU.trans hUt
  have hqc : ContinuousOn q K.space :=
    IsEmbedding.subtypeVal.continuousOn_iff.mpr ((e i).symm.continuousOn.mono hKt)
  have hqi : IsEmbedding (fun z : K.space => q z) :=
    ((e i).symm.isEmbedding_restrict.comp (IsEmbedding.inclusion hKt)).codRestrict _ _
  have hqPL : PolyhedralPLInCharts e (fun z => (q z : X)) K.space :=
    polyhedralPLInCharts_of_one_chart_inverse K hK
      ((K.affineOnFaces_affine (ContinuousAffineMap.id ℝ V3)).finitePiecewiseAffineOn hK) i hKt
  have holdPL := hold.polyhedralPLInCharts_comp K hK q hqc hqPL (mapsTo_univ _ _)
  have hnewPL : PolyhedralPLInCharts d ((d j).symm ∘ G) K.space :=
    polyhedralPLInCharts_of_one_chart_inverse K hK (hGK.finitePiecewiseAffineOn hK) j
      (hGt.mono_left hKU)
  have hgPL : PolyhedralPLInCharts d (fun z => (g (q z) : Y)) K.space :=
    holdPL.continuous_selection hold.target_domain.cover hold.target_domain.compatible K hK
      hnewPL ((continuous_subtype_val.comp g.continuous).comp_continuousOn hqc)
      (fun z hz => hselect z (hKU hz))
  have hO : IsOpen ((e i).source ∩ (e i) ⁻¹' interior K.space) :=
    (e i).continuousOn.isOpen_inter_preimage (e i).open_source isOpen_interior
  have hrange : range (fun z : K.space => q z) ∈ 𝓝 x := by
    apply Filter.mem_of_superset ((hO.preimage continuous_subtype_val).mem_nhds ⟨hxi, hxK⟩)
    intro y hy
    exact ⟨⟨e i y, interior_subset hy.2⟩, Subtype.ext ((e i).left_inv hy.1)⟩
  exact ⟨K, q, ⟨e i x, interior_subset hxK⟩, hK, hqc, hqi,
    Subtype.ext ((e i).left_inv hxi), hrange, hqPL, hgPL⟩

end PoincareConjecture.M76
