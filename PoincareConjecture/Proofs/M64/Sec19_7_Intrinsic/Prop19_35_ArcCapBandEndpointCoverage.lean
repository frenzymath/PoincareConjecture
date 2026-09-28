import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ChordTailNeighborhood
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CapAttachmentCuts
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ArcRelativeBoundaryCover

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold
open Poincare.Topology.Plane.Curves PoincareConjecture.Topology.Surface

namespace PoincareConjecture

theorem m64Intrinsic_arc_cap_band_endpoint_covers_region
    {gamma : ℝ → AnnulusCoordinates} (hg : ContDiff ℝ ∞ gamma) {T p : ℝ}
    (hinj : InjOn gamma (Icc 0 T))
    (hregular : ∀ t ∈ Ioo (0 : ℝ) T, deriv gamma t ≠ 0) (hp : p ∈ Ioo (0 : ℝ) T)
    {D U V : Set AnnulusCoordinates} (hD : IsCompact D) (hpD : gamma p ∉ D)
    (hU : IsOpen U) (hV : IsOpen V) (hdisj : Disjoint U V)
    (hfU : frontier U = gamma '' Icc 0 T ∪ D)
    (hfV : frontier V = gamma '' Icc 0 T ∪ D)
    (face : SmoothFace AnnulusCoordinates)
    (C : OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates)
    (basis : AffineBasis (Fin 3) ℝ AnnulusCoordinates)
    (hsource : convexHull ℝ (range basis) ⊆ C.source)
    (hcarrier : face.carrier = C '' convexHull ℝ (range basis))
    (hboundary : ∀ k : Fin 3, (face.boundary k).map = C ∘
      affineChartSegment (basis (k.succAbove 0)) (basis (k.succAbove 1)))
    (hchord : ∀ t : ℝ, (face.boundary 0).map t =
      (1 - t) • (face.boundary 0).map 0 + t • (face.boundary 0).map 1)
    (L : (ℝ × ℝ) ≃L[ℝ] AnnulusCoordinates)
    {lo : ℝ → ℝ} {a b ua wa ub wb ra rb : ℝ}
    (B : ObliqueBandFaces
      (collarParameterEquiv.trans L).toHomeomorph.toOpenPartialHomeomorph
      lo a b ua wa ub wb ra rb)
    (right terminal : Bool)
    (hbase : (B.endpointEdge right).map 0 = (face.boundary 0).map (if terminal then 1 else 0))
    (hpbase : (B.endpointEdge right).map 0 = gamma p)
    (hsubFace : face.carrier ⊆ closure U) (hsubBand : B.carrier ⊆ closure U)
    (hlower : B.lowerArc ⊆ gamma '' Icc 0 T)
    (hinter : face.carrier ∩ B.carrier ⊆ frontier face.carrier)
    {N : Set AnnulusCoordinates} (hN : IsOpen N) (hpN : gamma p ∈ N)
    (hfront : N ∩ frontier face.carrier ⊆ gamma '' Icc 0 T ∪
      (face.boundary 0).map '' Icc (0 : ℝ) 1)
    (hfar : (face.boundary 0).map (if terminal then 0 else 1) ∉ N)
    (hcutN : (B.endpointEdge right).map '' Icc (0 : ℝ) 1 ⊆ N)
    (hshared : (B.endpointEdge right).map '' Icc (0 : ℝ) 1 ⊆
      (face.boundary 0).map '' Icc (0 : ℝ) 1) :
    ∃ W : Set AnnulusCoordinates, IsOpen W ∧ gamma p ∈ W ∧
      W ∩ closure U ⊆ face.carrier ∪ B.carrier := by
  have hcutOne : (B.endpointEdge right).map 1 ∈ N := hcutN ⟨1, by norm_num, rfl⟩
  have hfarNe : (B.endpointEdge right).map 1 ≠
      (face.boundary 0).map (if terminal then 0 else 1) := by
    intro heq
    exact hfar (heq ▸ hcutOne)
  obtain ⟨O, hO, hpO, htail, htip⟩ := m64Intrinsic_exists_chord_tail_neighborhood
    (face.boundary 0).map (B.endpointEdge right).map hchord
    (m64Intrinsic_coordinate_face_boundary_injective face C basis hsource hboundary 0)
    (B.endpointEdge_injective right) (m64Intrinsic_band_endpoint_image_eq_segment L B right)
    hshared terminal hbase hfarNe
  obtain ⟨J, hJ, hpJ, hfrontBand⟩ := m64Intrinsic_exists_band_endpoint_neighborhood B right
  have hcancel := m64Intrinsic_cap_attachment_open_cut_interior B face C basis hsource
    hcarrier hboundary right terminal hbase hfar hcutN hshared hinter
  let K := face.carrier ∪ B.carrier
  have hKclosed : IsClosed K := face.isClosed_carrier.union B.isClosed_carrier
  have hfaceRegular : closure (interior face.carrier) = face.carrier := by
    rw [hcarrier]
    exact coordinate_triangle_closure_interior C basis hsource
  have hKregular : closure (interior K) = K := by
    apply subset_antisymm (closure_minimal interior_subset hKclosed)
    rintro z (hz | hz)
    · rw [← hfaceRegular] at hz
      exact closure_mono (interior_mono (subset_union_left : face.carrier ⊆ K)) hz
    · rw [← B.closure_interior_carrier] at hz
      exact closure_mono (interior_mono (subset_union_right : B.carrier ⊆ K)) hz
  have hpK : gamma p ∈ K := by
    rw [← hpbase]
    right
    exact B.isClosed_carrier.frontier_subset
      (B.endpointEdge_subset_frontier right ⟨0, by norm_num, rfl⟩)
  have hNJO : N ∩ J ∩ O ∈ 𝓝 (gamma p) :=
    ((hN.inter hJ).inter hO).mem_nhds ⟨⟨hpN, hpbase ▸ hpJ⟩, hpbase ▸ hpO⟩
  apply m64Intrinsic_exists_arc_relative_cover_of_local_frontier hg hinj hregular hp
    hD hpD hU hV hdisj hfU hfV hKclosed hKregular (union_subset hsubFace hsubBand) hpK hNJO
  intro z hz
  have hcut (hzcut : z ∈ (B.endpointEdge right).map '' Icc (0 : ℝ) 1) :
      z ∈ gamma '' Icc 0 T := by
    obtain ⟨u, hu, rfl⟩ := hzcut
    by_cases hu0 : u = 0
    · exact ⟨p, Ioo_subset_Icc_self hp, by rw [hu0, hpbase]⟩
    have hu1 : u ≠ 1 := by
      intro hu1
      exact htip (hu1 ▸ hz.1.2)
    exact False.elim (hz.2.2 (hcancel
      ⟨u, ⟨lt_of_le_of_ne hu.1 (Ne.symm hu0), lt_of_le_of_ne hu.2 hu1⟩, rfl⟩))
  rcases frontier_union_subset face.carrier B.carrier hz.2 with hzFace | hzBand
  · rcases hfront ⟨hz.1.1.1, hzFace.1⟩ with hzLoop | hzChord
    · exact Or.inl hzLoop
    · exact Or.inl (hcut (htail ⟨hz.1.2, hzChord⟩))
  · rcases hfrontBand ⟨hz.1.1.2, hzBand.2⟩ with hzLower | hzCut
    · exact Or.inl (hlower hzLower)
    · exact Or.inl (hcut hzCut)

end PoincareConjecture
