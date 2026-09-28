import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ShortAttachmentRays
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CapAttachmentNeighborhood

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold
open Poincare.Topology.Plane.Curves PoincareConjecture.Topology.Surface
open ChartCircleArrangementVertexPatch

namespace PoincareConjecture

theorem m64Intrinsic_exists_short_cap_band_join_length
    {gamma : ℝ → AnnulusCoordinates} (hg : ContDiff ℝ ∞ gamma) {T r : ℝ}
    (hr : 0 < r) (hrT : r < T)
    (hend : gamma 0 = gamma T) (hinj : InjOn gamma (Ico 0 T))
    (hregular : ∀ t ∈ Ioo (0 : ℝ) T, deriv gamma t ≠ 0)
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hdisj : Disjoint U V) (hfU : frontier U = gamma '' Icc 0 T)
    (hfV : frontier V = gamma '' Icc 0 T)
    (H : OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates) (hbase : H 0 = gamma 0)
    (haxis : ∀ s : ℝ, H (s, 0) = gamma s)
    (haxis' : ∀ s : ℝ, H (0, s) = gamma (T - s))
    (F : Bool × Bool → OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates)
    (hsource : ∀ i,
      {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r} ⊆ (F i).source)
    (hF : ∀ i, ContDiffOn ℝ ∞ (F i) (F i).source)
    (hFi : ∀ i, ContDiffOn ℝ ∞ (F i).symm (F i).target)
    (hfirst : ∀ i, ∀ s ∈ Icc (0 : ℝ) r,
      F i (s, 0) = H (sectorParameterEquiv 0 i (s, 0)))
    (hsecond : ∀ i, ∀ s ∈ Icc (0 : ℝ) r,
      F i (0, s) = H (sectorParameterEquiv 0 i (0, s)))
    (hchord : ∀ i t, F i ((1 - t) * r, t * r) =
      (1 - t) • F i (r, 0) + t • F i (0, r))
    (hsector : ∀ i,
      F i '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r} ⊆
        H '' (H.source ∩ (sectorParameterEquiv 0 i) ''
          {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2}))
    (positive terminal : Bool) (d : AnnulusCoordinates)
    (hcapRegion : (⋃ i, ⋃ (_ : if positive then i = (true, true) else i ≠ (true, true)),
      F i '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r}) ⊆ closure U) :
    let selected := if terminal then (positive, true) else (true, positive)
    let cap := F selected '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r}
    let caps := ⋃ i, ⋃ (_ : if positive then i = (true, true) else i ≠ (true, true)),
      F i '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r}
    ∃ delta > 0, ∀ ell : ℝ, 0 < ell → ell ≤ delta →
      ∀ (L : (ℝ × ℝ) ≃L[ℝ] AnnulusCoordinates)
        (lo : ℝ → ℝ) (a b ua wa ub wb ra rb : ℝ)
        (B : ObliqueBandFaces
          (collarParameterEquiv.trans L).toHomeomorph.toOpenPartialHomeomorph
          lo a b ua wa ub wb ra rb),
        (B.endpointEdge terminal).map 0 = gamma (if terminal then T - r else r) →
        (B.endpointEdge terminal).map '' Icc (0 : ℝ) 1 =
          (fun u : ℝ => gamma (if terminal then T - r else r) + u • d) '' Icc 0 ell →
        (B.endpointEdge terminal).map '' Icc (0 : ℝ) 1 ⊆ caps →
        caps ∩ B.carrier ⊆ B.leftCut ∪ B.rightCut →
        B.carrier ⊆ closure U → B.carrier \ B.lowerArc ⊆ U →
        B.lowerArc ⊆ gamma '' Icc 0 T →
        ∃ W : Set AnnulusCoordinates, IsOpen W ∧
          gamma (if terminal then T - r else r) ∈ W ∧ W ∩ closure U ⊆ cap ∪ B.carrier := by
  classical
  dsimp only
  let selected := if terminal then (positive, true) else (true, positive)
  let caps := ⋃ i, ⋃ (_ : if positive then i = (true, true) else i ≠ (true, true)),
    F i '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r}
  have hselectedOccupied :
      if positive then selected = (true, true) else selected ≠ (true, true) := by
    cases positive <;> cases terminal <;> simp [selected]
  have hselectedSub : (F selected ''
      {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r}) ⊆ caps :=
    fun _ hz => mem_iUnion.mpr ⟨selected, mem_iUnion.mpr ⟨hselectedOccupied, hz⟩⟩
  obtain ⟨N, hN, hpN, hselectN, hfrontN, hfarN⟩ :=
    m64Intrinsic_exists_cap_attachment_neighborhood hr hrT hinj H hbase haxis haxis' F
      hsource hF hFi hfirst hsecond hsector positive terminal
  obtain ⟨delta, hdelta, hshort⟩ :=
    m64Intrinsic_exists_short_ray_in_neighborhood (gamma (if terminal then T - r else r)) d hN hpN
  obtain ⟨face, hc, hz, _, _, D, basis, _, _, hs, hcarrier, hboundary⟩ :=
    m64Intrinsic_exists_coordinate_face_of_chosen_cap (F selected) hr
      (hsource selected) (hF selected) (hFi selected)
  have hfaceSub : face.carrier ⊆ caps := hc ▸ hselectedSub
  have hchordFace (t : ℝ) : (face.boundary 0).map t =
      (1 - t) • (face.boundary 0).map 0 + t • (face.boundary 0).map 1 := by
    rw [hz t, hz 0, hz 1]
    simpa only [sub_zero, one_mul, zero_mul, sub_self] using hchord selected t
  have htip : (face.boundary 0).map (if terminal then 1 else 0) =
      gamma (if terminal then T - r else r) := by
    rw [hz]
    cases terminal
    · simpa [selected, sectorParameterEquiv_apply, haxis] using
        hfirst (true, positive) r ⟨hr.le, le_rfl⟩
    · simpa [selected, sectorParameterEquiv_apply, haxis'] using
        hsecond (positive, true) r ⟨hr.le, le_rfl⟩
  have hfar : (face.boundary 0).map (if terminal then 0 else 1) ∉ N := by
    rw [hz]
    cases terminal <;> simpa only [selected, ↓reduceIte, Bool.false_eq_true, sub_zero,
      one_mul, zero_mul, sub_self] using hfarN
  have hfront : N ∩ frontier face.carrier ⊆ gamma '' Icc 0 T ∪
      (face.boundary 0).map '' Icc (0 : ℝ) 1 := by
    rw [hc]
    rw [show (face.boundary 0).map =
      (fun t : ℝ => F selected ((1 - t) * r, t * r)) from funext hz]
    exact hfrontN
  have hp : (if terminal then T - r else r) ∈ Ioo (0 : ℝ) T := by
    cases terminal
    · exact ⟨hr, hrT⟩
    · exact ⟨sub_pos.mpr hrT, sub_lt_self T hr⟩
  have hloopdisj : Disjoint U (gamma '' Icc 0 T) := by
    have h : Disjoint (interior U) (frontier U) := disjoint_interior_frontier
    simpa only [hU.interior_eq, hfU] using h
  refine ⟨delta, hdelta, ?_⟩
  intro ell _ hell L lo a b ua wa ub wb ra rb B hpbase hcut hcutCaps hinter hBU hBregion hlower
  have hcutN : (B.endpointEdge terminal).map '' Icc (0 : ℝ) 1 ⊆ N := by
    rw [hcut]
    exact (image_mono (Icc_subset_Icc le_rfl hell)).trans hshort
  have hbaseEdge : (B.endpointEdge terminal).map 0 =
      (face.boundary 0).map (if terminal then 1 else 0) := hpbase.trans htip.symm
  have hshared := m64Intrinsic_cap_attachment_cut_subset_chord B face terminal hBregion
    hloopdisj hfaceSub hinter (hc ▸ hselectN) hfront hcutN hcutCaps
    ⟨if terminal then 1 else 0, by cases terminal <;> norm_num, hbaseEdge.symm⟩
  have hinterFace := m64Intrinsic_band_cap_inter_subset_frontier B hfaceSub hinter
  obtain ⟨W, hW, hpW, hcover⟩ := m64Intrinsic_cap_band_endpoint_covers_region hg hend hinj
    hregular hp hU hV hdisj hfU hfV face D basis hs hcarrier hboundary hchordFace L B
      terminal terminal hbaseEdge hpbase (hfaceSub.trans hcapRegion) hBU hlower hinterFace
      hN hpN hfront hfar hcutN hshared
  exact ⟨W, hW, hpW, hc ▸ hcover⟩

end PoincareConjecture
