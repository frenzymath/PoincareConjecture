import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.FiniteAttachmentRim
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.RegularClosedAttachment
import PoincareConjecture.Proofs.M76.PrimeReduction.ProtectedDomainChartStars
import PoincareConjecture.Proofs.M76.PrimeReduction.OriginalBoundaryLinks
import PoincareConjecture.Proofs.M76.PrimeReduction.OriginalBoundaryMarks
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.OriginalFiniteModelBallImages
import PoincareConjecture.Proofs.M76.Mathlib.FaceLinkCofaceCount










set_option autoImplicit false
open Set Geometry Metric

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

open Classical in



theorem HamiltonMarkedProtectedBall.exists_marked_attachment_surface_model
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L] [IsZLattice ℝ L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D)
    (he : PLDomain e (latticeHandleDomain ι κ L)) (hpos : 0 < Fintype.card ι) :
    ∃ (s : Finset (latticeHandleDomain ι κ L))
      (F : LatticeHandleAmbient ι κ L → (s → ℝ × V3))
      (K : SimplicialComplex ℝ (s → ℝ × V3))
      (A : Fin 3 → SimplicialComplex ℝ (s → ℝ × V3))
      (H : latticeHandleDomain ι κ L ≃ₜ K.space)
      (g : (s → ℝ × V3) → latticeHandleDomain ι κ L)
      (J B : SimplicialComplex ℝ (s → ℝ × V3)),
      Continuous F ∧
      (∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target) ∧
      InjOn F (latticeHandleDomain ι κ L) ∧ K.faces.Finite ∧
      (∀ i, A i ≤ K ∧ (A i).faces.Finite ∧
        ∀ t ∈ K.faces, (∀ v ∈ t, v ∈ (A i).vertices) → t ∈ (A i).faces) ∧
      K.space = F '' latticeHandleDomain ι κ L ∧
      (A 0).space = F '' frontier (latticeHandleDomain ι κ L) ∧
      (A 1).space = F '' D ∧ (A 2).space = F '' frontier D ∧
      (∀ x, (H x : s → ℝ × V3) = F x) ∧ ContinuousOn g K.space ∧
      (∀ z : K.space, (g z : LatticeHandleAmbient ι κ L) = (H.symm z : _)) ∧
      PolyhedralPLInCharts e (fun z => (g z : LatticeHandleAmbient ι κ L)) K.space ∧
      IsFinitePLBallPair V3 (A 1).space (A 2).space ∧
      (∀ t ∈ (A 0).faces, ∃ u ∈ (A 0).faces, t ⊆ u ∧ u.card = 3) ∧
      (∀ t ∈ (A 0).faces, t.card = 2 →
        {u : Finset (s → ℝ × V3) | u ∈ (A 0).faces ∧ u.card = 3 ∧ t ⊆ u}.ncard = 2) ∧
      (∀ p ∈ (A 0).vertices, IsConnected ((A 0).faceLink {p}).space) ∧
      J = A 0 ⊓ A 2 ∧ J ≤ A 0 ∧ J ≤ A 2 ∧ J.faces.Finite ∧
      (∀ t ∈ K.faces, (∀ v ∈ t, v ∈ J.vertices) → t ∈ J.faces) ∧
      J.space = F '' (D ∩ frontier (latticeHandleDomain ι κ L)) ∧
      J.space = F '' hamiltonAttachingBlock ι κ L (3 / 2) ∧
      (∀ t ∈ J.faces, ∃ u ∈ J.faces, u.card = 3 ∧ t ⊆ u) ∧
      (∀ t ∈ J.faces, t.card = 2 →
        {u : Finset (s → ℝ × V3) | u ∈ J.faces ∧ u.card = 3 ∧ t ⊆ u}.ncard =
          if t ∈ B.faces then 1 else 2) ∧
      B = J ⊓ (A 0).closedFaceComplement J ∧ B ≤ J ∧ B.faces.Finite ∧
      (∀ t ∈ B.faces, t.card ≤ 2) ∧
      B.space = F '' (hamiltonMarkedProjection ι κ L ''
        (sphere (0 : ι → ℝ) 1 ×ˢ sphere (0 : κ → ℝ) (3 / 2))) := by
  classical
  let R := latticeHandleDomain ι κ L
  obtain ⟨s, F, K, A, H, g, hFc, hF, hK, hA, hKs, hA0, hA1, hA2,
      hH, hgc, hg, hgPL, hstars⟩ := exists_protected_domain_chart_stars
    (isCompact_latticeHandleDomain ι κ L) he b.subset_domain b.ball
  have hinj : InjOn F R := by
    intro x hx y hy hxy
    have hh : H ⟨x, hx⟩ = H ⟨y, hy⟩ := Subtype.ext
      ((hH ⟨x, hx⟩).trans (hxy.trans (hH ⟨y, hy⟩).symm))
    exact congrArg Subtype.val (H.injective hh)
  have hboundary (z : s → ℝ × V3) (hz : z ∈ K.space) :
      (g z : LatticeHandleAmbient ι κ L) ∈ frontier R ↔ z ∈ (A 0).space := by
    rw [hA0]
    exact original_model_mem_image_iff H F g hH hg he.closed.frontier_subset ⟨z, hz⟩
  obtain ⟨hpure, hcofaces, hlinks⟩ := original_boundary_surface_incidence
    K (A 0) hK (hA 0).1 he.closed.frontier_subset H g hg hboundary
    (fun p hp => by
      obtain ⟨C, hmap, _, hface, hkind⟩ := hstars p hp
      exact ⟨C, hmap, hface, hkind⟩)
  have hball : IsFinitePLBallPair V3 (A 1).space (A 2).space := by
    rw [hA1, hA2]
    exact b.ball.finitePLBallPair_image b.subset_domain F hF hinj
  have hcounts (t : Finset (s → ℝ × V3)) (ht : t ∈ (A 0).faces) (htc : t.card = 2) :
      {u : Finset (s → ℝ × V3) | u ∈ (A 0).faces ∧ u.card = 3 ∧ t ⊆ u}.ncard = 2 := by
    have hc : ((A 0).faceLink t).vertices.ncard =
        {u : Finset (s → ℝ × V3) | u ∈ (A 0).faces ∧ u.card = 3 ∧ t ⊆ u}.ncard := by
      simpa only [htc] using (A 0).ncard_faceLink_vertices_eq_cofaces t
    exact hc.symm.trans (hcofaces t ht htc)
  have hmark : D ∩ frontier R = hamiltonAttachingBlock ι κ L (3 / 2) := by
    rcases b.position with ⟨hzero, _⟩ | ⟨_, _, _, _, _, hmark⟩
    · omega
    · exact hmark
  let J := A 0 ⊓ A 2
  have hJs : J.space = F '' (D ∩ frontier R) := by
    rw [K.space_inf_eq_inter_of_le (A 0) (A 2) (hA 0).1 (hA 2).1, hA0, hA2]
    apply Subset.antisymm
    · rintro z ⟨⟨x, hx, rfl⟩, y, hy, hyx⟩
      have hyx' : y = x := hinj (b.subset_domain (b.ball.boundary_subset hy))
        (he.closed.frontier_subset hx) hyx
      exact ⟨x, ⟨b.ball.boundary_subset (hyx' ▸ hy), hx⟩, rfl⟩
    · rintro z ⟨x, hx, rfl⟩
      have hxd := (b.ball.frontier_inter_eq_of_subset b.subset_domain).symm.subset hx
      exact ⟨⟨x, hx.2, rfl⟩, x, hxd.1, rfl⟩
  have hJmark : J.space = F '' hamiltonAttachingBlock ι κ L (3 / 2) := by
    rw [hJs, hmark]
  have hJreg := b.marked_patch_finite_regular_closed he hpos (A 0) J F hFc hinj hA0 hJmark
  have hA0pure : ∀ t ∈ (A 0).faces, ∃ u ∈ (A 0).faces, u.card = 3 ∧ t ⊆ u := by
    intro t ht
    obtain ⟨u, hu, htu, huc⟩ := hpure t ht
    exact ⟨u, hu, huc, htu⟩
  have hJpure := (A 0).pure_of_relative_regular_closed J (hA 0).2.1 inf_le_left hA0pure hJreg
  let B := J ⊓ (A 0).closedFaceComplement J
  have hJ : J.faces.Finite := (hA 0).2.1.subset inf_le_left
  have hB : B.faces.Finite := hJ.subset inf_le_left
  have hBs : B.space = F '' (hamiltonMarkedProjection ι κ L ''
      (sphere (0 : ι → ℝ) 1 ×ˢ sphere (0 : κ → ℝ) (3 / 2))) :=
    b.marked_rim_subcomplex_space he hpos (A 0) J (hA 0).2.1 inf_le_left
      F hFc hinj hA0 hJmark
  refine ⟨s, F, K, A, H, g, J, B, hFc, hF, hinj, hK, hA, hKs, hA0, hA1, hA2,
    hH, hgc, hg, hgPL, hball, hpure, hcounts, hlinks, rfl, inf_le_left, inf_le_right,
    hJ, ?_, hJs, hJmark, hJpure, ?_, rfl, inf_le_left, hB, ?_, hBs⟩
  · intro t ht htv
    exact ⟨(hA 0).2.2 t ht (fun v hv => (htv v hv).1),
      (hA 2).2.2 t ht (fun v hv => (htv v hv).2)⟩
  · intro t ht htc
    exact (A 0).edge_coface_count_of_relative_regular_closed J (hA 0).2.1 inf_le_left
      hA0pure hcounts hJreg ht htc
  · exact (A 0).closedFaceComplement_inter_dim J (fun t ht => by
      obtain ⟨u, _, htu, huc⟩ := hpure t ht
      exact (Finset.card_le_card htu).trans_eq huc)

end PoincareConjecture.M76
