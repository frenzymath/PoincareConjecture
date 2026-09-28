import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.OriginalDiskPairs
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.TwoDiskSphereComplement
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.MarkedAttachmentSurfaceModel




set_option autoImplicit false
noncomputable section
open Set Metric Geometry PLAnnularStrip

namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "Ann" => squareAnnulus 8 1
local notation "I" => Icc (0 : ℝ) 1

open Classical in
theorem HamiltonMarkedProtectedBall.exists_original_disk_attachment_complement
    {ι κ α E : Type*} [Fintype ι] [Unique ι] [Fintype κ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D) (hdim : Fintype.card κ = 2)
    (F : LatticeHandleAmbient ι κ L → E) (hF : Continuous F)
    (hFPL : ∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target)
    (hfi : InjOn F (latticeHandleDomain ι κ L))
    (J B : SimplicialComplex ℝ E) (hJ : J.faces.Finite) (hBJ : B ≤ J)
    (hBdim : ∀ t ∈ B.faces, t.card ≤ 2)
    (hpure : ∀ t ∈ J.faces, ∃ u ∈ J.faces, u.card = 3 ∧ t ⊆ u)
    (hcofaces : ∀ t ∈ J.faces, t.card = 2 →
      {u : Finset E | u ∈ J.faces ∧ u.card = 3 ∧ t ⊆ u}.ncard =
        if t ∈ B.faces then 1 else 2)
    (hJmark : J.space = F '' hamiltonAttachingBlock ι κ L (3 / 2))
    (hBmark : B.space = F '' (hamiltonMarkedProjection ι κ L ''
      (sphere (0 : ι → ℝ) 1 ×ˢ sphere (0 : κ → ℝ) (3 / 2)))) :
    ∃ (d r : Bool → Set E)
      (H : Ann ≃ₜ (F '' frontier D \ (J.space \ B.space) : Set E))
      (C : P2 × ℝ → E),
      (∀ side, IsFinitePLBallPair P2 (d side) (r side) ∧
        d side = F '' (hamiltonMarkedProjection ι κ L ''
          ({fun _ : ι => if side then (1 : ℝ) else -1} ×ˢ
            closedBall (0 : κ → ℝ) (3 / 2))) ∧
        r side = F '' (hamiltonMarkedProjection ι κ L ''
          ({fun _ : ι => if side then (1 : ℝ) else -1} ×ˢ
            sphere (0 : κ → ℝ) (3 / 2)))) ∧
      Disjoint (d false) (d true) ∧
      d false ∪ d true = F '' hamiltonAttachingBlock ι κ L (3 / 2) ∧
      r false ∪ r true = B.space ∧
      H.IsFinitePL ∧
      (∀ z : Ann, depth 8 (z : P2) = -1 ↔ (H z : E) ∈ r false) ∧
      (∀ z : Ann, depth 8 (z : P2) = 1 ↔ (H z : E) ∈ r true) ∧
      FinitePiecewiseAffineOn C (Ann ×ˢ I) ∧ InjOn C (Ann ×ˢ I) ∧
      MapsTo C (Ann ×ˢ I) (F '' D) ∧
      (∀ z : Ann, C (z, 0) = H z) ∧
      (∀ z ∈ Ann ×ˢ I, C z ∈ F '' frontier D ↔ z.2 = 0) ∧
      (C '' (Ann ×ˢ I)) ∩ (F '' hamiltonAttachingBlock ι κ L (3 / 2)) =
        r false ∪ r true ∧
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧
        ∀ ε : ℝ, 0 < ε → ε ≤ δ →
          IsOpen ((Subtype.val : (F '' D) → E) ⁻¹'
            (C '' ((Ann \ {z | depth 8 z = -1 ∨ depth 8 z = 1}) ×ˢ Ico 0 ε))) := by
  obtain ⟨d, r, hd, hdis, hcover⟩ := b.exists_original_disk_pairs hdim F hF hfi
    J B hJ hBJ hBdim hpure hcofaces hJmark hBmark
  have hsphere : sphere (0 : ι → ℝ) 1 =
      ({fun _ : ι => (-1 : ℝ)} ∪ {fun _ : ι => (1 : ℝ)}) := by
    ext x
    constructor
    · intro hx
      obtain ⟨side, hside⟩ := (markedDiskSignCoordinates (ι := ι)).surjective ⟨x, hx⟩
      have hv := congrArg Subtype.val hside
      rw [markedDiskSignCoordinates_apply] at hv
      cases side
      · exact Or.inl hv.symm
      · exact Or.inr hv.symm
    · rintro (hx | hx)
      · rw [show x = fun _ => (-1 : ℝ) from hx]
        simpa only [markedDiskSignCoordinates_apply, Bool.false_eq_true, if_false] using
          (markedDiskSignCoordinates (ι := ι) false).property
      · rw [show x = fun _ => (1 : ℝ) from hx]
        simpa only [markedDiskSignCoordinates_apply, if_true] using
          (markedDiskSignCoordinates (ι := ι) true).property
  have hrcover : r false ∪ r true = B.space := by
    rw [(hd false).2.2, (hd true).2.2, hBmark, hsphere, union_prod, image_union, image_union]
    rfl
  have hremove : (d false \ r false) ∪ (d true \ r true) = J.space \ B.space := by
    ext x
    constructor
    · rintro (⟨hxd, hxr⟩ | ⟨hxd, hxr⟩)
      · refine ⟨hcover.subset (Or.inl hxd), ?_⟩
        intro hxB
        rcases hrcover.symm.subset hxB with hx | hx
        · exact hxr hx
        · exact disjoint_left.mp hdis hxd ((hd true).1.1 hx)
      · refine ⟨hcover.subset (Or.inr hxd), ?_⟩
        intro hxB
        rcases hrcover.symm.subset hxB with hx | hx
        · exact disjoint_left.mp hdis ((hd false).1.1 hx) hxd
        · exact hxr hx
    · rintro ⟨hxJ, hxB⟩
      rcases hcover.symm.subset hxJ with hx | hx
      · exact Or.inl ⟨hx, fun hr => hxB (hrcover.subset (Or.inl hr))⟩
      · exact Or.inr ⟨hx, fun hr => hxB (hrcover.subset (Or.inr hr))⟩
  have hball : IsFinitePLBallPair V3 (F '' D) (F '' frontier D) :=
    b.ball.finitePLBallPair_image b.subset_domain F hFPL hfi
  have hmark : D ∩ frontier (latticeHandleDomain ι κ L) =
      hamiltonAttachingBlock ι κ L (3 / 2) := by
    rcases b.position with ⟨hzero, _⟩ | ⟨_, _, _, _, _, hmark⟩
    · simp at hzero
    · exact hmark
  have hJS : J.space ⊆ F '' frontier D := by
    rw [hJmark, ← hmark]
    apply image_mono
    intro x hx
    exact ((b.ball.frontier_inter_eq_of_subset b.subset_domain).symm.subset hx).1
  have hdS (side) : d side ⊆ F '' frontier D := by
    apply Subset.trans _ hJS
    rw [← hcover]
    cases side
    · exact subset_union_left
    · exact subset_union_right
  obtain ⟨H, C, hH, hzero, hone, hC, hCi, hCin, hCbase, hCfront, hCmeet, hCopen⟩ :=
    exists_two_disk_sphere_complement_annulus_collar hball d r (fun side => (hd side).1) hdS hdis
  have heq : F '' frontier D \ ((d false \ r false) ∪ (d true \ r true)) =
      F '' frontier D \ (J.space \ B.space) := by rw [hremove]
  refine ⟨d, r, H.trans (Homeomorph.setCongr heq), C, hd, hdis, hcover.trans hJmark,
    hrcover, hH.setCongr rfl heq, hzero, hone,
    hC, hCi, hCin, hCbase, hCfront, ?_, hCopen⟩
  simpa only [← hcover.trans hJmark] using hCmeet




theorem HamiltonMarkedProtectedBall.exists_original_disk_complement_model
    {ι κ α : Type*} [Fintype ι] [Unique ι] [Fintype κ]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L] [IsZLattice ℝ L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D)
    (he : PLDomain e (latticeHandleDomain ι κ L)) (hdim : Fintype.card κ = 2) :
    ∃ (s : Finset (latticeHandleDomain ι κ L))
      (F : LatticeHandleAmbient ι κ L → (s → ℝ × V3))
      (K J B : SimplicialComplex ℝ (s → ℝ × V3))
      (Q : latticeHandleDomain ι κ L ≃ₜ K.space)
      (g : (s → ℝ × V3) → latticeHandleDomain ι κ L)
      (d r : Bool → Set (s → ℝ × V3))
      (H : Ann ≃ₜ (F '' frontier D \ (J.space \ B.space) : Set (s → ℝ × V3)))
      (C : P2 × ℝ → (s → ℝ × V3)),
      Continuous F ∧
      (∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target) ∧
      InjOn F (latticeHandleDomain ι κ L) ∧ K.faces.Finite ∧
      K.space = F '' latticeHandleDomain ι κ L ∧
      (∀ x, (Q x : s → ℝ × V3) = F x) ∧ ContinuousOn g K.space ∧
      (∀ z : K.space, (g z : LatticeHandleAmbient ι κ L) = (Q.symm z : _)) ∧
      PolyhedralPLInCharts e (fun z => (g z : LatticeHandleAmbient ι κ L)) K.space ∧
      IsFinitePLBallPair V3 (F '' D) (F '' frontier D) ∧
      J ≤ K ∧ B ≤ J ∧ J.faces.Finite ∧ B.faces.Finite ∧
      J.space = F '' hamiltonAttachingBlock ι κ L (3 / 2) ∧
      B.space = F '' (hamiltonMarkedProjection ι κ L ''
        (sphere (0 : ι → ℝ) 1 ×ˢ sphere (0 : κ → ℝ) (3 / 2))) ∧
      (∀ side, IsFinitePLBallPair P2 (d side) (r side) ∧
        d side = F '' (hamiltonMarkedProjection ι κ L ''
          ({fun _ : ι => if side then (1 : ℝ) else -1} ×ˢ
            closedBall (0 : κ → ℝ) (3 / 2))) ∧
        r side = F '' (hamiltonMarkedProjection ι κ L ''
          ({fun _ : ι => if side then (1 : ℝ) else -1} ×ˢ
            sphere (0 : κ → ℝ) (3 / 2)))) ∧
      Disjoint (d false) (d true) ∧
      d false ∪ d true = F '' hamiltonAttachingBlock ι κ L (3 / 2) ∧
      r false ∪ r true = B.space ∧ H.IsFinitePL ∧
      (∀ z : Ann, depth 8 (z : P2) = -1 ↔ (H z : s → ℝ × V3) ∈ r false) ∧
      (∀ z : Ann, depth 8 (z : P2) = 1 ↔ (H z : s → ℝ × V3) ∈ r true) ∧
      FinitePiecewiseAffineOn C (Ann ×ˢ I) ∧ InjOn C (Ann ×ˢ I) ∧
      MapsTo C (Ann ×ˢ I) (F '' D) ∧
      (∀ z : Ann, C (z, 0) = H z) ∧
      (∀ z ∈ Ann ×ˢ I, C z ∈ F '' frontier D ↔ z.2 = 0) ∧
      (C '' (Ann ×ˢ I)) ∩ (F '' hamiltonAttachingBlock ι κ L (3 / 2)) =
        r false ∪ r true ∧
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧
        ∀ ε : ℝ, 0 < ε → ε ≤ δ →
          IsOpen ((Subtype.val : (F '' D) → (s → ℝ × V3)) ⁻¹'
            (C '' ((Ann \ {z | depth 8 z = -1 ∨ depth 8 z = 1}) ×ˢ Ico 0 ε))) := by
  obtain ⟨s, F, K, A, Q, g, J, B, hFc, hFPL, hfi, hK, hA, hKs, _, hA1, hA2,
    hQ, hgc, hg, hgPL, hball, _, _, _, _, hJA0, _, hJ, _, _, hJmark,
    hpure, hcofaces, _, hBJ, hB, hBdim, hBmark⟩ :=
      b.exists_marked_attachment_surface_model he (by simp)
  obtain ⟨d, r, H, C, hd, hdis, hcover, hrcover, hH, hzero, hone,
    hC, hCi, hCin, hCbase, hCfront, hCmeet, hCopen⟩ :=
      b.exists_original_disk_attachment_complement hdim F hFc hFPL hfi J B hJ hBJ hBdim
        hpure hcofaces hJmark hBmark
  have hball' : IsFinitePLBallPair V3 (F '' D) (F '' frontier D) := by
    rw [← hA1, ← hA2]
    exact hball
  exact ⟨s, F, K, J, B, Q, g, d, r, H, C, hFc, hFPL, hfi, hK, hKs, hQ, hgc,
    hg, hgPL, hball', hJA0.trans (hA 0).1, hBJ, hJ, hB, hJmark, hBmark,
    hd, hdis, hcover, hrcover, hH, hzero, hone, hC, hCi, hCin, hCbase,
    hCfront, hCmeet, hCopen⟩

end PoincareConjecture.M76
