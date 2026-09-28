import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.MarkedAttachmentAnnulus
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.OriginalAnnulusRimModels
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.MarkedAttachmentSurfaceModel

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Metric Geometry BrownCollar PLAnnularStrip

namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

open Classical in
theorem HamiltonMarkedProtectedBall.exists_original_attachment_annulus
    {ι κ α E : Type*} [Fintype ι] [Fintype κ] [Unique κ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D) (hi : Fintype.card ι = 2)
    (F : LatticeHandleAmbient ι κ L → E) (hF : Continuous F)
    (hfi : InjOn F (latticeHandleDomain ι κ L))
    (J B : SimplicialComplex ℝ E) (hJ : J.faces.Finite) (hBJ : B ≤ J)
    (hB : B.faces.Finite) (hBdim : ∀ t ∈ B.faces, t.card ≤ 2)
    (hJmark : J.space = F '' hamiltonAttachingBlock ι κ L (3 / 2))
    (hBmark : B.space = F '' (hamiltonMarkedProjection ι κ L ''
      (sphere (0 : ι → ℝ) 1 ×ˢ sphere (0 : κ → ℝ) (3 / 2))))
    (hpure : ∀ t ∈ J.faces, ∃ u ∈ J.faces, u.card = 3 ∧ t ⊆ u)
    (hcounts : ∀ t ∈ J.faces, t.card = 2 →
      {u : Finset E | u ∈ J.faces ∧ u.card = 3 ∧ t ⊆ u}.ncard =
        if t ∈ B.faces then 1 else 2) :
    ∃ A : squareAnnulus 8 1 ≃ₜ J.space, A.IsFinitePL ∧
      (∀ p : squareAnnulus 8 1, depth 8 (p : ℝ × ℝ) = -1 ↔
        (A p : E) ∈ F '' (hamiltonMarkedProjection ι κ L ''
          (sphere (0 : ι → ℝ) 1 ×ˢ {fun _ : κ => -(3 / 2 : ℝ)}))) ∧
      (∀ p : squareAnnulus 8 1, depth 8 (p : ℝ × ℝ) = 1 ↔
        (A p : E) ∈ F '' (hamiltonMarkedProjection ι κ L ''
          (sphere (0 : ι → ℝ) 1 ×ˢ {fun _ : κ => (3 / 2 : ℝ)}))) := by
  classical
  obtain ⟨P, hP⟩ := b.exists_marked_image_homeomorph (by omega) F hF hfi
    (sphere (0 : ι → ℝ) 1 ×ˢ closedBall (0 : κ → ℝ) (3 / 2))
    ((isCompact_sphere _ _).prod (isCompact_closedBall _ _)) subset_rfl J.space hJmark
  obtain ⟨C, gamma, hC, hfaces⟩ := b.exists_original_annulus_rim_models hi
    F hF hfi J B hB hBdim hJmark hBmark
  have hmark (i : Bool) : (C i).space = range (fun x : sphere (0 : ι → ℝ) 1 =>
      (P ⟨((x : ι → ℝ), fun _ : κ => if i then (3 / 2 : ℝ) else -(3 / 2 : ℝ)),
        x.property, by
          rw [mem_closedBall_zero_iff, pi_norm_const, Real.norm_eq_abs]
          cases i <;> norm_num⟩ : E)) := by
    rw [(hC i).2.2.2]
    simp only [hP]
    apply Subset.antisymm
    · rintro y ⟨_, ⟨x, ⟨hx, hend⟩, rfl⟩, rfl⟩
      refine ⟨⟨x.1, hx⟩, ?_⟩
      apply congrArg (F ∘ hamiltonMarkedProjection ι κ L)
      exact Prod.ext rfl hend.symm
    · rintro y ⟨x, rfl⟩
      exact ⟨_, ⟨((x : ι → ℝ), fun _ : κ => if i then (3 / 2 : ℝ) else -(3 / 2 : ℝ)),
        ⟨x.property, rfl⟩, rfl⟩, rfl⟩
  obtain ⟨A, hA, hlo, hhi⟩ := exists_marked_attachment_annulus J hJ hi P hpure C
    (fun i => (hC i).1.trans hBJ) gamma (fun i => (hC i).2.2.1) hmark
    (fun t ht htc => by simpa only [hfaces] using hcounts t ht htc)
  refine ⟨A, hA, ?_, ?_⟩
  · simpa only [(hC false).2.2.2, Bool.false_eq_true, if_false] using hlo
  · simpa only [(hC true).2.2.2, if_true] using hhi

theorem HamiltonMarkedProtectedBall.exists_original_attachment_annulus_model
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L] [IsZLattice ℝ L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D)
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (hdim : Fintype.card ι + Fintype.card κ = 3) (hi : Fintype.card ι = 2) :
    ∃ (s : Finset (latticeHandleDomain ι κ L))
      (F : LatticeHandleAmbient ι κ L → (s → ℝ × V3))
      (K : SimplicialComplex ℝ (s → ℝ × V3))
      (A : Fin 3 → SimplicialComplex ℝ (s → ℝ × V3))
      (H : latticeHandleDomain ι κ L ≃ₜ K.space)
      (g : (s → ℝ × V3) → latticeHandleDomain ι κ L)
      (J B : SimplicialComplex ℝ (s → ℝ × V3))
      (ann : squareAnnulus 8 1 ≃ₜ J.space),
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
      J = A 0 ⊓ A 2 ∧ J ≤ A 0 ∧ J ≤ A 2 ∧ J.faces.Finite ∧
      (∀ t ∈ K.faces, (∀ v ∈ t, v ∈ J.vertices) → t ∈ J.faces) ∧
      J.space = F '' (D ∩ frontier (latticeHandleDomain ι κ L)) ∧
      J.space = F '' hamiltonAttachingBlock ι κ L (3 / 2) ∧
      B = J ⊓ (A 0).closedFaceComplement J ∧ B ≤ J ∧ B.faces.Finite ∧
      B.space = F '' (hamiltonMarkedProjection ι κ L ''
        (sphere (0 : ι → ℝ) 1 ×ˢ sphere (0 : κ → ℝ) (3 / 2))) ∧
      ann.IsFinitePL ∧
      (∀ p : squareAnnulus 8 1, depth 8 (p : ℝ × ℝ) = -1 ↔
        (ann p : s → ℝ × V3) ∈ F '' (hamiltonMarkedProjection ι κ L ''
          (sphere (0 : ι → ℝ) 1 ×ˢ {fun _ : κ => -(3 / 2 : ℝ)}))) ∧
      (∀ p : squareAnnulus 8 1, depth 8 (p : ℝ × ℝ) = 1 ↔
        (ann p : s → ℝ × V3) ∈ F '' (hamiltonMarkedProjection ι κ L ''
          (sphere (0 : ι → ℝ) 1 ×ˢ {fun _ : κ => (3 / 2 : ℝ)}))) := by
  classical
  obtain ⟨hκ⟩ := Fintype.card_eq_one_iff_nonempty_unique.mp
    (show Fintype.card κ = 1 by omega)
  letI : Unique κ := hκ
  obtain ⟨s, F, K, A, H, g, J, B, hFc, hF, hfi, hK, hA, hKs, hA0, hA1, hA2,
      hH, hgc, hg, hgPL, hball, _, _, _, hJdef, hJA0, hJA2,
      hJ, hJfull, hJs, hJmark, hJpure, hJcounts, hBdef, hBJ, hB, hBdim, hBmark⟩ :=
    b.exists_marked_attachment_surface_model he (by omega)
  obtain ⟨ann, hann, hlo, hhi⟩ := b.exists_original_attachment_annulus hi
    F hFc hfi J B hJ hBJ hB hBdim hJmark hBmark hJpure hJcounts
  exact ⟨s, F, K, A, H, g, J, B, ann, hFc, hF, hfi, hK, hA, hKs, hA0, hA1, hA2,
    hH, hgc, hg, hgPL, hball, hJdef, hJA0, hJA2, hJ, hJfull, hJs, hJmark,
    hBdef, hBJ, hB, hBmark, hann, hlo, hhi⟩

end PoincareConjecture.M76
