import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.OriginalAnnulusMark
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.SourceAnnulusPeriod

set_option autoImplicit false
open Set Geometry Topology PLAnnularStrip

namespace PoincareConjecture.M76

local notation "P2" => (ℝ × ℝ)
local notation "Ann" => squareAnnulus 8 1

theorem exists_finitePL_original_annular_coordinates
    {E V X ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [TopologicalSpace X]
    (e : ι → OpenPartialHomeomorph X V)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V)
    {K : SimplicialComplex ℝ E} {S B : Set X}
    (H : K.space ≃ₜ S) (F : E → X)
    (hF : PolyhedralPLInCharts e F K.space) (hFval : ∀ x : K.space, F x = (H x : X))
    (A : Ann ≃ₜ B) (hBS : B ⊆ S)
    (j : P2 → X) (hj : PolyhedralPLInCharts e j Ann)
    (hjval : ∀ z : Ann, j z = (A z : X)) :
    ∃ (C : Set E) (hCK : C ⊆ K.space) (q : Ann ≃ₜ C),
      IsCompact C ∧ IsClosed C ∧ q.IsFinitePL ∧ q.symm.IsFinitePL ∧
      (∀ z : Ann, (q z : E) = (H.symm ⟨A z, hBS (A z).property⟩ : E)) ∧
      (∀ z : Ann, (H ⟨q z, hCK (q z).property⟩ : X) = (A z : X)) ∧
      ∃ L : SimplicialComplex ℝ E, L.faces.Finite ∧ L.space = C := by
  obtain ⟨J, hJ, hJs⟩ := _root_.Dehn.exists_finite_square_annulus_complex
    (L := 8) (d := 1) (by norm_num) (by norm_num)
  let T : J.space ≃ₜ Ann := Homeomorph.setCongr hJs
  let gamma : C(J.space, S) := (ContinuousMap.inclusion hBS).comp
    ((⟨A, A.continuous⟩ : C(Ann, B)).comp ⟨T, T.continuous⟩)
  obtain ⟨v, hv, hvvalue⟩ := exists_finitePL_original_carrier_coordinates
    e hcompat H F hF hFval J hJ gamma j (hJs.symm ▸ hj) (fun z => hjval (T z))
  have hvAnn : FinitePiecewiseAffineOn v Ann := hJs ▸ hv
  let f : Ann → E := fun z => (H.symm ⟨A z, hBS (A z).property⟩ : E)
  have hfi : IsEmbedding f := IsEmbedding.subtypeVal.comp
    (H.symm.isEmbedding.comp ((IsEmbedding.inclusion hBS).comp A.isEmbedding))
  let C : Set E := range f
  have hCK : C ⊆ K.space := by
    rintro x ⟨z, rfl⟩
    exact (H.symm ⟨A z, hBS (A z).property⟩).property
  let q : Ann ≃ₜ C := hfi.toHomeomorph
  have hqvalue (z : Ann) : (q z : E) = (H.symm ⟨A z, hBS (A z).property⟩ : E) := rfl
  have hqPL : q.IsFinitePL := by
    refine ⟨v, hvAnn, ?_⟩
    intro z
    exact (hvvalue (T.symm z)).symm
  let : CompactSpace Ann := isCompact_iff_compactSpace.mp hvAnn.isCompact
  have hcompact : IsCompact C := isCompact_range hfi.continuous
  have hfinite : ∃ L : SimplicialComplex ℝ E, L.faces.Finite ∧ L.space = C := by
    obtain ⟨_, ⟨L, hL, hLs, _⟩, _⟩ := hqPL.symm
    exact ⟨L, hL, hLs⟩
  refine ⟨C, hCK, q, hcompact, hcompact.isClosed, hqPL, hqPL.symm, hqvalue, ?_, hfinite⟩
  intro z
  exact congrArg (fun x : S => (x : X)) (H.apply_symm_apply ⟨A z, hBS (A z).property⟩)

theorem original_annular_coordinate_mark_iff
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {D C : Set E} {S B : Set X}
    (H : D ≃ₜ S) (A : Ann ≃ₜ B) (q : Ann ≃ₜ C) (hCD : C ⊆ D)
    (hvalue : ∀ z : Ann, (H ⟨q z, hCD (q z).property⟩ : X) = (A z : X))
    (x : D) :
    (x : E) ∈ Dehn.originalAnnulusOpenMark q ↔
      (H x : X) ∈ Dehn.originalAnnulusOpenMark A := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    refine ⟨A (q.symm y), ?_, ?_⟩
    · simpa only [Set.mem_ofPred_eq, A.symm_apply_apply] using hy
    · have h := hvalue (q.symm y)
      rw [q.apply_symm_apply] at h
      exact h.symm.trans (congrArg (fun z : D => (H z : X)) (Subtype.ext hyx))
  · rintro ⟨y, hy, hyx⟩
    refine ⟨q (A.symm y), ?_, ?_⟩
    · simpa only [Set.mem_ofPred_eq, q.symm_apply_apply] using hy
    · have h : (⟨q (A.symm y), hCD (q (A.symm y)).property⟩ : D) = x := by
        apply H.injective
        apply Subtype.ext
        exact (hvalue (A.symm y)).trans (by simpa only [A.apply_symm_apply] using hyx)
      exact congrArg Subtype.val h

theorem isOpen_original_annular_coordinate_mark
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {D C : Set E} {S B : Set X}
    (H : D ≃ₜ S) (A : Ann ≃ₜ B) (q : Ann ≃ₜ C) (hCD : C ⊆ D)
    (hvalue : ∀ z : Ann, (H ⟨q z, hCD (q z).property⟩ : X) = (A z : X))
    (hopen : IsOpen ((Subtype.val : S → X) ⁻¹' Dehn.originalAnnulusOpenMark A)) :
    IsOpen ((Subtype.val : D → E) ⁻¹' Dehn.originalAnnulusOpenMark q) := by
  have heq : (Subtype.val : D → E) ⁻¹' Dehn.originalAnnulusOpenMark q =
      H ⁻¹' ((Subtype.val : S → X) ⁻¹' Dehn.originalAnnulusOpenMark A) := by
    ext x
    exact original_annular_coordinate_mark_iff H A q hCD hvalue x
  rw [heq]
  exact hopen.preimage H.continuous

end PoincareConjecture.M76
