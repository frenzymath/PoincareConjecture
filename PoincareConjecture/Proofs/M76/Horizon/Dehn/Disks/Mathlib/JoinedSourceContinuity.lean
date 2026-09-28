import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.RetainedDoubleRelation
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.UpperResolutionSources
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.AlternateResolutionSources
import Mathlib.Topology.ContinuousOn

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.Dehn

theorem joinSourceCopies_continuous
    {E Y : Type*} [TopologicalSpace E] [TopologicalSpace Y] {A B : Set E}
    (hAB : Disjoint A B) (hA : IsClosed A) (hB : IsClosed B)
    {jA : A → Y} {jB : B → Y} (hcA : Continuous jA) (hcB : Continuous jB) :
    Continuous (joinSourceCopies hAB jA jB) := by
  let A' : Set (A ∪ B : Set E) := Subtype.val ⁻¹' A
  let B' : Set (A ∪ B : Set E) := Subtype.val ⁻¹' B
  have hA' : IsClosed A' := hA.preimage continuous_subtype_val
  have hB' : IsClosed B' := hB.preimage continuous_subtype_val
  have hcA' : ContinuousOn (joinSourceCopies hAB jA jB) A' := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hc : Continuous (fun x : A' ↦ jA ⟨x.val.val, x.property⟩) :=
      hcA.comp ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)
    apply hc.congr
    intro x
    exact (joinSourceCopies_left hAB jA jB x.val x.property).symm
  have hcB' : ContinuousOn (joinSourceCopies hAB jA jB) B' := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hc : Continuous (fun x : B' ↦ jB ⟨x.val.val, x.property⟩) :=
      hcB.comp ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)
    apply hc.congr
    intro x
    exact (joinSourceCopies_right hAB jA jB x.val x.property).symm
  have hcover : A' ∪ B' = univ := by
    apply eq_univ_iff_forall.mpr
    intro x
    exact x.property
  have hc := hcA'.union_of_isClosed hcB' hA' hB'
  rw [hcover] at hc
  exact continuousOn_univ.mp hc

theorem UpperResolutionSources.retainedCopy_continuous
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A QA C QC : Set E} {Sstrip : Set (ℝ × ℝ)}
    {pA pC : Icc (0 : ℝ) 1 → E} {pminus pplus : Icc (0 : ℝ) 1 → Sstrip}
    {fA fC : E → X} {fS : (ℝ × ℝ) → X} {g : (Fin 2 → ℝ) → X}
    (s : UpperResolutionSources A C Sstrip pA pC pminus pplus fA fS fC g)
    (hA : IsFinitePLBallPair (ℝ × ℝ) A QA) (hC : IsFinitePLBallPair (ℝ × ℝ) C QC)
    (hAC : Disjoint A C) : Continuous (joinSourceCopies hAC s.jA s.jC) :=
  joinSourceCopies_continuous hAC hA.isCompact.isClosed hC.isCompact.isClosed
    s.embeddings.1.continuous s.embeddings.2.2.continuous

theorem AlternateResolutionSources.retainedCopy_continuous
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A QA M QM C QC : Set E} {Sstrip : Set (ℝ × ℝ)}
    {pA pL pR pC : Icc (0 : ℝ) 1 → E} {pminus pplus : Icc (0 : ℝ) 1 → Sstrip}
    {fA fM fC : E → X} {fL fR : (ℝ × ℝ) → X} {g : (Fin 2 → ℝ) → X}
    (s : AlternateResolutionSources A M C Sstrip pA pL pR pC pminus pplus fA fL fM fR fC g)
    (hA : IsFinitePLBallPair (ℝ × ℝ) A QA) (hM : IsFinitePLBallPair (ℝ × ℝ) M QM)
    (hC : IsFinitePLBallPair (ℝ × ℝ) C QC)
    (hAM : Disjoint A M) (hAC : Disjoint A C) (hMC : Disjoint M C) :
    Continuous (joinSourceCopies (disjoint_union_left.mpr ⟨hAC, hMC⟩)
      (joinSourceCopies hAM s.jA s.jM) s.jC) :=
  joinSourceCopies_continuous (disjoint_union_left.mpr ⟨hAC, hMC⟩)
    (hA.isCompact.isClosed.union hM.isCompact.isClosed) hC.isCompact.isClosed
    (joinSourceCopies_continuous hAM hA.isCompact.isClosed hM.isCompact.isClosed
      s.embeddings.1.continuous s.embeddings.2.2.1.continuous)
    s.embeddings.2.2.2.2.continuous

end PoincareConjecture.M76.Dehn
