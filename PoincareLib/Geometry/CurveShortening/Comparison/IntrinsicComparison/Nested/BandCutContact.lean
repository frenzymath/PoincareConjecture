import PoincareLib.Geometry.CurveShortening.Comparison.IntrinsicComparison.Nested.GraphBands
import PoincareLib.Geometry.CurveShortening.Comparison.IntrinsicComparison.Band.CutContacts

/-! Nesting with unchanged coordinates preserves exact endpoint contacts.
Source: MT Claim 19.40; joined-orientation derivation, Section 6. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold
open Poincare.Topology.Plane.Curves PoincareMT.Topology.Surface

namespace PoincareMT

private theorem endpoint_height_image
    {F : OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates}
    {f : ℝ → ℝ} {a b ua wa ub wb ra rb : ℝ}
    (B : ObliqueBandFaces F f a b ua wa ub wb ra rb) (right : Bool) :
    (fun z => B.coordinates (collarParameterEquiv.symm (if right then 1 else 0, z))) ''
      Icc (0 : ℝ) (B.height (if right then 1 else 0)) =
        if right then B.rightCut else B.leftCut := by
  cases right
  · exact B.left_height_image
  · exact B.right_height_image

/-- A band nested in the original coordinate subgraph meets an original endpoint cut in
exactly its own shorter endpoint cut. Source:
`proof-work/tasks/M64/derivations/2026-09-27-joined-orientation-and-attachments.md`, Section
6. -/
theorem m64Intrinsic_nested_band_cut_contact
    {F : OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates}
    {f : ℝ → ℝ} {a b ua wa ub wb ra rb sa sb : ℝ}
    (B : ObliqueBandFaces F f a b ua wa ub wb ra rb)
    (C : ObliqueBandFaces F f a b ua wa ub wb sa sb)
    (hcoordinates : ∀ q, C.coordinates q = B.coordinates q) (hband : C.band ⊆ B.band)
    (right : Bool) :
    C.carrier ∩ (if right then B.rightCut else B.leftCut) =
      if right then C.rightCut else C.leftCut := by
  let e : ℝ := if right then 1 else 0
  have he : e ∈ Icc (0 : ℝ) 1 := by cases right <;> simp [e]
  rw [← endpoint_height_image B right, ← endpoint_height_image C right]
  ext p
  constructor
  · rintro ⟨hpC, z, hz, hzp⟩
    obtain ⟨q, hq, hqp⟩ := C.carrier_eq_image ▸ hpC
    have heq : B.coordinates (collarParameterEquiv.symm (e, z)) = B.coordinates q :=
      hzp.trans (hqp.symm.trans (hcoordinates q))
    have hqeq := B.coordinates.injOn (m64Intrinsic_band_height_mem_source B he hz)
      (B.band_subset_source (hband hq)) heq
    have hqe : (collarParameterEquiv q).1 = e := by
      simpa only [collarParameterEquiv.apply_symm_apply] using
        (congrArg (fun x => (collarParameterEquiv x).1) hqeq).symm
    have hq' := C.band_eq_subgraph ▸ hq
    refine ⟨(collarParameterEquiv q).2, ⟨hq'.2.1, ?_⟩, ?_⟩
    · simpa only [hqe] using hq'.2.2
    · change C.coordinates (collarParameterEquiv.symm (e, (collarParameterEquiv q).2)) = p
      rw [← hqe, Prod.eta, collarParameterEquiv.symm_apply_apply]
      exact hqp
  · rintro ⟨z, hz, rfl⟩
    have hq : collarParameterEquiv.symm (e, z) ∈ C.band := by
      rw [C.band_eq_subgraph]
      simpa only [mem_ofPred_eq, collarParameterEquiv.apply_symm_apply, mem_Icc, e]
        using And.intro he hz
    have hqB := B.band_eq_subgraph ▸ hband hq
    have hzB : z ∈ Icc (0 : ℝ) (B.height e) := by
      simpa only [collarParameterEquiv.apply_symm_apply, mem_Icc] using hqB.2
    refine ⟨?_, z, hzB, (hcoordinates _).symm⟩
    rw [C.carrier_eq_image]
    exact ⟨collarParameterEquiv.symm (e, z), hq, rfl⟩

end PoincareMT
