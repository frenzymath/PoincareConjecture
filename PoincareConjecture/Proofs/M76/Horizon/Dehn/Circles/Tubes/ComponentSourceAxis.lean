import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.SourceStripClosing
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.Intervals.PairedComponentNeighborhoods

set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D2" => closedBall (0 : V2) 1

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {f : V2 → X} {R : Set X}
  {old : OrdinaryDoubleCurveModel e f R} {i : old.Index}



theorem ComponentBranchModel.graph_mem_self_paired_axis_iff
    (D : ComponentBranchModel old i) (hself : old.mate i = i)
    {w : V2} (hw : w ∈ D2) (hcore : f w ∈ D.core) :
    D.graph (f w) ∈ D.axis.space ↔ w ∈ old.pieces i := by
  have hphysical : D.graph (f w) ∈ D.axis.space ↔ f w ∈ f '' old.pieces i := by
    rw [D.axis_space]
    constructor
    · rintro ⟨v, hv, hgraph⟩
      exact ⟨v, hv, (D.graph_separates (f w) hcore (f v) hgraph.symm).symm⟩
    · rintro ⟨v, hv, hfv⟩
      exact ⟨v, hv, congrArg D.graph hfv⟩
  rw [hphysical, old.piece_image_preimage i w hw, hself, union_self]



theorem ComponentBranchModel.source_strip_selected_iff
    (D : ComponentBranchModel old i) (hself : old.mate i = i)
    {a b : ℝ} (sigma : P2 × ℝ → (D.sample → ℝ × V3))
    (haxis : ∀ z ∈ signedTubeDiamond ×ˢ Icc a b,
      sigma z ∈ D.axis.space ↔ z.1 = (0, 0))
    (phi : Fin 2 → P2 → V2)
    (hphi : ∀ j z, z ∈ Icc (-1 : ℝ) 1 ×ˢ Icc a b →
      phi j z ∈ D2 ∧ f (phi j z) = (D.inverse (sigma (signedSheetStripMap j z)) : X) ∧
        D.graph (f (phi j z)) = sigma (signedSheetStripMap j z)) :
    ∀ j z, z ∈ Icc (-1 : ℝ) 1 ×ˢ Icc a b →
      (phi j z ∈ old.pieces i ↔ z.1 = 0) := by
  intro j z hz
  have h := hphi j z hz
  have hcore : f (phi j z) ∈ D.core := h.2.1.symm ▸ (D.inverse _).property
  rw [← D.graph_mem_self_paired_axis_iff hself h.1 hcore, h.2.2,
    haxis _ (signedSheetStripMap_mem j hz)]
  fin_cases j <;> simp [signedSheetStripMap_apply]



theorem ComponentBranchModel.source_strip_axis_cover
    (D : ComponentBranchModel old i) (hself : old.mate i = i)
    {a b : ℝ} (sigma : P2 × ℝ → (D.sample → ℝ × V3))
    (haxis : ∀ z ∈ signedTubeDiamond ×ˢ Icc a b,
      sigma z ∈ D.axis.space ↔ z.1 = (0, 0))
    (haxisimage : (fun s => sigma ((0, 0), s)) '' Icc a b = D.axis.space)
    (phi : Fin 2 → P2 → V2)
    (hphi : ∀ j z, z ∈ Icc (-1 : ℝ) 1 ×ˢ Icc a b →
      phi j z ∈ D2 ∧ f (phi j z) = (D.inverse (sigma (signedSheetStripMap j z)) : X) ∧
        D.graph (f (phi j z)) = sigma (signedSheetStripMap j z))
    (hwhole : D2 ∩ f ⁻¹' ((fun z => (D.inverse (sigma z) : X)) ''
        (signedTubeDiamond ×ˢ Icc a b)) =
      ⋃ j, phi j '' (Icc (-1 : ℝ) 1 ×ˢ Icc a b)) :
    (⋃ j, (fun s => phi j (0, s)) '' Icc a b) = old.pieces i := by
  have hselected := D.source_strip_selected_iff hself sigma haxis phi hphi
  have hzero : (0 : ℝ) ∈ Icc (-1 : ℝ) 1 := by norm_num
  ext w
  constructor
  · intro hw
    obtain ⟨j, s, hs, rfl⟩ := mem_iUnion.mp hw
    exact (hselected j (0, s) ⟨hzero, hs⟩).mpr rfl
  · intro hw
    have hwD : w ∈ D2 := (old.piece_subset_double i hw).1
    have hgraph : D.graph (f w) ∈ D.axis.space :=
      D.axis_space.symm.subset ⟨w, hw, rfl⟩
    obtain ⟨s, hs, hsig⟩ := haxisimage.symm.subset hgraph
    change sigma ((0, 0), s) = D.graph (f w) at hsig
    have hsK : sigma ((0, 0), s) ∈ D.complex.space :=
      SimplicialComplex.space_subset_of_le D.axis_le (hsig.symm ▸ hgraph)
    have hvalue : (D.inverse (sigma ((0, 0), s)) : X) = f w :=
      D.graph_separates _ (D.inverse _).property _ ((D.graph_inverse _ hsK).trans hsig)
    have hwpre : w ∈ D2 ∩ f ⁻¹' ((fun z => (D.inverse (sigma z) : X)) ''
        (signedTubeDiamond ×ˢ Icc a b)) := by
      refine ⟨hwD, ((0, 0), s), ⟨?_, hs⟩, hvalue⟩
      rw [signedTubeDiamond_coordinate_iff]
      norm_num
    obtain ⟨j, z, hz, hzw⟩ := mem_iUnion.mp (hwhole.subset hwpre)
    have hz0 : z.1 = 0 := (hselected j z hz).mp (hzw.symm ▸ hw)
    refine mem_iUnion.mpr ⟨j, z.2, hz.2, ?_⟩
    have hform : (0, z.2) = z := Prod.ext hz0.symm rfl
    exact (congrArg (phi j) hform).trans hzw

end PoincareConjecture.M76.Dehn
