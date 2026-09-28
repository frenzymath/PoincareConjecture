import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.IncidentJointTransport
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Tubes.Joints.IncidentSigns

set_option autoImplicit false
open Set Metric Geometry Topology Geometry.SimplicialComplex

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)

open Classical in
theorem ComponentBranchModel.exists_incident_joint_transport
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X] {S : Set E}
    {e : ι → OpenPartialHomeomorph X V3} {f : E → X} {R : Set X}
    {old : SourceCircleDecomposition f S} {i : old.Index}
    (D : ComponentBranchModel (e := e) (R := R) old i) [Fintype D.complex.faces]
    (hcore : D.core ⊆ interior R)
    (s : Finset (D.sample → ℝ × V3)) (hs : s ∈ D.axis.faces) (hcard : s.card = 2)
    (p v : D.sample → ℝ × V3) (hps : p ∈ s) (hvs : v ∈ s)
    {x y x' y' : E} (C : RawSourceCrossing e f S R x y) (C' : RawSourceCrossing e f S R x' y')
    (hC : MapsTo (fun z ↦ (D.inverse z : X)) (D.complex.closedStar p).space C.chart.source)
    (hC' : MapsTo (fun z ↦ (D.inverse z : X)) (D.complex.closedStar v).space C'.chart.source)
    (hface : (D.complex.closedStar v).AffineOnFaces (fun z ↦ C'.chart (D.inverse z)))
    (haxis : ∀ z ∈ (D.complex.closedStar v).space,
      z ∈ D.axis.space ↔ (D.inverse z : X) ∈ R ∧
        C'.chart (D.inverse z) 0 = 0 ∧ C'.chart (D.inverse z) 1 = 0)
    (hsheet : ∀ j : Fin 2,
      ((D.complex.closedStar v).vertexSubcomplex
        {z | (D.inverse z : X) ∈ R ∧ C'.chart (D.inverse z) j.castSucc = 0}).space =
      (D.complex.closedStar v).space ∩
        {z | (D.inverse z : X) ∈ R ∧ C'.chart (D.inverse z) j.castSucc = 0})
    (J : SignedJointCross (D.sample → ℝ × V3))
    (hJ : J.disk = (D.complex.barycentricDualBlock s).space)
    (hcoord : J.coordinate = fun j z => C.chart (D.inverse z) j.castSucc)
    (hcoface : ∀ j b, ∃ t : Finset (D.sample → ℝ × V3),
      t ∈ D.complex.faces ∧ s ⊆ t ∧ t.card = 3 ∧ J.endpoint j b = t.centroid ℝ id) :
    ∃ (swap : Bool) (eta : Fin 2 → Bool),
      (∀ j z, z ∈ J.disk → (J.coordinate j z = 0 ↔
        C'.chart (D.inverse z) (jointSheetIndex swap j).castSucc = 0)) ∧
      (∀ j : Fin 2, if eta j then
        C'.chart (D.inverse (J.endpoint j.rev false)) (jointSheetIndex swap j).castSucc < 0 ∧
          0 < C'.chart (D.inverse (J.endpoint j.rev true)) (jointSheetIndex swap j).castSucc
        else
          0 < C'.chart (D.inverse (J.endpoint j.rev false)) (jointSheetIndex swap j).castSucc ∧
          C'.chart (D.inverse (J.endpoint j.rev true)) (jointSheetIndex swap j).castSucc < 0) ∧
      ∀ j b z, z ∈ J.disk →
        (SignedJointCross.side b (J.coordinate j z) ↔
          SignedJointCross.side (if eta j then b else !b)
            (C'.chart (D.inverse z) (jointSheetIndex swap j).castSucc)) := by
  classical
  let L := D.complex.barycentricDualBlock s
  have hLK : L.space ⊆ D.complex.space := (D.joint_subset_star hs hps).trans
    (SimplicialComplex.space_subset_of_le
      (show D.complex.closedStar p ≤ D.complex from fun _ ht => ht.1))
  have hLC : MapsTo (fun z ↦ (D.inverse z : X)) L.space C.chart.source :=
    fun _ hz => hC (D.joint_subset_star hs hps hz)
  have hLC' : MapsTo (fun z ↦ (D.inverse z : X)) L.space C'.chart.source :=
    fun _ hz => hC' (D.joint_subset_star hs hvs hz)
  obtain ⟨swap, hswap⟩ := D.exists_joint_sheet_swap hcore L
    (D.complex.barycentricDualBlock_finite s) hLK C C' hLC hLC' J hJ hcoord
  have hzero (j : Fin 2) (z : D.sample → ℝ × V3) (hz : z ∈ J.disk) :
      J.coordinate j z = 0 ↔ C'.chart (D.inverse z) (jointSheetIndex swap j).castSucc = 0 := by
    rw [hcoord]
    have hzL := hJ.subset hz
    fin_cases j
    · cases swap <;> simpa [jointSheetIndex] using hswap false z hzL
    · cases swap <;> simpa [jointSheetIndex] using hswap true z hzL
  obtain ⟨eta, heta⟩ := D.exists_incident_joint_signs hcore s hs hcard v hvs
    C' hC' hface haxis hsheet J hJ hcoface swap hzero
  have hcont (j : Fin 2) : ContinuousOn
      (fun z => C'.chart (D.inverse z) (jointSheetIndex swap j).castSucc) J.disk :=
    (continuous_apply _).comp_continuousOn
      (C'.chart.continuousOn.comp (D.inverse_PL.continuousOn.mono (hJ.subset.trans hLK))
        (fun _ hz => hLC' (hJ.subset hz)))
  exact ⟨swap, eta, hzero, heta, J.side_iff_of_zero_and_endpoint_signs
    (fun j z => C'.chart (D.inverse z) (jointSheetIndex swap j).castSucc)
    hcont hzero eta heta⟩

end PoincareConjecture.M76.Dehn.Annuli
