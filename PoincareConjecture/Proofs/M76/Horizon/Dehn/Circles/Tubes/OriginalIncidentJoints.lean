import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.IncidentJointTransport

set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)

open Classical in

theorem ComponentBranchModel.exists_incident_joints
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {f : V2 → X} {R : Set X}
    {old : OrdinaryDoubleCurveModel e f R} {i : old.Index}
    (D : ComponentBranchModel old i) (hcore : D.core ⊆ interior R) :
    letI : Fintype D.complex.faces := D.complex_finite.fintype
    ∃ (x y : D.axis.vertices → V2) (C : ∀ v, RawCrossingChart e f R (x v) (y v)),
      (∀ v : D.axis.vertices, MapsTo (fun z ↦ (D.inverse z : X)) (D.complex.closedStar v).space
        (C v).chart.source) ∧
      (∀ v : D.axis.vertices,
        (D.complex.closedStar v).AffineOnFaces (fun z ↦ (C v).chart (D.inverse z))) ∧
      (∀ (v : D.axis.vertices) z, z ∈ (D.complex.closedStar v).space →
        (z ∈ D.axis.space ↔ (D.inverse z : X) ∈ R ∧
          (C v).chart (D.inverse z) 0 = 0 ∧ (C v).chart (D.inverse z) 1 = 0)) ∧
      (∀ (v : D.axis.vertices) (j : Fin 2),
        ((D.complex.closedStar v).vertexSubcomplex
          {z | (D.inverse z : X) ∈ R ∧ (C v).chart (D.inverse z) j.castSucc = 0}).space =
        (D.complex.closedStar v).space ∩
          {z | (D.inverse z : X) ∈ R ∧ (C v).chart (D.inverse z) j.castSucc = 0}) ∧
      ∀ s ∈ D.axis.faces, s.card = 2 →
        ∃ (J : SignedJointCross (D.sample → ℝ × V3)),
          J.disk = (D.complex.barycentricDualBlock s).space ∧
          J.rim = ((D.complex.barycentricDualBlock s).link (s.centroid ℝ id)).space ∧
          J.center = s.centroid ℝ id ∧
          (∀ j b, ∃ t : Finset (D.sample → ℝ × V3),
            t ∈ D.complex.faces ∧ s ⊆ t ∧ t.card = 3 ∧ J.endpoint j b = t.centroid ℝ id) ∧
          ∀ v : D.axis.vertices, (v : D.sample → ℝ × V3) ∈ s →
            ∃ (swap : Bool) (eta : Fin 2 → Bool),
              (∀ j z, z ∈ J.disk → (J.coordinate j z = 0 ↔
                (C v).chart (D.inverse z) (jointSheetIndex swap j).castSucc = 0)) ∧
              ∀ j b z, z ∈ J.disk →
                (SignedJointCross.side b (J.coordinate j z) ↔
                  SignedJointCross.side (if eta j then b else !b)
                    ((C v).chart (D.inverse z) (jointSheetIndex swap j).castSucc)) := by
  classical
  let : Fintype D.complex.faces := D.complex_finite.fintype
  choose x y C hC hface haxis hsheet using
    fun v : D.axis.vertices => D.exists_marked_raw_star v v.property
  refine ⟨x, y, C, hC, hface, haxis, hsheet, ?_⟩
  intro s hs hcard
  obtain ⟨p, hp⟩ := D.axis.nonempty_of_mem_faces hs
  obtain ⟨x0, y0, C0, J, hC0, _, _, hJ, hrim, hcoord, hcenter, hcoface⟩ :=
    D.exists_signed_joint_cross hcore s hs hcard p hp
  have hcoface' (j : Fin 2) (b : Bool) : ∃ t : Finset (D.sample → ℝ × V3),
      t ∈ D.complex.faces ∧ s ⊆ t ∧ t.card = 3 ∧ J.endpoint j b = t.centroid ℝ id := by
    obtain ⟨t, ht, hst, htc, he⟩ := hcoface j b
    exact ⟨t, ht.1.1, hst, htc, he⟩
  refine ⟨J, hJ, hrim, hcenter, hcoface', ?_⟩
  intro v hv
  obtain ⟨swap, eta, hzero, _, hside⟩ := D.exists_incident_joint_transport hcore s hs hcard
    p v hp hv C0 (C v) hC0 (hC v) (hface v) (haxis v) (hsheet v) J hJ hcoord hcoface'
  exact ⟨swap, eta, hzero, hside⟩

end PoincareConjecture.M76.Dehn
