import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.IncidentDiamondMaps
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Tubes.Joints.IncidentJoints



set_option autoImplicit false
open Set Metric Geometry Topology Geometry.SimplicialComplex

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)

open Classical in
theorem ComponentBranchModel.exists_incident_diamond_maps
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X] {S : Set E}
    {e : ι → OpenPartialHomeomorph X V3} {f : E → X} {R : Set X}
    {old : SourceCircleDecomposition f S} {i : old.Index}
    (D : ComponentBranchModel (e := e) (R := R) old i) (hcore : D.core ⊆ interior R) :
    letI : Fintype D.complex.faces := D.complex_finite.fintype
    ∃ (x y : D.axis.vertices → E) (C : ∀ v, RawSourceCrossing e f S R (x v) (y v)),
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
        ∃ G : signedTubeDiamond ≃ₜ (D.complex.barycentricDualBlock s).space,
          G.IsFinitePL ∧
          (G ⟨(0, 0), mem_iUnion.mpr ⟨false, mem_iUnion.mpr ⟨false, signedTube_center_mem⟩⟩⟩ :
            D.sample → ℝ × V3) = s.centroid ℝ id ∧
          (∀ j b, ∃ t : Finset (D.sample → ℝ × V3),
            t ∈ D.complex.faces ∧ s ⊆ t ∧ t.card = 3 ∧
              (G ⟨signedTubeCorner j b,
                signedTubeRadius_subset_diamond j b (right_mem_segment ℝ _ _)⟩ :
                  D.sample → ℝ × V3) = t.centroid ℝ id) ∧
          ∀ v : D.axis.vertices, (v : D.sample → ℝ × V3) ∈ s →
            ∃ a : SignedAxisPermutation,
              (a.symm.diamond.trans G).IsFinitePL ∧
              ∀ j b (z : signedTubeDiamond),
                SignedJointCross.side b (SignedAxisPermutation.coordinate j z) ↔
                  SignedJointCross.side b
                    ((C v).chart (D.inverse (G (a.symm.diamond z))) j.castSucc) := by
  classical
  let : Fintype D.complex.faces := D.complex_finite.fintype
  obtain ⟨x, y, C, hC, hface, haxis, hsheet, hJ⟩ := D.exists_incident_joints hcore
  refine ⟨x, y, C, hC, hface, haxis, hsheet, ?_⟩
  intro s hs hcard
  obtain ⟨J, hJs, _, hcenter, hcoface, hinc⟩ := hJ s hs hcard
  obtain ⟨G, hG, hside, _, hGc, hGe⟩ := J.exists_diamond_map_with_sides
  let G' := G.trans (Homeomorph.setCongr hJs)
  have hG' : G'.IsFinitePL := by
    obtain ⟨g, hg, hgv⟩ := hG
    exact ⟨g, hg, hgv⟩
  refine ⟨G', hG', hGc.trans hcenter, ?_, ?_⟩
  · intro j b
    obtain ⟨t, ht, hst, htc, he⟩ := hcoface j b
    exact ⟨t, ht, hst, htc, (hGe j b).trans he⟩
  · intro v hv
    obtain ⟨swap, eta, _, htrans⟩ := hinc v hv
    let a : SignedAxisPermutation := ⟨swap, eta⟩
    refine ⟨a, (a.symm.diamond_isFinitePL hG').trans hG', ?_⟩
    exact J.incident_diamond_sides G hside a
      (fun j z ↦ (C v).chart (D.inverse z) j.castSucc) htrans

end PoincareConjecture.M76.Dehn.Annuli
