import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.JointCoordinateMaps
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.OriginalIncidentJoints
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleArc.SignedCoordinateSectors









set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)

theorem signed_diamond_quarters_of_coordinate_sides
    {E : Type*} [TopologicalSpace E] {T : Set E}
    (G : signedTubeDiamond ≃ₜ T) (ell : Fin 2 → E → ℝ)
    (hside : ∀ j b (x : signedTubeDiamond),
      SignedJointCross.side b (SignedAxisPermutation.coordinate j x) ↔
        SignedJointCross.side b (ell j (G x))) :
    ∀ b c (x : signedTubeDiamond),
      (x : P2) ∈ signedTubeQuarter b c ↔
        (G x : E) ∈ signedCoordinateSector T ell (fun _ ↦ true) b c := by
  intro b c x
  rw [signedTubeQuarter_side_iff]
  change _ ↔ (G x : E) ∈ T ∧
    SignedJointCross.side b (ell 0 (G x)) ∧ SignedJointCross.side c (ell 1 (G x))
  rw [and_iff_right (G x).property]
  exact (hside 0 b x).and (hside 1 c x)

theorem SignedJointCross.incident_diamond_sides
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (J : SignedJointCross E) (G : signedTubeDiamond ≃ₜ J.disk)
    (hG : ∀ j b (x : signedTubeDiamond),
      SignedJointCross.side b (SignedAxisPermutation.coordinate j x) ↔
        SignedJointCross.side b (J.coordinate j (G x)))
    (a : SignedAxisPermutation) (ell : Fin 2 → E → ℝ)
    (htrans : ∀ j b, ∀ z ∈ J.disk,
      SignedJointCross.side b (J.coordinate j z) ↔
        SignedJointCross.side (if a.sign j then b else !b) (ell (a.index j) z)) :
    ∀ j b (x : signedTubeDiamond),
      SignedJointCross.side b (SignedAxisPermutation.coordinate j x) ↔
        SignedJointCross.side b (ell j (G (a.symm.diamond x))) := by
  intro j b x
  have hii : a.index (a.index j) = j := by
    cases hs : a.swap <;> fin_cases j <;> simp [SignedAxisPermutation.index, jointSheetIndex, hs]
  let c := signedTubeReindex (a.sign (a.index j)) b
  have hc : signedTubeReindex (a.sign (a.index j)) c = b := by
    dsimp [c]
    cases a.sign (a.index j) <;> cases b <;> rfl
  have hlinear := a.side_iff (a.index j) c (a.symm.linear x)
  rw [a.linear_apply_symm, hii, hc] at hlinear
  have htarget := htrans (a.index j) c (G (a.symm.diamond x))
    (G (a.symm.diamond x)).property
  change SignedJointCross.side c (J.coordinate (a.index j) (G (a.symm.diamond x))) ↔
    SignedJointCross.side (signedTubeReindex (a.sign (a.index j)) c)
      (ell (a.index (a.index j)) (G (a.symm.diamond x))) at htarget
  rw [hii, hc] at htarget
  exact hlinear.symm.trans ((hG (a.index j) c (a.symm.diamond x)).trans htarget)

open Classical in
theorem ComponentBranchModel.exists_incident_diamond_maps
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

end PoincareConjecture.M76.Dehn
