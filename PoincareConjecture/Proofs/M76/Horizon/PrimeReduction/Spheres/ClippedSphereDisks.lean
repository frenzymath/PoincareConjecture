import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.ClippedSphereParameter
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.SmallSphereDisk










set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "V2" => (Fin 2 → ℝ)




theorem ChartwisePLSphere.exists_clipped_disk_neighborhood
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {S : Set X}
    (s : ChartwisePLSphere e S) (Q : OpenPartialHomeomorph X V3)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (J P : SimplicialComplex ℝ V3) (hJ : J.faces.Finite)
    (hJQ : J.space ⊆ Q.target) (hP : P.faces.Finite)
    (hPs : P.space = Q '' (S ∩ Q.source) ∩ J.space)
    {w : V3} (hw : w ∈ P.space) (hwJ : w ∈ interior J.space) :
    ∃ d q : Set V3, IsFinitePLBallPair V2 d q ∧ d ⊆ P.space ∧
      w ∈ d \ q ∧ IsOpen ((Subtype.val : P.space → V3) ⁻¹' (d \ q)) := by
  obtain ⟨g, hg, hgS, hgi, hright, hleft, himage⟩ :=
    s.exists_finite_clipped_parameter Q hQ J P hJ hJQ hP hPs
  obtain ⟨H, hH, hHval⟩ := hg.exists_homeomorph_image hgi
  let O : Set (sphere (0 : V3) 1) :=
    (fun x => s.map x) ⁻¹' (Q.source ∩ Q ⁻¹' interior J.space)
  have hO : IsOpen O := (Q.isOpen_inter_preimage isOpen_interior).preimage
    s.piecewiseAffine.continuousOn.domRestrict
  have hgwO : (⟨g w, hgS hw⟩ : sphere (0 : V3) 1) ∈ O := by
    change s.map (g w) ∈ Q.source ∧ Q (s.map (g w)) ∈ interior J.space
    rw [hright w hw]
    exact ⟨Q.map_target (hJQ (interior_subset hwJ)),
      (Q.right_inv (hJQ (interior_subset hwJ))).symm ▸ hwJ⟩
  obtain ⟨U, hU, hUeq⟩ := isOpen_induced_iff.mp hO
  have hgwU : g w ∈ U := (Set.ext_iff.mp hUeq ⟨g w, hgS hw⟩).mpr hgwO
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨B, hB, hBs, _⟩, _⟩, _⟩ :=
    (isFinitePLBallPair_unit_cube : IsFinitePLBallPair V3
      (closedBall (0 : V3) 1) (sphere (0 : V3) 1))
  let K := B.frontierSubcomplex (closedBall (0 : V3) 1)
  have hK : K.faces.Finite := B.frontierSubcomplex_finite _ hB
  have hKs : K.space = sphere (0 : V3) 1 := by
    rw [B.frontierSubcomplex_space isClosed_closedBall (convex_closedBall _ _)
      ⟨0, ball_subset_interior_closedBall (mem_ball_self zero_lt_one)⟩ hBs,
      frontier_closedBall _ one_ne_zero]
  let C := closedBall (0 : V3) 1
  let F : sphere (0 : V3) 1 ≃ₜ frontier C :=
    Homeomorph.setCongr (frontier_closedBall (0 : V3) one_ne_zero).symm
  have hF : F.IsFinitePL :=
    ⟨id, ⟨K, hK, hKs, K.affineOnFaces_affine (ContinuousAffineMap.id ℝ V3)⟩,
      fun _ => rfl⟩
  obtain ⟨D, R, hD, hDU, hgwD, hopen⟩ :=
    hF.exists_small_local_ball_pairs_of_convex_frontier (isCompact_closedBall _ _)
      (convex_closedBall _ _) ⟨0, ball_subset_interior_closedBall
        (mem_ball_self zero_lt_one)⟩ (V := V2) (by simp)
      ⟨g w, hgS hw⟩ hU hgwU
  have hDimage : D ⊆ g '' P.space := by
    intro x hx
    obtain ⟨hxS, hxU⟩ := hDU hx
    have hxO : (⟨x, hxS⟩ : sphere (0 : V3) 1) ∈ O :=
      (Set.ext_iff.mp hUeq ⟨x, hxS⟩).mp hxU
    exact himage.symm.subset ⟨hxS, hxO.1, interior_subset hxO.2⟩
  let d := P.space ∩ g ⁻¹' D
  let q := P.space ∩ g ⁻¹' R
  have hball : IsFinitePLBallPair V2 d q := hH.preimage_ballPair hD hDimage hHval
  refine ⟨d, q, hball, inter_subset_left, ⟨⟨hw, hgwD.1⟩, fun h => hgwD.2 h.2⟩, ?_⟩
  let gS : P.space → sphere (0 : V3) 1 := fun x => ⟨g x, hgS x.property⟩
  have hgScont : Continuous gS := hg.continuousOn.domRestrict.subtype_mk _
  have heq : (Subtype.val : P.space → V3) ⁻¹' (d \ q) =
      gS ⁻¹' ((Subtype.val : sphere (0 : V3) 1 → V3) ⁻¹' (D \ R)) := by
    ext x
    simp only [d, q, gS, mem_preimage, mem_sdiff, mem_inter_iff, x.property, true_and]
  rw [heq]
  exact hopen.preimage hgScont

end PoincareConjecture.M76
