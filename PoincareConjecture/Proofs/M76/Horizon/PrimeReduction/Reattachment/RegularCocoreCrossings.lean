import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.ClippedSphereEdgeIncidence
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.RegularCocoreSection
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Coordinates.LocalDiskEdgeCrossing
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.TriangleInteriorCrossingChart

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)
local notation "P3" => ((ℝ × ℝ) × ℝ)

private noncomputable def swapCocoreCoordinates : P3 ≃ᴬ[ℝ] P3 :=
  let L : P3 ≃ₗ[ℝ] P3 :=
    { toFun := fun z => ((z.2,z.1.2),z.1.1)
      invFun := fun z => ((z.2,z.1.2),z.1.1)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  L.toContinuousLinearEquiv.toContinuousAffineEquiv

theorem ChartwisePLSphere.exists_regular_cocore_crossing_chart
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {S : Set X}
    (s : ChartwisePLSphere e S) (Q : OpenPartialHomeomorph X V3)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (J P : SimplicialComplex ℝ V3) (hJ : J.faces.Finite)
    (hJQ : J.space ⊆ Q.target) (hP : P.faces.Finite)
    (hPs : P.space = Q '' (S ∩ Q.source) ∩ J.space)
    (A : V3 →ᵃ[ℝ] ℝ) (hreg : ∀ v ∈ P.vertices, A v ≠ 0)
    {w : V3} (hwP : w ∈ P.space) (hwJ : w ∈ interior J.space) (hwA : A w = 0)
    {O : Set V3} (hO : IsOpen O) (hwO : w ∈ O) :
    ∃ B : OpenPartialHomeomorph V3 P3,
      w ∈ B.source ∧ B.source ⊆ O ∩ interior J.space ∧ B w = 0 ∧
      LocallyPiecewiseAffineOn B B.source ∧
      LocallyPiecewiseAffineOn B.symm B.target ∧
      (∀ x ∈ B.source, Q.symm x ∈ S ↔ (B x).2 = 0) ∧
      ∀ x ∈ B.source, A x = (B x).1.1 := by
  classical
  have hbound : ∀ a ∈ P.faces, a.card ≤ 3 :=
    fun a ha => s.clipped_face_card_le_three Q hQ J P hJ hJQ hPs ha
  have hphysical (x : V3) (hx : x ∈ interior J.space) :
      Q.symm x ∈ S ↔ x ∈ P.space := by
    rw [hPs]
    have hxQ := hJQ (interior_subset hx)
    constructor
    · intro h
      exact ⟨⟨Q.symm x,⟨h,Q.map_target hxQ⟩,Q.right_inv hxQ⟩,interior_subset hx⟩
    · rintro ⟨⟨y,⟨hy,hyQ⟩,hxy⟩,_⟩
      rw [← hxy,Q.left_inv hyQ]
      exact hy
  obtain ⟨a,ha,hwa⟩ := P.exists_face_intrinsicInterior_of_finite hP hwP
  have hapos := Finset.card_pos.mpr (P.nonempty_of_mem_faces ha)
  have hahi := hbound a ha
  have hane : a.card ≠ 1 := by
    intro h
    obtain ⟨v,rfl⟩ := Finset.card_eq_one.mp h
    have hwv : w = v := by
      simpa only [Finset.coe_singleton,convexHull_singleton,mem_singleton_iff] using
        intrinsicInterior_subset hwa
    exact hreg v ha (hwv ▸ hwA)
  obtain ⟨v,hv⟩ := P.nonempty_of_mem_faces ha
  have hvA := hreg v (P.face_subset_vertices ha hv)
  by_cases ha2 : a.card = 2
  · obtain ⟨d,r,hd,hdP,hwd,hopen⟩ :=
      s.exists_clipped_disk_neighborhood Q hQ J P hJ hJQ hP hPs hwP hwJ
    obtain ⟨B,hwB,hBO,hBw,hB,hBi,hBP,hBA⟩ :=
      P.exists_transverse_edge_crossing_chart_of_local_disk hP hbound ha ha2 A hwa hwA
        ⟨v,hv,hvA⟩ hd hdP hwd hopen (hO.inter isOpen_interior) ⟨hwO,hwJ⟩
    let E := swapCocoreCoordinates
    let G := B.trans E.toHomeomorph.toOpenPartialHomeomorph
    have hsource : G.source = B.source := by
      change B.source ∩ B ⁻¹' univ = B.source
      simp
    refine ⟨G,hsource.symm.subset hwB,hsource.subset.trans hBO,?_,?_,?_,?_,?_⟩
    · change E (B w) = 0
      rw [hBw]
      rfl
    · exact (locallyPiecewiseAffineOn_affine E.toContinuousAffineMap isOpen_univ).comp hB
    · exact hBi.comp (locallyPiecewiseAffineOn_affine E.symm.toContinuousAffineMap isOpen_univ)
    · intro x hx
      exact (hphysical x (hBO (hsource.subset hx)).2).trans (hBP x (hsource.subset hx))
    · intro x hx
      exact hBA x (hsource.subset hx)
  · have ha3 : a.card = 3 := by omega
    have hmax : ∀ b ∈ P.faces, a ⊆ b → b = a := by
      intro b hb hab
      exact (Finset.eq_of_subset_of_card_le hab (by have := hbound b hb; omega)).symm
    obtain ⟨U,hU,hwU,hPU⟩ := P.exists_open_maximal_face_affine_germ hP ha hmax hwa
    have hwplane : w ∈ affineSpan ℝ (a : Set V3) :=
      convexHull_subset_affineSpan (s := (a : Set V3)) (intrinsicInterior_subset hwa)
    have hvplane : v ∈ affineSpan ℝ (a : Set V3) := subset_affineSpan ℝ _ hv
    obtain ⟨F,hFzero,hFA,hFP⟩ := (affineSpan ℝ (a : Set V3)).exists_centered_height_plane_coordinates
      (by simp) (P.finrank_faceDirection_of_card ha ha3) A
      ⟨v,hvplane,w,hwplane,by simpa only [hwA] using hvA⟩ hwplane
    let V := (O ∩ interior J.space) ∩ U
    let B := F.symm.toHomeomorph.toOpenPartialHomeomorphOfImageEq V
      ((hO.inter isOpen_interior).inter hU) (F.symm '' V) rfl
    refine ⟨B,⟨⟨hwO,hwJ⟩,hwU⟩,inter_subset_left,?_,?_,?_,?_,?_⟩
    · change F.symm w = 0
      rw [← hFzero,F.symm_apply_apply]
    · exact locallyPiecewiseAffineOn_affine F.symm.toContinuousAffineMap B.open_source
    · exact locallyPiecewiseAffineOn_affine F.toContinuousAffineMap B.open_target
    · intro x hx
      have h := hFP (F.symm x)
      rw [F.apply_symm_apply] at h
      exact (hphysical x hx.1.2).trans ((hPU x hx.2).trans h)
    · intro x _
      change A x = (F.symm x).1.1
      have h := hFA (F.symm x)
      simpa only [F.apply_symm_apply,hwA,zero_add] using h

theorem ChartwisePLSphere.exists_regular_cocore_section_with_crossings
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {S : Set X}
    (s : ChartwisePLSphere e S) (Q : OpenPartialHomeomorph X V3)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (J : SimplicialComplex ℝ V3) (hJ : J.faces.Finite) (hJQ : J.space ⊆ Q.target)
    (A : V3 →ᵃ[ℝ] ℝ) {a b : ℝ} (hab : a < b)
    (hband : ∀ x ∈ Q '' (S ∩ Q.source) ∩ J.space,
      A x ∈ Ioo a b → x ∈ interior J.space) :
    ∃ t ∈ Ioo a b,
      HasDisjointPolygonPresentation ((Q '' (S ∩ Q.source) ∩ J.space) ∩ {x | A x = t}) ∧
      ∀ w ∈ (Q '' (S ∩ Q.source) ∩ J.space) ∩ {x | A x = t},
        ∀ O : Set V3, IsOpen O → w ∈ O →
        ∃ B : OpenPartialHomeomorph V3 P3,
          w ∈ B.source ∧ B.source ⊆ O ∩ interior J.space ∧ B w = 0 ∧
          LocallyPiecewiseAffineOn B B.source ∧
          LocallyPiecewiseAffineOn B.symm B.target ∧
          (∀ x ∈ B.source, Q.symm x ∈ S ↔ (B x).2 = 0) ∧
          ∀ x ∈ B.source, A x - t = (B x).1.1 := by
  obtain ⟨P,hP,hPs,t,ht,hreg,hsection⟩ :=
    s.exists_regular_cocore_section_with_carrier Q hQ J hJ hJQ A hab hband
  let height : V3 →ᵃ[ℝ] ℝ := A - AffineMap.const ℝ V3 t
  have hregular : ∀ v ∈ P.vertices, height v ≠ 0 := by
    intro v hv h
    exact hreg v hv (sub_eq_zero.mp h)
  refine ⟨t,ht,hsection,?_⟩
  intro w hw O hO hwO
  exact s.exists_regular_cocore_crossing_chart Q hQ J P hJ hJQ hP hPs height hregular
    (hPs.symm.subset hw.1) (hband w hw.1 (hw.2 ▸ ht)) (sub_eq_zero.mpr hw.2) hO hwO

end PoincareConjecture.M76
