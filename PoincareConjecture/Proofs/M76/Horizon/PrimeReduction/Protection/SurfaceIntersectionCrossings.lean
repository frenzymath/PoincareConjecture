import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.SurfaceIntersectionDegree
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Coordinates.FaceGraphCrossing
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Affine.RelativeInteriorHeightSigns
import PoincareConjecture.Proofs.M76.Mathlib.ConvexPolyhedralNeighborhood








set_option autoImplicit false
open Set Geometry Filter Module
open scoped Topology
namespace Geometry.SimplicialComplex
local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)

theorem exists_surface_crossing_of_transverse_triangle
    (P T : SimplicialComplex ℝ V3) (hP : P.faces.Finite) (hT : T.faces.Finite)
    (hPc : ∀ a ∈ P.faces, a.card ≤ 3) (hTc : ∀ t ∈ T.faces, t.card ≤ 3)
    {a t : Finset V3} (ha : a ∈ P.faces) (ht : t ∈ T.faces) (ht3 : t.card = 3)
    {w : V3} (hwa : w ∈ intrinsicInterior ℝ (convexHull ℝ (a : Set V3)))
    (hwt : w ∈ intrinsicInterior ℝ (convexHull ℝ (t : Set V3)))
    (hspan : affineSpan ℝ ((a : Set V3) ∪ (t : Set V3)) = ⊤)
    (hdisk : ∃ d q : Set V3, IsFinitePLBallPair (Fin 2 → ℝ) d q ∧ d ⊆ P.space ∧
      w ∈ d \ q ∧ IsOpen ((Subtype.val : P.space → V3) ⁻¹' (d \ q)))
    {O : Set V3} (hO : IsOpen O) (hwO : w ∈ O) :
    ∃ B : OpenPartialHomeomorph V3 C3,
      w ∈ B.source ∧ B.source ⊆ O ∧ B w = 0 ∧
      LocallyPiecewiseAffineOn B B.source ∧
      LocallyPiecewiseAffineOn B.symm B.target ∧
      (∀ x ∈ B.source, x ∈ P.space ↔ (B x).2 = 0) ∧
      ∀ x ∈ B.source, x ∈ T.space ↔ (B x).1.1 = 0 := by
  classical
  let V := affineSpan ℝ (t : Set V3)
  have hVdim : finrank ℝ V.direction = 2 := T.finrank_faceDirection_of_card ht ht3
  have hwV : w ∈ V := convexHull_subset_affineSpan _ (intrinsicInterior_subset hwt)
  have hVtop : V ≠ ⊤ := by
    intro hh
    rw [hh,AffineSubspace.direction_top,finrank_top] at hVdim
    norm_num at hVdim
  obtain ⟨A,_,hAV⟩ := V.exists_defining_height_of_finrank_two (by simp) hVdim ⟨w,hwV⟩
  have hAz : A w = 0 := (hAV w).mpr hwV
  have hnonzero : ∃ v ∈ a, A v ≠ 0 := V.exists_nonzero_height_vertex_of_span_union_eq_top
    hVtop A hAV (subset_affineSpan ℝ _) hspan
  obtain ⟨u,v,hu,hv,hint,hgerm⟩ := P.exists_two_segment_section_of_transverse_face
    hP hPc ha hwa A hAz hnonzero hdisk
  have hsign := Set.mem_both_height_closures_of_intrinsicInterior_convexHull a A hwa hAz hnonzero
  have hneg : w ∈ closure (P.space ∩ {x | A x < 0}) :=
    closure_mono (inter_subset_inter_left _ (P.convexHull_subset_space ha)) hsign.1
  have hpos : w ∈ closure (P.space ∩ {x | 0 < A x}) :=
    closure_mono (inter_subset_inter_left _ (P.convexHull_subset_space ha)) hsign.2
  obtain ⟨U,hU,hwU,hTU⟩ := T.exists_open_eq_affineSpan_of_triangle_interior hT hTc ht ht3 hwt
  obtain ⟨J,hJ,_,hPJ⟩ := (P.isCompact_space_of_finite hP).exists_finite_convex_neighborhood
  have hwP := P.convexHull_subset_space ha (intrinsicInterior_subset hwa)
  obtain ⟨K,L,hK,_,_,hLK,_,hLP,_,_,hwL,hwK,hLc,_⟩ :=
    J.exists_marked_full_surface_refinement P hJ hP (hPJ.trans interior_subset) hPc hwP (hPJ hwP)
  obtain ⟨d,q,hd,hdP,hwd,hopen⟩ := hdisk
  have hopenL : IsOpen ((Subtype.val : L.space → V3) ⁻¹' (d \ q)) := by
    obtain ⟨W,hW,hWpre⟩ := isOpen_induced_iff.mp hopen
    apply isOpen_induced_iff.mpr
    refine ⟨W,hW,?_⟩
    ext x
    exact Set.ext_iff.mp hWpre ⟨x,hLP.subset x.property⟩
  obtain ⟨B,hwB,hBO,hBw,hB,hBi,hBP,hBA,_⟩ :=
    K.exists_affine_vertex_crossing_chart_of_local_disk L hK hLK hLc hwL hwK hd
      (hdP.trans hLP.symm.subset) hwd hopenL A hu hv hint.subset
      (by simpa only [hLP] using hgerm)
      (by simpa only [hLP] using hneg) (by simpa only [hLP] using hpos)
      (hO.inter hU) ⟨hwO,hwU⟩
  refine ⟨B,hwB,fun x hx => (hBO hx).1,hBw,hB,hBi,?_,?_⟩
  · simpa only [hLP] using hBP
  · intro x hx
    have hTx : x ∈ T.space ↔ x ∈ V :=
      ⟨fun h => (hTU.subset ⟨h,(hBO hx).2⟩).1,
        fun h => (hTU.symm.subset ⟨h,(hBO hx).2⟩).1⟩
    exact hTx.trans ((hAV x).symm.trans (hBA x hx))

private noncomputable def swapCrossingCoordinates : C3 ≃ᴬ[ℝ] C3 :=
  let L : C3 ≃ₗ[ℝ] C3 :=
    { toFun := fun z => ((z.2,z.1.2),z.1.1)
      invFun := fun z => ((z.2,z.1.2),z.1.1)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  L.toContinuousLinearEquiv.toContinuousAffineEquiv

theorem exists_swapped_crossing_chart
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (B : OpenPartialHomeomorph E C3) {w : E} (hwB : w ∈ B.source) (hBw : B w = 0)
    (hB : LocallyPiecewiseAffineOn B B.source)
    (hBi : LocallyPiecewiseAffineOn B.symm B.target)
    {S T : Set E}
    (hS : ∀ x ∈ B.source, x ∈ S ↔ (B x).2 = 0)
    (hT : ∀ x ∈ B.source, x ∈ T ↔ (B x).1.1 = 0) :
    ∃ C : OpenPartialHomeomorph E C3,
      C.source = B.source ∧ w ∈ C.source ∧ C w = 0 ∧
      LocallyPiecewiseAffineOn C C.source ∧ LocallyPiecewiseAffineOn C.symm C.target ∧
      (∀ x ∈ C.source, x ∈ T ↔ (C x).2 = 0) ∧
      ∀ x ∈ C.source, x ∈ S ↔ (C x).1.1 = 0 := by
  let A := swapCrossingCoordinates
  let C := B.trans A.toHomeomorph.toOpenPartialHomeomorph
  have hCs : C.source = B.source := by
    change B.source ∩ B ⁻¹' univ = B.source
    simp
  refine ⟨C,hCs,hCs.symm ▸ hwB,?_,?_,?_,?_,?_⟩
  · change A (B w) = 0
    rw [hBw]
    rfl
  · exact (locallyPiecewiseAffineOn_affine A.toContinuousAffineMap isOpen_univ).comp hB
  · exact hBi.comp (locallyPiecewiseAffineOn_affine A.symm.toContinuousAffineMap isOpen_univ)
  · intro x hx
    exact hT x (hCs.subset hx)
  · intro x hx
    exact hS x (hCs.subset hx)

theorem exists_surface_crossing_chart_of_position
    (P T : SimplicialComplex ℝ V3) (hP : P.faces.Finite) (hT : T.faces.Finite)
    (hPc : ∀ a ∈ P.faces, a.card ≤ 3) (hTc : ∀ t ∈ T.faces, t.card ≤ 3)
    {Z : Set V3} (hZ : Disjoint Z T.space)
    (hposition : ∀ a ∈ P.faces, convexHull ℝ (a : Set V3) ⊆ Z ∨
      ∀ t ∈ T.faces, affineSpan ℝ ((a : Set V3) ∪ (t : Set V3)) = ⊤ ∨
        Disjoint (intrinsicInterior ℝ (convexHull ℝ (a : Set V3)))
          (convexHull ℝ (t : Set V3)))
    {w : V3} (hw : w ∈ P.space ∩ T.space)
    (hdiskP : ∃ d q : Set V3, IsFinitePLBallPair (Fin 2 → ℝ) d q ∧ d ⊆ P.space ∧
      w ∈ d \ q ∧ IsOpen ((Subtype.val : P.space → V3) ⁻¹' (d \ q)))
    (hdiskT : ∃ d q : Set V3, IsFinitePLBallPair (Fin 2 → ℝ) d q ∧ d ⊆ T.space ∧
      w ∈ d \ q ∧ IsOpen ((Subtype.val : T.space → V3) ⁻¹' (d \ q)))
    {O : Set V3} (hO : IsOpen O) (hwO : w ∈ O) :
    ∃ B : OpenPartialHomeomorph V3 C3,
      w ∈ B.source ∧ B.source ⊆ O ∧ B w = 0 ∧
      LocallyPiecewiseAffineOn B B.source ∧
      LocallyPiecewiseAffineOn B.symm B.target ∧
      (∀ x ∈ B.source, x ∈ P.space ↔ (B x).2 = 0) ∧
      ∀ x ∈ B.source, x ∈ T.space ↔ (B x).1.1 = 0 := by
  obtain ⟨a,ha,hwa⟩ := P.exists_face_intrinsicInterior_of_finite hP hw.1
  obtain ⟨t,ht,hwt⟩ := T.exists_face_intrinsicInterior_of_finite hT hw.2
  have hspan : affineSpan ℝ ((a : Set V3) ∪ (t : Set V3)) = ⊤ := by
    rcases hposition a ha with hp | hp
    · exact False.elim (disjoint_left.mp hZ (hp (intrinsicInterior_subset hwa)) hw.2)
    rcases hp t ht with hp | hd
    · exact hp
    · exact False.elim (disjoint_left.mp hd hwa (intrinsicInterior_subset hwt))
  have hthree : a.card = 3 ∨ t.card = 3 := by
    by_contra hn
    have hac : a.card ≤ 2 := by have := hPc a ha; omega
    have htc : t.card ≤ 2 := by have := hTc t ht; omega
    have hjoin : affineSpan ℝ (a : Set V3) ⊔ affineSpan ℝ (t : Set V3) = ⊤ := by
      rw [←AffineSubspace.span_union]
      exact hspan
    have hrank := (affineSpan ℝ (a : Set V3)).finrank_inf_add_ambient_of_mem_of_sup_top
      (affineSpan ℝ (t : Set V3))
      (convexHull_subset_affineSpan _ (intrinsicInterior_subset hwa))
      (convexHull_subset_affineSpan _ (intrinsicInterior_subset hwt)) hjoin
    have ha1 := finrank_affineSpan_finset_le (P.nonempty_of_mem_faces ha) (d:=1) hac
    have ht1 := finrank_affineSpan_finset_le (T.nonempty_of_mem_faces ht) (d:=1) htc
    have hdim : finrank ℝ V3 = 3 := by simp
    omega
  rcases hthree with ha3 | ht3
  · obtain ⟨B,hwB,hBO,hBw,hB,hBi,hBT,hBP⟩ :=
      T.exists_surface_crossing_of_transverse_triangle P hT hP hTc hPc ht ha ha3 hwt hwa
        (by simpa only [union_comm] using hspan) hdiskT hO hwO
    obtain ⟨C,hCs,hwC,hCw,hC,hCi,hCP,hCT⟩ :=
      exists_swapped_crossing_chart B hwB hBw hB hBi hBT hBP
    exact ⟨C,hwC,hCs.subset.trans hBO,hCw,hC,hCi,hCP,hCT⟩
  · exact P.exists_surface_crossing_of_transverse_triangle T hP hT hPc hTc ha ht ht3
      hwa hwt hspan hdiskP hO hwO

end Geometry.SimplicialComplex
