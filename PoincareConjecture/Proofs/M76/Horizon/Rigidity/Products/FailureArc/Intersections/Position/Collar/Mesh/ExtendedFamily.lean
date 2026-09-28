import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Collar.Mesh.PairMotion
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Collar.Mesh.SourceRefinement
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FiniteChartImageIntersection
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Collar.Composition.PatchExtension
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Collar.Mesh.ContactRetention

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76
local notation "E" => ((ℝ × ℝ) × ℝ)
local notation "V3" => (Fin 3 → ℝ)

theorem exists_original_local_coface_motion_family
    {D X ι : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
    [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {S T : Set X} {b : Bool}
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (K : SimplicialComplex ℝ D) (hK : K.faces.Finite)
    {g : D → X} (hg : PolyhedralPLInCharts e g K.space) (hgi : InjOn g K.space)
    (x : K.space) (C : OriginalSurfacePairChart e S T (g x) b)
    {U : Set X} (hU : IsOpen U) (hxU : g x ∈ U) :
    let Q := C.chart.trans C.coordinates
    ∃ (r : ℝ) (J : SimplicialComplex ℝ D) (O A W : Set X),
      0 < r ∧ J.faces.Finite ∧ J.IsSubdivision K ∧
      IsOpen O ∧ g x ∈ O ∧ O ⊆ U ∩ Q.source ∧
      IsCompact A ∧ A ⊆ O ∧ IsOpen W ∧ g x ∈ W ∧ W ⊆ O ∧
      A = Q.symm '' closedBall (0 : E) r ∧ W = O ∩ {y | ‖(Q y).1‖ < r} ∧
      ∀ (N : SimplicialComplex ℝ D), N.faces.Finite → N.IsSubdivision J →
      ∀ epsilon : ℝ, 0 < epsilon →
      ∃ (c : ℝ) (F : X ≃ₜ X), c ∈ Ioo (0 : ℝ) epsilon ∧
        EqOn F id Aᶜ ∧
        (∀ i j, (e i).symm.trans (F.toOpenPartialHomeomorph.trans (e j)) ∈
          piecewiseAffineGroupoid V3) ∧
        (∀ i j, (e i).symm.trans (F.symm.toOpenPartialHomeomorph.trans (e j)) ∈
          piecewiseAffineGroupoid V3) ∧
        F ⁻¹' T = T ∧
        (∀ z ∈ Q.target, Q.symm z ∈ F '' S ↔
          (CollarMesh.normalGraphCoordinates r c z).2 = 0 ∧ (b = true → 0 ≤ z.1.2)) ∧
        (∀ s ∈ N.faces, MapsTo g (convexHull ℝ (s : Set D)) O →
          ∃ B : D →ᴬ[ℝ] E,
            EqOn ((CollarMesh.normalGraphCoordinates r c) ∘ Q ∘ g) B
              (convexHull ℝ (s : Set D))) ∧
        Disjoint (F '' S) (g '' N.vertices ∩ W) ∧
        ((F '' S) \ S) ⊆ W ∧
        ∀ (R : Set X) (B : Set (ℝ × ℝ)),
          (∀ z ∈ C.coordinates.source,
            C.chart.symm z ∈ R ↔ (C.coordinates z).1 ∈ B) → F ⁻¹' R = R := by
  let Q := C.chart.trans C.coordinates
  have hxQ : g x ∈ Q.source := ⟨C.center_source, C.center_coordinates⟩
  have hQx : Q (g x) = 0 := C.center_zero
  have hQPL (i : ι) : LocallyPiecewiseAffineOn ((e i).symm.trans Q)
      ((e i).symm.trans Q).source := by
    have h := ((mem_piecewiseAffineGroupoid_iff V3 _).mp (C.compatible i)).1
    simpa only [Q, OpenPartialHomeomorph.coe_trans,
      OpenPartialHomeomorph.trans_source, preimage_inter, preimage_comp, inter_assoc,
      Function.comp_assoc] using C.forwardPL.comp h
  obtain ⟨f, O, hf, hO, hxO, hOU, hfg⟩ :=
    CollarMesh.exists_mixed_chart_extension_with_ambient_window K hK hg hgi Q hQPL x hxQ hU hxU
  have hzeroQ : (0 : E) ∈ Q.target := hQx ▸ Q.map_source hxQ
  have hQzero : Q.symm 0 = g x := by rw [← hQx, Q.left_inv hxQ]
  let V : Set E := Q.target ∩ Q.symm ⁻¹' O
  have hV : IsOpen V := Q.symm.isOpen_inter_preimage hO
  have hzeroV : (0 : E) ∈ V := ⟨hzeroQ, by change Q.symm 0 ∈ O; rw [hQzero]; exact hxO⟩
  obtain ⟨ε, hε, hεV⟩ := Metric.isOpen_iff.mp hV 0 hzeroV
  let r := ε / 2
  have hr : 0 < r := half_pos hε
  have hballV : closedBall (0 : E) r ⊆ V := by
    intro z hz
    exact hεV ((mem_closedBall.mp hz).trans_lt (half_lt_self hε))
  have hballQ := hballV.trans inter_subset_left
  obtain ⟨J, hJ, hJK, hfamily⟩ :=
    CollarMesh.exists_normal_graph_source_refinement_family K hK hf r
  let A := Q.symm '' closedBall (0 : E) r
  let W := O ∩ {y | ‖(Q y).1‖ < r}
  have hWO : W ⊆ O := inter_subset_left
  have hW : IsOpen W :=
    ((continuous_fst.comp_continuousOn (Q.continuousOn.mono (hOU.trans inter_subset_right))).norm).isOpen_inter_preimage hO isOpen_Iio
  have hxW : g x ∈ W := ⟨hxO, by change ‖(Q (g x)).1‖ < r; rw [hQx]; simpa using hr⟩
  refine ⟨r, J, O, A, W, hr, hJ, hJK, hO, hxO, hOU,
    (isCompact_closedBall _ _).image_of_continuousOn (Q.symm.continuousOn.mono hballQ),
    ?_, hW, hxW,
    hWO, rfl, rfl, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact (hballV hz).2
  · intro N hN hNJ epsilon hepsilon
    have hNK : N.space = K.space := hNJ.space_eq.trans hJK.space_eq
    obtain ⟨c, H, hc, hHPL, hval, hoff, _, _, hfaces, hvertices⟩ :=
      hfamily N hN hNJ epsilon hepsilon
    obtain ⟨F, _, hFoff, hFPL, hFinv, hFT, hS, hmarks⟩ :=
      C.exists_supported_normal_motion he H hHPL hval hoff hballQ
    refine ⟨c, F, hc, hFoff, hFPL, hFinv, hFT, hS, ?_, ?_, ?_, hmarks⟩
    · intro s hs hmap
      obtain ⟨B, hB⟩ := hfaces s hs
      refine ⟨B, ?_⟩
      intro z hz
      have heq := hfg z (hNK.subset (N.convexHull_subset_space hs hz)) (hmap hz)
      change CollarMesh.normalGraphCoordinates r c (Q (g z)) = B z
      rw [← heq]
      exact hB hz
    · apply disjoint_left.mpr
      rintro v hvS ⟨⟨z, hz, rfl⟩, hzW⟩
      have hzO := hWO hzW
      have hzQ := (hOU hzO).2
      have hfz := hfg z (hNK.subset (N.vertices_subset_space hz)) hzO
      have hvz := (hS (Q (g z)) (Q.map_source hzQ)).mp
        (by change Q.symm (Q (g z)) ∈ F '' S; rwa [Q.left_inv hzQ])
      have hplane : f z ∈ H '' {p : E | p.2 = 0} := by
        rw [hfz]
        exact (CollarMesh.normalGraphCoordinates_surface hval _).mpr hvz.1
      have hnorm : ‖(f z).1‖ < r := by
        rw [hfz]
        exact hzW.2
      exact disjoint_left.mp hvertices hplane ⟨⟨z, hz, rfl⟩, hnorm⟩
    · rintro v ⟨hvS, hvold⟩
      have hvA : v ∈ A := by
        by_contra hn
        obtain ⟨w, hw, hwv⟩ := hvS
        exact hvold (F.injective (hwv.trans (hFoff hn).symm) ▸ hw)
      obtain ⟨z, hz, rfl⟩ := hvA
      have hzQ := hballQ hz
      have hnew := (hS z hzQ).mp hvS
      have hplane : z ∈ H '' {p : E | p.2 = 0} :=
        (CollarMesh.normalGraphCoordinates_surface hval _).mpr hnew.1
      have hznot : z ∉ {p : E | p.2 = 0} := by
        intro hz0
        change z.2 = 0 at hz0
        apply hvold
        have hzC : z ∈ C.coordinates.target := hzQ.1
        change C.chart.symm (C.coordinates.symm z) ∈ S
        apply (C.first_surface _ (C.coordinates.map_target hzC)).mpr
        simpa only [C.coordinates.right_inv hzC] using And.intro hz0 hnew.2
      refine ⟨(hballV hz).2, ?_⟩
      change ‖(Q (Q.symm z)).1‖ < r
      rw [Q.right_inv hzQ]
      exact CollarMesh.normal_motion_new_contacts_active hval ⟨hplane, hznot⟩

end PoincareConjecture.M76
