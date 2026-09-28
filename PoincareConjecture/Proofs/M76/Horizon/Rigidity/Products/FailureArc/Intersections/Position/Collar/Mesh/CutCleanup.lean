import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Collar.Composition.FiniteCut
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Collar.Mesh.RegionTransport

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem exists_original_collar_vertex_cut_position
    {D X ι : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
    [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {S T R U W : Set X}
    (hcover : ∀ y, ∃ i, y ∈ (e i).source)
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (K : SimplicialComplex ℝ D) (hK : K.faces.Finite)
    {g : D → X} (hg : PolyhedralPLInCharts e g K.space) (hgi : InjOn g K.space)
    (hT : g '' K.space ⊆ T)
    (P Q : Set D) (hP : IsClosed P) (hPK : P ⊆ K.space) (hQK : Q ⊆ K.space)
    (hfinite : (P ∩ g ⁻¹' S).Finite)
    (hcut : ∀ x ∈ P, g x ∈ S → Nonempty (OriginalSurfacePairChart e S T (g x) false))
    (hU : IsOpen U) (hUR : U ⊆ interior R) (hPU : g '' (P ∩ g ⁻¹' S) ⊆ U)
    (hW : IsOpen W) (hQW : g '' Q ⊆ W)
    (hcharts : ∀ y ∈ S, y ∈ T → y ∈ U ∪ g '' Q →
      (y ∈ interior R ∧ Nonempty (OriginalSurfacePairChart e S T y false)) ∨
      ∃ C : OriginalSurfacePairChart e S T y true,
        ∀ z ∈ C.coordinates.source, C.chart.symm z ∈ R ↔ 0 ≤ (C.coordinates z).1.2) :
    ∃ (N : SimplicialComplex ℝ D) (H : X ≃ₜ X) (B : Set X),
      N.faces.Finite ∧ N.IsSubdivision K ∧ IsCompact B ∧ B ⊆ U ∪ W ∧ EqOn H id Bᶜ ∧
      (∀ i j, (e i).symm.trans (H.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      (∀ i j, (e i).symm.trans (H.symm.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧ H ⁻¹' T = T ∧ H ⁻¹' R = R ∧
      Disjoint (H '' S) (g '' (N.vertices ∩ Q)) ∧
      ∀ a ∈ N.faces, a.card = 2 → convexHull ℝ (a : Set D) ⊆ P →
        (H '' S ∩ (g '' convexHull ℝ (a : Set D))).Finite ∧
          HasOriginalEdgeCofaceCharts e (H '' S) N g a := by
  classical
  obtain ⟨N, F, A, hN, hNK, hA, hAU, hFoff, hFPL, hFinv, hFT, hFV, hedges⟩ :=
    exists_original_finite_cut_coface_position hcover he K hK hg hgi P hPK hfinite hcut hU hPU
  have hFR : F ⁻¹' R = R :=
    F.injective.preimage_eq_self_of_eqOn_compl
      (fun y hy => hFoff (fun h => hy (interior_subset (hUR (hAU h)))))
  have hcompactP : IsCompact P := (K.isCompact_space_of_finite hK).of_isClosed_subset hP hPK
  have hclosedP : IsClosed (g '' P) :=
    (hcompactP.image_of_continuousOn (hg.continuousOn.mono hPK)).isClosed
  have hfiniteV := ((N.finite_vertices_of_finite_faces hN).inter_of_left Q).image g
  let V := hfiniteV.toFinset
  have hV : (V : Set X) = g '' (N.vertices ∩ Q) := hfiniteV.coe_toFinset
  have hVW : (V : Set X) ⊆ W ∪ g '' P := by
    rw [hV]
    exact (image_mono inter_subset_right).trans (hQW.trans subset_union_left)
  have hprotected : Disjoint (F '' S) ((V : Set X) ∩ g '' P) := by
    apply hFV.mono_right
    rw [hV]
    exact inter_subset_inter_left _ (image_mono inter_subset_left)
  have hcurrent : ∀ p ∈ V, p ∉ g '' P → p ∈ F '' S →
      (p ∈ interior R ∧ Nonempty (OriginalSurfacePairChart e (F '' S) T p false)) ∨
      ∃ C : OriginalSurfacePairChart e (F '' S) T p true,
        ∀ z ∈ C.coordinates.source, C.chart.symm z ∈ R ↔ 0 ≤ (C.coordinates z).1.2 := by
    intro p hp _ hpS
    have hpQ : p ∈ g '' Q := image_mono inter_subset_right (hV.subset hp)
    have hpT : p ∈ T := hT (image_mono hQK hpQ)
    obtain ⟨y, hyS, rfl⟩ := hpS
    have hyT : y ∈ T := by
      change y ∈ F ⁻¹' T at hpT
      rwa [hFT] at hpT
    have hycover : y ∈ U ∪ g '' Q := by
      by_cases hyA : y ∈ A
      · exact Or.inl (hAU hyA)
      · exact Or.inr (by simpa only [hFoff hyA, id_eq] using hpQ)
    exact region_pair_chart_image_of_preserving_sets hcover F hFinv hFT hFR
      (hcharts y hyS hyT hycover)
  obtain ⟨G, C, hC, hCW, hCP, hGoff, hGPL, hGinv, hGT, hGR, hGV⟩ :=
    exists_protected_vertex_cleanup hcover he V hW hclosedP hVW hprotected hcurrent
  have himage : (F.trans G) '' S = G '' (F '' S) := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨F z, ⟨z, hz, rfl⟩, rfl⟩
    · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, rfl⟩
  refine ⟨N, F.trans G, A ∪ C, hN, hNK, hA.union hC,
    union_subset (hAU.trans subset_union_left) (hCW.trans subset_union_right), ?_,
    original_PL_motion_trans e hcover F G hFPL hGPL,
    original_PL_motion_trans e hcover G.symm F.symm hGinv hFinv, ?_, ?_, ?_, ?_⟩
  · intro y hy
    change G (F y) = y
    rw [hFoff (fun h => hy (Or.inl h))]
    exact hGoff (fun h => hy (Or.inr h))
  · change F ⁻¹' (G ⁻¹' T) = T
    rw [hGT, hFT]
  · change F ⁻¹' (G ⁻¹' R) = R
    rw [hGR, hFR]
  · rw [himage, ← hV]
    exact hGV
  · intro a ha hcard haP
    obtain ⟨hfa, hca⟩ := hedges a ha hcard haP
    have hretained := protected_contacts_retained_by_vertex_cleanup G hC hCP hGoff
      (image_mono haP) hfa hca
    rw [himage]
    exact hretained

end PoincareConjecture.M76
