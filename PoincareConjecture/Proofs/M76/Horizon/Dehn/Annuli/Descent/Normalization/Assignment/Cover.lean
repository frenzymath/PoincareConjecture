import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Descent.Normalization.Assignment.Charts
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FiniteMarkedFaceCover
import PoincareConjecture.Proofs.M76.Horizon.Polyhedral.Simplicial.RefinementEdgeStars










set_option autoImplicit false

open Set Metric Geometry Topology

namespace Geometry.OriginalPLTower

local notation "V3" => (Fin 3 → ℝ)

variable {U V M ι : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [TopologicalSpace M] {e : ι → OpenPartialHomeomorph M V3}
  {S : SimplicialComplex ℝ U} {f : U → M} {r : M → ℝ} {C : Set M}
  {s t : Stage e S f r C}




theorem Step.exists_relative_face_chart_cover (step : Step s t)
    {R : Set M} (he : PoincareConjecture.M76.PLDomain e R)
    (K A P : SimplicialComplex ℝ V) (hK : K.faces.Finite) (hAK : A ≤ K)
    (hAs : A.space = K.space ∩ P.space)
    {boundary : Set V} (hboundary : boundary ⊆ interior P.space)
    {j : V → t.Carrier} (hj : PolyhedralPLInCharts t.charts j K.space)
    (hjR : MapsTo j K.space (t.projection ⁻¹' R))
    (hproper : ∀ x ∈ K.space,
      j x ∈ frontier (t.projection ⁻¹' R) ↔ x ∈ boundary) :
    ∃ (K' A' : SimplicialComplex ℝ V),
      K'.faces.Finite ∧ K'.IsSubdivision K ∧ A' ≤ K' ∧ A'.space = A.space ∧
      (∀ a ∈ K'.faces, (∀ v ∈ a, v ∈ A'.vertices) → a ∈ A'.faces) ∧
      ∃ (center : K'.faces → K.space)
        (box : ∀ a : K'.faces, RelativeChartBox step R (j (center a))),
        (∀ a : K'.faces, MapsTo j (convexHull ℝ (a.val : Set V))
          (box a).neighborhood) ∧
        ∀ a : K'.faces, a.val ∉ A'.faces →
          (box a).upper.source ⊆ interior (t.projection ⁻¹' R) := by
  classical
  let boxes (x : K.space) : RelativeChartBox step R (j x) :=
    Classical.choice (step.nonempty_relative_chart_box he (hjR x.property))
  let W (x : K.space) : Set K.space :=
    (fun z : K.space ↦ j z) ⁻¹'
      ((boxes x).upper.source ∩ (boxes x).upper ⁻¹'
        ball ((boxes x).upper (j x)) (boxes x).radius) ∩
    (if (x : V) ∈ interior P.space then Subtype.val ⁻¹' interior P.space else univ)
  have hjc : Continuous (fun z : K.space ↦ j z) :=
    hj.continuousOn.comp_continuous continuous_subtype_val (fun z ↦ z.property)
  have hW (x : K.space) : IsOpen (W x) := by
    apply IsOpen.inter
    · exact ((boxes x).upper.isOpen_inter_preimage isOpen_ball).preimage hjc
    · split_ifs
      · exact isOpen_interior.preimage continuous_subtype_val
      · exact isOpen_univ
  have hcover (x : K.space) : ∃ y, x ∈ W y := by
    refine ⟨x, ⟨(boxes x).point, mem_ball_self (boxes x).radius_pos⟩, ?_⟩
    split_ifs with hx
    · exact hx
    · exact mem_univ x
  obtain ⟨K', A', hK', hsub, hA', hAK', hA's, hfull, hfaces⟩ :=
    K.exists_finite_marked_face_cover A hK (hK.subset hAK)
      (SimplicialComplex.space_subset_of_le hAK) W hW hcover
  have hchoose (a : K'.faces) : ∃ x : K.space,
      ∀ (z : V) (hz : z ∈ convexHull ℝ (a.val : Set V)),
        (⟨z, hsub.space_eq.subset (K'.convexHull_subset_space a.property hz)⟩ : K.space)
          ∈ W x := by
    obtain ⟨x, hx⟩ := hfaces a a.property
    exact ⟨x, fun z hz ↦ hx ⟨z, hsub.space_eq.subset
      (K'.convexHull_subset_space a.property hz)⟩ hz⟩
  choose center hcenter using hchoose
  refine ⟨K', A', hK', hsub, hAK', hA's, hfull, center,
    fun a ↦ boxes (center a), ?_, ?_⟩
  · intro a z hz
    have hsmall := (hcenter a z hz).1
    exact ⟨hsmall.1, (boxes (center a)).small_large (subset_closure hsmall.2)⟩
  · intro a ha
    apply (boxes (center a)).interior_source
    have hnot : (center a : V) ∉ interior P.space := by
      intro hc
      obtain ⟨z, hz⟩ := Set.Nonempty.intrinsicInterior
        (convex_convexHull ℝ (a.val : Set V))
        (Finset.coe_nonempty.mpr (K'.nonempty_of_mem_faces a.property)).convexHull
      have hzp : z ∈ interior P.space := by
        have hzW := (hcenter a z (intrinsicInterior_subset hz)).2
        simpa only [if_pos hc, mem_preimage] using hzW
      apply ha
      apply K'.face_mem_subcomplex_of_intrinsicInterior A' hAK' a.property hz
      rw [hA's, hAs]
      exact ⟨hsub.space_eq.subset (K'.convexHull_subset_space a.property
        (intrinsicInterior_subset hz)), interior_subset hzp⟩
    by_contra hn
    have hfront : j (center a) ∈ frontier (t.projection ⁻¹' R) :=
      ⟨subset_closure (hjR (center a).property), hn⟩
    exact hnot (hboundary ((hproper _ (center a).property).mp hfront))

end Geometry.OriginalPLTower
