import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Boundary.ProjectionOrientation
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Boundary.Orientation.GeometricCofaceSigns
import PoincareConjecture.Proofs.M76.Dehn.OriginalPLStage
import PoincareConjecture.Proofs.M76.PrimeReduction.OriginalBoundaryMarks









set_option autoImplicit false

open Set Geometry Topology AbstractSimplicialComplex
open PreAbstractSimplicialComplex.ModTwoCochains

namespace PoincareConjecture.M76.Dehn

local notation "V3" => (Fin 3 → ℝ)



theorem exists_frontier_coface_signs_of_common_projection
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X]
    (e : ι → OpenPartialHomeomorph X V3)
    (hcover : ∀ x : X, ∃ i, x ∈ (e i).source)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (P : X → V3) (hP : ∀ i, EqOn (e i) P (e i).source)
    (K A : SimplicialComplex ℝ E) (hAK : A ≤ K) (hA : A.faces.Finite)
    (g : E → X) (N : Set X) (hgi : InjOn g K.space)
    (hgc : ContinuousOn g A.space) (hfront : MapsTo g A.space (frontier N))
    (hstars : ∀ p ∈ K.vertices, ∃ B : OpenPartialHomeomorph X V3,
      (∀ k, (e k).symm.trans B ∈ piecewiseAffineGroupoid V3) ∧
      MapsTo g (K.closedStar p).space B.source ∧
      (K.closedStar p).AffineOnFaces (B ∘ g) ∧
      (B.source ⊆ N ∨ ∃ (ell : V3 →ᴬ[ℝ] ℝ) (n : V3),
        ell.contLinear n = 1 ∧ ∀ y ∈ B.source, y ∈ N ↔ 0 ≤ ell (B y))) :
    ∃ (number : E → ℕ) (sign : Finset E → ZMod 2), InjOn number A.vertices ∧
      ∀ t ∈ A.faces, t.card = 3 → ∀ u ∈ A.faces, u.card = 3 → t ≠ u →
        ∀ s : Finset E, s.card = 2 → s ⊆ t → s ⊆ u →
          (sign t + boundaryFaceParity number t s) +
            (sign u + boundaryFaceParity number u s) = 1 := by
  let charts := {H : OpenPartialHomeomorph X V3 |
    ∀ k, (e k).symm.trans H ∈ piecewiseAffineGroupoid V3}
  let q : charts → OpenPartialHomeomorph X V3 := Subtype.val
  have hq : ∀ H J, (q H).symm.trans (q J) ∈ piecewiseAffineGroupoid V3 :=
    fun H J ↦ compatiblePLCharts_trans e hcover hcompat H J H.property J.property
  let base : ι → charts := fun i ↦ ⟨e i, fun j ↦ hcompat j i⟩
  obtain ⟨label, hlabel⟩ := exists_chart_labels_of_neutral_cover q hq base hcover
    (fun i j x ↦ plAtlasTransitionSign_eq_one_of_common_coordinates
      q hq (base i) (base j) P (hP i) (hP j) x)
  let pull (H : charts) : {z : A.space | g z ∈ (q H).source} → (q H).source :=
    fun z ↦ ⟨g z.val, z.property⟩
  have hpull (H : charts) : Continuous (pull H) :=
    (hgc.domRestrict.comp continuous_subtype_val).subtype_mk _
  let labels (H : charts) := (label H).comap ⟨pull H, hpull H⟩
  obtain ⟨number, sigma, hcancel⟩ :=
    exists_frontier_all_edge_signs_of_chart_labels e K A hAK hA g N hgi hfront hstars
      hq labels (fun H J z hH hJ ↦ hlabel H J (g z) hH hJ)
  exact exists_geometric_coface_signs A number sigma hcancel

end PoincareConjecture.M76.Dehn

namespace Geometry.OriginalPLTower

local notation "V3" => (Fin 3 → ℝ)



theorem Stage.exists_standard_region_boundary_signs
    {U E M : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [DecidableEq E] [TopologicalSpace M]
    (chart : OpenPartialHomeomorph M V3)
    {S : SimplicialComplex ℝ U} {f : U → M} {r : M → ℝ} {C : Set M}
    (st : Stage (fun _ : Unit ↦ chart) S f r C)
    {N : Set st.Carrier} (hN : IsClosed N)
    (K A : SimplicialComplex ℝ E) (hAK : A ≤ K) (hA : A.faces.Finite)
    (J : N ≃ₜ K.space) (F : st.Carrier → E) (g : E → N)
    (hJF : ∀ x : N, (J x : E) = F x)
    (hg : ∀ z : K.space, (g z : st.Carrier) = (J.symm z : st.Carrier))
    (hAs : A.space = F '' frontier N)
    (hstars : ∀ p ∈ K.vertices, ∃ B : OpenPartialHomeomorph st.Carrier V3,
      MapsTo (fun z ↦ (g z : st.Carrier)) (K.closedStar p).space B.source ∧
      (K.closedStar p).AffineOnFaces (fun z ↦ B (g z)) ∧
      (∀ k, (st.charts k).symm.trans B ∈ piecewiseAffineGroupoid V3) ∧
      (B.source ⊆ N ∨ ∃ (ell : V3 →ᴬ[ℝ] ℝ) (n : V3),
        ell.contLinear n = 1 ∧ ∀ y ∈ B.source, y ∈ N ↔ 0 ≤ ell (B y))) :
    ∃ (number : E → ℕ) (sign : Finset E → ZMod 2), InjOn number A.vertices ∧
      ∀ t ∈ A.faces, t.card = 3 → ∀ u ∈ A.faces, u.card = 3 → t ≠ u →
        ∀ s : Finset E, s.card = 2 → s ⊆ t → s ⊆ u →
          (sign t + boundaryFaceParity number t s) +
            (sign u + boundaryFaceParity number u s) = 1 := by
  have hgi : InjOn (fun z ↦ (g z : st.Carrier)) K.space := by
    intro x hx y hy hxy
    have h : J.symm ⟨x, hx⟩ = J.symm ⟨y, hy⟩ :=
      Subtype.ext ((hg ⟨x, hx⟩).symm.trans (hxy.trans (hg ⟨y, hy⟩)))
    exact congrArg Subtype.val (J.symm.injective h)
  have hgc : ContinuousOn (fun z ↦ (g z : st.Carrier)) K.space := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    change Continuous (fun z : K.space ↦ (g z : st.Carrier))
    have heq : (fun z : K.space ↦ (g z : st.Carrier)) =
        (fun z : K.space ↦ (J.symm z : st.Carrier)) := funext hg
    rw [heq]
    exact continuous_subtype_val.comp J.symm.continuous
  have hfront : MapsTo (fun z ↦ (g z : st.Carrier)) A.space (frontier N) := by
    intro z hz
    apply (PoincareConjecture.M76.original_model_mem_image_iff J F g hJF hg
      hN.frontier_subset ⟨z, SimplicialComplex.space_subset_of_le hAK hz⟩).mpr
    exact hAs ▸ hz
  apply PoincareConjecture.M76.Dehn.exists_frontier_coface_signs_of_common_projection
    st.charts st.cover st.compatible (chart ∘ st.projection) ?_
    K A hAK hA (fun z ↦ (g z : st.Carrier)) N hgi
    (hgc.mono (SimplicialComplex.space_subset_of_le hAK)) hfront ?_
  · intro i x _
    exact congrFun (st.chart_forward i) x
  · intro p hp
    obtain ⟨B, hB, hPL, hcompat, hregion⟩ := hstars p hp
    exact ⟨B, hcompat, hB, hPL, hregion⟩

end Geometry.OriginalPLTower
