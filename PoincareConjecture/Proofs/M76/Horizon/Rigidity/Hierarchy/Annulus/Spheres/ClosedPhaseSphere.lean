import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Topology.CircleGroups.OrientedFrontier
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Topology.ComponentGroups
import PoincareConjecture.Proofs.M76.Rigidity.OriginalClosedCircleMap
import PoincareConjecture.Proofs.M76.Wall.OriginalFrontierSurfaceModel
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.ConnectedSubsetComponent

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Metric Geometry AbstractSimplicialComplex
open Poincare.Topology.Orientation.ProjectivePlane

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

theorem hamiltonZeroAmbient_positiveThreeAtlas :
    Nonempty (Poincare.Topology.PositiveThreeAtlas X) := by
  let E := (Fin 0 → ℝ) × (Fin 3 → ℝ)
  let lattice := hamiltonZeroPeriodLattice
  let : DiscreteTopology lattice.toAddSubgroup :=
    inferInstanceAs (DiscreteTopology hamiltonZeroPeriodLattice)
  let p : E →+ X :=
    (AddMonoidHom.id (Fin 0 → ℝ)).prodMap (QuotientAddGroup.mk' lattice.toAddSubgroup)
  have hq : IsCoveringMap
      (QuotientAddGroup.mk : (Fin 3 → ℝ) → ((Fin 3 → ℝ) ⧸ lattice.toAddSubgroup)) :=
    (lattice.toAddSubgroup.isAddQuotientCoveringMap_of_comm
      DiscreteTopology.isDiscrete).isCoveringMap
  have hp : IsLocalHomeomorph p := hq.id_prod.isLocalHomeomorph
  have hsurj : Function.Surjective p := by
    rintro ⟨x, y⟩
    obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective y
    exact ⟨(x, z), rfl⟩
  let a : E ≃L[ℝ] EuclideanSpace ℝ (Fin 3) :=
    (LinearEquiv.ofFinrankEq _ _ (by
      simp [E, Module.finrank_prod, finrank_euclideanSpace])).toContinuousLinearEquiv
  exact p.exists_positiveThreeAtlas_of_quotient hp hsurj a

theorem hamiltonZeroAmbient_localOrientation :
    Nonempty (LocalOrientation X) := by
  let : T2Space X := (Q0).isEmbedding.t2Space
  let : SecondCountableTopology X := (Q0).isEmbedding.secondCountableTopology
  obtain ⟨P⟩ := hamiltonZeroAmbient_positiveThreeAtlas
  exact exists_localOrientation_of_positiveThreeAtlas P

theorem exists_hamiltonZero_euclidean_atlas_labels
    {ι : Type*} (e : ι → OpenPartialHomeomorph X E3)
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid E3) :
    ∃ label : ∀ i, LocallyConstant (e i).source PLOrientationSheet,
      ∀ i j (x : X) (hi : x ∈ (e i).source) (hj : x ∈ (e j).source),
        (label j ⟨x, hj⟩).val =
          plAtlasTransitionSign e he i j ⟨x, hi, hj⟩ * (label i ⟨x, hi⟩).val := by
  let h := Q0
  let : T2Space X := h.isEmbedding.t2Space
  let : LocallyCompactSpace X := h.isOpenEmbedding.locallyCompactSpace
  obtain ⟨O⟩ := hamiltonZeroAmbient_localOrientation
  exact exists_plAtlas_labels_of_localOrientation O euclideanLocalOrientation e he

theorem exists_hamiltonZero_original_atlas_labels
    {ι : Type*} (e : ι → OpenPartialHomeomorph X V3)
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3) :
    ∃ label : ∀ i, LocallyConstant (e i).source PLOrientationSheet,
      ∀ i j (x : X) (hi : x ∈ (e i).source) (hj : x ∈ (e j).source),
        (label j ⟨x, hj⟩).val =
          plAtlasTransitionSign e he i j ⟨x, hi, hj⟩ * (label i ⟨x, hi⟩).val := by
  let a : V3 ≃ᴬ[ℝ] E3 := (EuclideanSpace.equiv (Fin 3) ℝ).symm.toContinuousAffineEquiv
  let q (i : ι) := (e i).transHomeomorph a.toHomeomorph
  have hq := affine_model_plAtlas_compatible e he a
  obtain ⟨label, hlabel⟩ := exists_hamiltonZero_euclidean_atlas_labels q hq
  refine ⟨label, ?_⟩
  intro i j x hi hj
  have h := hlabel i j x hi hj
  rw [plAtlasTransitionSign_affine_model e he a i j ⟨x, hi, hj⟩] at h
  exact h

open PreAbstractSimplicialComplex.ModTwoCochains

theorem exists_hamiltonZero_frontier_geometric_coface_signs
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E]
    (e : ι → OpenPartialHomeomorph X V3)
    (hcover : ∀ x : X, ∃ i, x ∈ (e i).source)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (K A : SimplicialComplex ℝ E) (hAK : A ≤ K) (hA : A.faces.Finite)
    (g : E → X) (N : Set X) (hg : ContinuousOn g A.space)
    (hgi : InjOn g K.space) (hfront : MapsTo g A.space (frontier N))
    (hstars : ∀ p ∈ K.vertices, ∃ D : OpenPartialHomeomorph X V3,
      (∀ i, (e i).symm.trans D ∈ piecewiseAffineGroupoid V3) ∧
      MapsTo g (K.closedStar p).space D.source ∧
      (K.closedStar p).AffineOnFaces (D ∘ g) ∧
      (D.source ⊆ N ∨ ∃ (ell : V3 →ᴬ[ℝ] ℝ) (n : V3),
        ell.contLinear n = 1 ∧ ∀ y ∈ D.source, y ∈ N ↔ 0 ≤ ell (D y))) :
    ∃ (number : E → ℕ) (sign : Finset E → ZMod 2), InjOn number A.vertices ∧
      ∀ t ∈ A.faces, t.card = 3 → ∀ u ∈ A.faces, u.card = 3 → t ≠ u →
        ∀ s : Finset E, s.card = 2 → s ⊆ t → s ⊆ u →
          (sign t + boundaryFaceParity number t s) +
            (sign u + boundaryFaceParity number u s) = 1 := by
  let charts := {D : OpenPartialHomeomorph X V3 |
    ∀ i, (e i).symm.trans D ∈ piecewiseAffineGroupoid V3}
  let q : charts → OpenPartialHomeomorph X V3 := Subtype.val
  have hq : ∀ H D, (q H).symm.trans (q D) ∈ piecewiseAffineGroupoid V3 :=
    fun H D => compatiblePLCharts_trans e hcover hcompat H D H.property D.property
  obtain ⟨label, hlabel⟩ := exists_hamiltonZero_original_atlas_labels q hq
  let f (H : charts) : C({z : A.space | g z ∈ H.val.source}, H.val.source) :=
    ⟨fun z => ⟨g z.val, z.property⟩,
      (hg.comp_continuous (continuous_subtype_val.comp continuous_subtype_val)
        (fun z => z.val.property)).subtype_mk _⟩
  let labels (H : charts) := LocallyConstant.comap (f H) (label H)
  obtain ⟨number, sign, hsign⟩ :=
    exists_frontier_all_edge_signs_of_chart_labels e K A hAK hA g N hgi hfront hstars
      hq labels (fun H D z hH hD => hlabel H D (g z) hH hD)
  exact Dehn.exists_geometric_coface_signs A number sign hsign

theorem exists_hamiltonZero_frontier_component_sphere_of_isCyclic
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E]
    (e : ι → OpenPartialHomeomorph X V3)
    (hcover : ∀ x : X, ∃ i, x ∈ (e i).source)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (K A : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hAK : A ≤ K)
    (g : E → X) (N : Set X) (hg : PolyhedralPLInCharts e g K.space)
    (hgi : InjOn g K.space) (hfront : MapsTo g A.space (frontier N))
    (hstars : ∀ p ∈ K.vertices, ∃ D : OpenPartialHomeomorph X V3,
      (∀ i, (e i).symm.trans D ∈ piecewiseAffineGroupoid V3) ∧
      MapsTo g (K.closedStar p).space D.source ∧
      (K.closedStar p).AffineOnFaces (D ∘ g) ∧
      (D.source ⊆ N ∨ ∃ (ell : V3 →ᴬ[ℝ] ℝ) (n : V3),
        ell.contLinear n = 1 ∧ ∀ y ∈ D.source, y ∈ N ↔ 0 ≤ ell (D y)))
    (hpure : ∀ s ∈ A.faces, ∃ t ∈ A.faces, s ⊆ t ∧ t.card = 3)
    (hcofaces : ∀ s ∈ A.faces, s.card = 2 →
      {t : Finset E | t ∈ A.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    (hlinks : ∀ p ∈ A.vertices, IsConnected (A.faceLink {p}).space)
    (C : A.vertexAbstractComplex.edgeGraph.ConnectedComponent)
    (x : (A.edgeComponentComplex C).space)
    [IsCyclic (FundamentalGroup (A.edgeComponentComplex C).space x)] :
    Nonempty (ChartwisePLSphere e (g '' (A.edgeComponentComplex C).space)) := by
  classical
  let h := Q0
  let : T2Space X := h.isEmbedding.t2Space
  let J := A.edgeComponentComplex C
  have hJ : J.faces.Finite := hK.subset ((A.edgeComponentComplex_le C).trans hAK)
  let : Fintype J.vertices := (J.finite_vertices_of_finite_faces hJ).fintype
  have hJK : J ≤ K := (A.edgeComponentComplex_le C).trans hAK
  have hJs : J.space ⊆ K.space := SimplicialComplex.space_subset_of_le hJK
  obtain ⟨number, sign, hnumber, hcancel⟩ :=
    exists_hamiltonZero_frontier_geometric_coface_signs e hcover hcompat K J hJK hJ g N
      (hg.continuousOn.mono hJs) hgi
      (fun _ hz => hfront (SimplicialComplex.space_subset_of_le (A.edgeComponentComplex_le C) hz))
      hstars
  have hJpure : ∀ s ∈ J.faces, ∃ t ∈ J.faces, t.card = 3 ∧ s ⊆ t := by
    intro s hs
    obtain ⟨t, ht, hst, htc⟩ := A.edgeComponentComplex_pure C hpure s hs
    exact ⟨t, ht, htc, hst⟩
  have hJlinks : ∀ p ∈ J.vertices, IsConnected (J.link p).space := by
    intro p hp
    rw [← J.faceLink_singleton_eq_link, A.edgeComponentComplex_vertex_link C hp]
    exact hlinks p (A.edgeComponentComplex_le C hp)
  have hJcofaces : ∀ s ∈ J.faces, s.card = 2 →
      {t : Finset E | t ∈ J.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2 := by
    intro s hs hsc
    rw [A.edgeComponentComplex_cofaces C hs 3]
    exact hcofaces s (A.edgeComponentComplex_le C hs) hsc
  have hcount := J.surfaceEulerCount_eq_two_of_isCyclic_and_geometric_signs hJ hJpure
    (A.edgeComponentComplex_isPathConnected C).isConnected (by intro p hp; convert! hJlinks p hp)
    hJcofaces number hnumber sign (by convert! hcancel) x
  rw [SimplicialComplex.surfaceEulerCount_eq_vertex_counts] at hcount
  apply exists_original_component_sphere_of_count K A hK hAK hg hgi
    hpure hcofaces hlinks C
  change Nat.card J.vertices + Nat.card (Triangle J.vertexAbstractComplex.toPreAbstractSimplicialComplex) =
    Nat.card (Edge J.vertexAbstractComplex.toPreAbstractSimplicialComplex) + 2
  omega

theorem exists_hamiltonZero_whole_frontier_component_sphere
    {ι : Type*} (e : ι → OpenPartialHomeomorph X V3) {N S : Set X}
    (he : PLDomain e N) (hN : IsCompact N) (hSne : S.Nonempty)
    (hSF : S ⊆ frontier N)
    (hcomponent : ∀ x ∈ S, connectedComponentIn (frontier N) x = S)
    (hcyclic : ∀ x : S, IsCyclic (FundamentalGroup S x)) :
    Nonempty (ChartwisePLSphere e S) := by
  classical
  let h := Q0
  let : T2Space X := h.isEmbedding.t2Space
  obtain ⟨x, hx⟩ := hSne
  have hNne : N.Nonempty := ⟨x, he.closed.frontier_subset (hSF hx)⟩
  obtain ⟨s, F, K, A, Hmodel, g, HB, hFc, _, hK, hAK, hA, _, _, hAs,
    hH, _, hg, hgPL, _, _, hboundary, hstars, hpure, hcofaces, hlinks⟩ :=
    he.exists_original_frontier_surface_model hN hNne
  let q : (s → ℝ × V3) → X := fun z => g z
  have hqi : InjOn q K.space := by
    intro z hz w hw hzw
    have hh : Hmodel.symm ⟨z, hz⟩ = Hmodel.symm ⟨w, hw⟩ :=
      Subtype.ext ((hg ⟨z, hz⟩).symm.trans (hzw.trans (hg ⟨w, hw⟩)))
    exact congrArg Subtype.val (Hmodel.symm.injective hh)
  have hqF (y : X) (hy : y ∈ N) : q (F y) = y := by
    rw [← hH ⟨y, hy⟩]
    exact (hg (Hmodel ⟨y, hy⟩)).trans
      (congrArg Subtype.val (Hmodel.symm_apply_apply ⟨y, hy⟩))
  have hSconn : IsConnected S := by
    rw [← hcomponent x hx]
    exact isConnected_connectedComponentIn_iff.mpr (hSF hx)
  have hFA : F '' S ⊆ A.space := by
    rw [hAs]
    exact image_mono hSF
  obtain ⟨D, hD⟩ := A.exists_edgeComponentComplex_of_isConnected hA
    (hSconn.image F hFc.continuousOn) hFA
  let J := A.edgeComponentComplex D
  have hJA : J ≤ A := A.edgeComponentComplex_le D
  have hJK : J ≤ K := hJA.trans hAK
  have hJs : J.space ⊆ K.space := SimplicialComplex.space_subset_of_le hJK
  have hqfront : MapsTo q A.space (frontier N) := fun z hz =>
    (hboundary z (SimplicialComplex.space_subset_of_le hAK hz)).mpr hz
  have hxJ : F x ∈ J.space := hD (mem_image_of_mem F hx)
  have hqS : q '' J.space = S := by
    apply Subset.antisymm
    · rw [← hcomponent x hx]
      apply ((A.edgeComponentComplex_isPathConnected D).isConnected.image q
        (hgPL.continuousOn.mono hJs)).isPreconnected.subset_connectedComponentIn
      · exact ⟨F x, hxJ, hqF x (he.closed.frontier_subset (hSF hx))⟩
      · rintro _ ⟨z, hz, rfl⟩
        exact hqfront (SimplicialComplex.space_subset_of_le hJA hz)
    · intro y hy
      exact ⟨F y, hD (mem_image_of_mem F hy), hqF y (he.closed.frontier_subset (hSF hy))⟩
  have hJ : J.faces.Finite := hA.subset hJA
  let : CompactSpace J.space := isCompact_iff_compactSpace.mp
    (J.isCompact_space_of_finite hJ)
  let HC0 : J.space ≃ q '' J.space := Equiv.Set.imageOfInjOn q J.space (hqi.mono hJs)
  have hHC0 : Continuous HC0 := (hgPL.continuousOn.mono hJs).domRestrict.subtype_mk _
  let HC : J.space ≃ₜ S :=
    (HC0.toHomeomorphOfContinuousClosed hHC0 hHC0.isClosedMap).trans (Homeomorph.setCongr hqS)
  let z : J.space := ⟨F x, hxJ⟩
  let : IsCyclic (FundamentalGroup S (HC z)) := hcyclic (HC z)
  let : IsCyclic (FundamentalGroup J.space z) :=
    isCyclic_of_injective (FundamentalGroup.map ⟨HC, HC.continuous⟩ z)
      (FundamentalGroup.map_injective_of_leftInverse ⟨HC, HC.continuous⟩
        ⟨HC.symm, HC.symm.continuous⟩ HC.left_inv z)
  have hsphere := exists_hamiltonZero_frontier_component_sphere_of_isCyclic e
    he.cover he.compatible K A hK hAK q N hgPL hqi hqfront
    (by intro p hp; convert! hstars p hp)
    hpure hcofaces (by intro p hp; convert! hlinks p hp) D z
  change Nonempty (ChartwisePLSphere e (q '' J.space)) at hsphere
  rw [hqS] at hsphere
  exact hsphere

end PoincareConjecture.M76
