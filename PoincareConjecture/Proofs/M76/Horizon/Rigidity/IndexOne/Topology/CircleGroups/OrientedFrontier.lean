import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Topology.CircleGroups.ClosedPhaseSigns
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Topology.CircleGroups.AmbientOrientation
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Topology.CircleGroups.AffineSignTransport
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Topology.CircleGroups.FiniteSurface
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Boundary.Orientation.GeometricCofaceSigns
import PoincareConjecture.Proofs.M76.Wall.OriginalComponentSphere

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Geometry
open AbstractSimplicialComplex
open Poincare.Topology.Orientation.ProjectivePlane

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "V3" => (Fin 3 → ℝ)

theorem exists_hamilton_euclidean_atlas_labels
    {ι : Type*} (e : ι → OpenPartialHomeomorph X E3)
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid E3) :
    ∃ label : ∀ i, LocallyConstant (e i).source PLOrientationSheet,
      ∀ i j (x : X) (hi : x ∈ (e i).source) (hj : x ∈ (e j).source),
        (label j ⟨x, hj⟩).val =
          plAtlasTransitionSign e he i j ⟨x, hi, hj⟩ * (label i ⟨x, hi⟩).val := by
  let h := (Homeomorph.refl (Fin 1 → ℝ)).prodCongr
    (hamiltonLowerLatticePiEquiv (Fin 2))
  let : T2Space X := h.isEmbedding.t2Space
  let : LocallyCompactSpace X := h.isOpenEmbedding.locallyCompactSpace
  obtain ⟨O⟩ := hamiltonIntervalTorusAmbient_localOrientation
  exact exists_plAtlas_labels_of_localOrientation O euclideanLocalOrientation e he

theorem exists_hamilton_original_atlas_labels
    {ι : Type*} (e : ι → OpenPartialHomeomorph X V3)
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3) :
    ∃ label : ∀ i, LocallyConstant (e i).source PLOrientationSheet,
      ∀ i j (x : X) (hi : x ∈ (e i).source) (hj : x ∈ (e j).source),
        (label j ⟨x, hj⟩).val =
          plAtlasTransitionSign e he i j ⟨x, hi, hj⟩ * (label i ⟨x, hi⟩).val := by
  let a : V3 ≃ᴬ[ℝ] E3 := (EuclideanSpace.equiv (Fin 3) ℝ).symm.toContinuousAffineEquiv
  let q (i : ι) := (e i).transHomeomorph a.toHomeomorph
  have hq := affine_model_plAtlas_compatible e he a
  obtain ⟨label, hlabel⟩ := exists_hamilton_euclidean_atlas_labels q hq
  refine ⟨label, ?_⟩
  intro i j x hi hj
  have h := hlabel i j x hi hj
  rw [plAtlasTransitionSign_affine_model e he a i j ⟨x, hi, hj⟩] at h
  exact h

open PreAbstractSimplicialComplex.ModTwoCochains

theorem exists_hamilton_frontier_geometric_coface_signs
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
  obtain ⟨label, hlabel⟩ := exists_hamilton_original_atlas_labels q hq
  let f (H : charts) : C({z : A.space | g z ∈ H.val.source}, H.val.source) :=
    ⟨fun z => ⟨g z.val, z.property⟩,
      (hg.comp_continuous (continuous_subtype_val.comp continuous_subtype_val)
        (fun z => z.val.property)).subtype_mk _⟩
  let labels (H : charts) := LocallyConstant.comap (f H) (label H)
  obtain ⟨number, sign, hsign⟩ :=
    exists_frontier_all_edge_signs_of_chart_labels e K A hAK hA g N hgi hfront hstars
      hq labels (fun H D z hH hD => hlabel H D (g z) hH hD)
  exact Dehn.exists_geometric_coface_signs A number sign hsign

theorem exists_hamilton_frontier_component_sphere_of_isCyclic
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
  let h := (Homeomorph.refl (Fin 1 → ℝ)).prodCongr
    (hamiltonLowerLatticePiEquiv (Fin 2))
  let : T2Space X := h.isEmbedding.t2Space
  let J := A.edgeComponentComplex C
  have hJ : J.faces.Finite := hK.subset ((A.edgeComponentComplex_le C).trans hAK)
  let : Fintype J.vertices := (J.finite_vertices_of_finite_faces hJ).fintype
  have hJK : J ≤ K := (A.edgeComponentComplex_le C).trans hAK
  have hJs : J.space ⊆ K.space := SimplicialComplex.space_subset_of_le hJK
  obtain ⟨number, sign, hnumber, hcancel⟩ :=
    exists_hamilton_frontier_geometric_coface_signs e hcover hcompat K J hJK hJ g N
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

end PoincareConjecture.M76.HamiltonIntervalTorus
