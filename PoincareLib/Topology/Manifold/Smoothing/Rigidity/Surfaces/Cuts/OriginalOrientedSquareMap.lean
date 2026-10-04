import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.Cuts.OriginalEulerCutDisk
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.Cuts.OriginalCoherentSourceReversal
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.Cuts.OriginalPeriodicSquareMap
import PoincareLib.Topology.Manifold.Smoothing.Dehn.Disks.Boundary.Orientation.GeometricCofaceSigns

/-!
# Periodic square maps of the original oriented Euler-zero surface

The original finite surface supplies the primal and dual trees and the entire
copied cut disk. Its coherent signs reverse the actual paired bridge endpoints.
The matched rectangle construction then supplies a total finite PL square map
with precisely the periodic fibers, normalized to period 64.
-/

set_option autoImplicit false

open Set Geometry Classical AbstractSimplicialComplex
open PreAbstractSimplicialComplex.ModTwoCochains
open PoincareMT.M76.PeriodicSquare

namespace PoincareMT.M76.OriginalTriangleCopies

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

/-- Construct the entire period-64 square map from the finite connected
oriented surface and its Euler count. All map and fiber data are conclusions. -/
theorem nonempty_sourceSquareMap64_of_euler_zero_and_geometric_signs
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hconn : IsConnected K.space)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 3)
    (hcofaces : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    (hlinks : ∀ p ∈ K.vertices, IsConnected (K.faceLink {p}).space)
    (hzero : K.surfaceEulerCount = 0)
    (number : E → ℕ) (hnumber : InjOn number K.vertices)
    (sourceSign : Finset E → ZMod 2)
    (hcancel : ∀ T ∈ K.faces, ∀ U ∈ K.faces, T.card = 3 → U.card = 3 → T ≠ U →
      ∀ a b : E, a ≠ b → {a, b} ⊆ T → {a, b} ⊆ U →
      (sourceSign T + boundaryFaceParity number T {a, b}) +
        (sourceSign U + boundaryFaceParity number U {a, b}) = 1) :
    Nonempty (SourceSquareMap 64 K) := by
  let : Fintype K.faces := hK.fintype
  let : Fintype K.vertices := (K.finite_vertices_of_finite_faces hK).fintype
  let : Fintype K.barycentricSubdivision.faces := K.barycentricSubdivision_finite.fintype
  obtain ⟨P, hP, D, hD, _, _, hcut⟩ :=
    exists_original_cut_disk_of_euler_zero K hconn hpure hcofaces hlinks hzero
  let : Fintype (ResidualComplementaryEdge K P D) := Fintype.ofFinite _
  obtain ⟨labels, ⟨A⟩⟩ := hcut
  have hbound : ∀ s ∈ K.faces, s.card ≤ 3 := by
    intro s hs
    obtain ⟨t, _, hst, htc⟩ := hpure s hs
    exact htc ▸ Finset.card_le_card hst
  exact ⟨A.sourceSquareMap64_of_source_reversal hbound
    (A.source_bridge_reversal_of_original_coherent_signs hpure number hnumber sourceSign hcancel)⟩

/-- Vertex-numbered coherent source signs construct the actual period-64 map.
The geometric sign conversion preserves the literal original faces. -/
theorem nonempty_sourceSquareMap64_of_euler_zero_and_signs
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hconn : IsConnected K.space)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 3)
    (hcofaces : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    (hlinks : ∀ p ∈ K.vertices, IsConnected (K.faceLink {p}).space)
    (hzero : K.surfaceEulerCount = 0)
    (number : K.vertices ↪ ℕ)
    (sigma : PreAbstractSimplicialComplex.ModTwoCochains.Triangle
      K.vertexAbstractComplex.toPreAbstractSimplicialComplex → ZMod 2)
    (hcancel : ∀ (t u : PreAbstractSimplicialComplex.ModTwoCochains.Triangle
        K.vertexAbstractComplex.toPreAbstractSimplicialComplex), t ≠ u →
      ∀ s : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex,
        s.val ⊆ t.val → s.val ⊆ u.val →
        (sigma t + boundaryFaceParity number t.val s.val) +
          (sigma u + boundaryFaceParity number u.val s.val) = 1) :
    Nonempty (SourceSquareMap 64 K) := by
  obtain ⟨label, sign, hlabel, hsign⟩ := Dehn.exists_geometric_coface_signs K number sigma hcancel
  apply nonempty_sourceSquareMap64_of_euler_zero_and_geometric_signs K hK hconn hpure
    hcofaces hlinks hzero label hlabel sign
  intro T hT U hU hTc hUc hne a b hab ha hb
  exact hsign T hT hTc U hU hUc hne {a, b} (by simp [hab]) ha hb

end PoincareMT.M76.OriginalTriangleCopies
