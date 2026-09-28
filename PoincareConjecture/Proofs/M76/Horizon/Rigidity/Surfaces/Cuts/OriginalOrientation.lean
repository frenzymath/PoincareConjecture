import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Orientation.LocalProjection
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Orientation.Finite.AllEdgeSigns

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Geometry AbstractSimplicialComplex
open PreAbstractSimplicialComplex.ModTwoCochains

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) hamiltonZeroPeriodLattice
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

theorem exists_hamiltonZero_frontier_all_edge_signs
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E]
    (e : ι → OpenPartialHomeomorph X0 V3)
    (hcover : ∀ x, ∃ i, x ∈ (e i).source)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (K J : SimplicialComplex ℝ E) (hJK : J ≤ K) (hJ : J.faces.Finite)
    (g : E → X0) (N : Set X0)
    (hgi : InjOn g K.space) (hg : ContinuousOn g J.space)
    (hfront : MapsTo g J.space (frontier N))
    (hstars : ∀ p ∈ K.vertices, ∃ D : OpenPartialHomeomorph X0 V3,
      (∀ i, (e i).symm.trans D ∈ piecewiseAffineGroupoid V3) ∧
      MapsTo g (K.closedStar p).space D.source ∧
      (K.closedStar p).AffineOnFaces (D ∘ g) ∧
      (D.source ⊆ N ∨ ∃ (ell : V3 →ᴬ[ℝ] ℝ) (n : V3),
        ell.contLinear n = 1 ∧ ∀ y ∈ D.source, y ∈ N ↔ 0 ≤ ell (D y))) :
    ∃ (number : J.vertices ↪ ℕ)
      (sigma : Triangle J.vertexAbstractComplex.toPreAbstractSimplicialComplex → ZMod 2),
      ∀ (t u : Triangle J.vertexAbstractComplex.toPreAbstractSimplicialComplex), t ≠ u →
        ∀ s : Edge J.vertexAbstractComplex.toPreAbstractSimplicialComplex,
          s.val ⊆ t.val → s.val ⊆ u.val →
          (sigma t + boundaryFaceParity number t.val s.val) +
            (sigma u + boundaryFaceParity number u.val s.val) = 1 := by
  let : T2Space X0 := (Q0).isEmbedding.t2Space
  let : LocallyCompactSpace X0 := (Q0).isOpenEmbedding.locallyCompactSpace
  let charts := {D : OpenPartialHomeomorph X0 V3 |
    ∀ i, (e i).symm.trans D ∈ piecewiseAffineGroupoid V3}
  let q : charts → OpenPartialHomeomorph X0 V3 := Subtype.val
  have hq : ∀ H D, (q H).symm.trans (q D) ∈ piecewiseAffineGroupoid V3 :=
    fun H D ↦ compatiblePLCharts_trans e hcover hcompat H D H.property D.property
  obtain ⟨label, hlabel⟩ := exists_hamiltonZero_local_projection_atlas_labels
    (id : X0 → X0) (Homeomorph.refl X0).isLocalHomeomorph q hq
  let pull (D : charts) : C({z : J.space | g z ∈ D.val.source}, D.val.source) :=
    ⟨fun z ↦ ⟨g z.val, z.property⟩,
      (hg.comp_continuous (continuous_subtype_val.comp continuous_subtype_val)
        (fun z ↦ z.val.property)).subtype_mk _⟩
  let labels (D : charts) := LocallyConstant.comap (pull D) (label D)
  exact exists_frontier_all_edge_signs_of_chart_labels e K J hJK hJ g N hgi hfront hstars
    hq labels (fun H D z hH hD ↦ hlabel H D (g z) hH hD)

end PoincareConjecture.M76
