import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.DoubleCurve.CrossingEdgeGraph
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Graphs.ComponentCycleLabels
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Polygons.RegularTriangleIntersection

/-!
# The realized graph of a regular geometric slice

Actual crossing edges label distinct points of the zero plane.
Triangle incidence supplies the graph, and the closed-surface
coface condition makes it degree two. See Alexander 1924, p. 6
and M76 derivation 93.
-/

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [DecidableEq E]

/-- The actual crossing-edge labels of a geometric zero slice.
See Alexander p. 6 and M76 derivation 93. -/
def regularCrossingEdges (K : SimplicialComplex ℝ E) (A : E →ᵃ[ℝ] ℝ) : Set (Finset E) :=
  {e | e ∈ K.faces ∧ e.IsBichromaticPair (fun v => decide (0 < A v))}

/-- The regular slice graph records shared triangular cofaces
of crossing edges. See Alexander p. 6 and M76 derivation 93. -/
noncomputable def regularSliceGraph (K : SimplicialComplex ℝ E) (A : E →ᵃ[ℝ] ℝ) :
    SimpleGraph (K.regularCrossingEdges A) :=
  K.toPreAbstractSimplicialComplex.crossingEdgeGraph (fun v => decide (0 < A v))

/-- Combinatorial crossing labels strictly straddle a regular
affine zero plane. See Alexander p. 6 and M76 derivation 93. -/
theorem straddlesZero_of_regularCrossingEdge (K : SimplicialComplex ℝ E) (A : E →ᵃ[ℝ] ℝ)
    (hreg : ∀ v ∈ K.vertices, A v ≠ 0) (e : K.regularCrossingEdges A) :
    A.StraddlesZero e.val := by
  apply (A.straddlesZero_iff_bichromatic e.val ?_).mpr e.property.2
  intro v hv
  exact hreg v (K.down_closed e.property.1 (Finset.singleton_subset_iff.mpr hv)
    (Finset.singleton_nonempty v))

/-- The actual geometric point represented by a crossing-edge
label. See Alexander p. 6 and M76 derivation 93. -/
noncomputable def regularCrossingPoint (K : SimplicialComplex ℝ E) (A : E →ᵃ[ℝ] ℝ)
    (hreg : ∀ v ∈ K.vertices, A v ≠ 0) (e : K.regularCrossingEdges A) : E :=
  A.straddlingPoint e.val (K.straddlesZero_of_regularCrossingEdge A hreg e)

/-- The realized crossing belongs to its edge and to the
affine zero plane. See Alexander p. 6 and M76 derivation 93. -/
theorem regularCrossingPoint_mem (K : SimplicialComplex ℝ E) (A : E →ᵃ[ℝ] ℝ)
    (hreg : ∀ v ∈ K.vertices, A v ≠ 0) (e : K.regularCrossingEdges A) :
    K.regularCrossingPoint A hreg e ∈ convexHull ℝ (e.val : Set E) ∧
      A (K.regularCrossingPoint A hreg e) = 0 :=
  A.straddlingPoint_mem e.val (K.straddlesZero_of_regularCrossingEdge A hreg e)

/-- Different crossing labels realize to different points.
See Alexander p. 6 and M76 derivation 93. -/
theorem regularCrossingPoint_injective (K : SimplicialComplex ℝ E) (A : E →ᵃ[ℝ] ℝ)
    (hreg : ∀ v ∈ K.vertices, A v ≠ 0) :
    Function.Injective (K.regularCrossingPoint A hreg) := by
  intro e f hef
  apply Subtype.ext
  have he := K.regularCrossingPoint_mem A hreg e
  have hf := K.regularCrossingPoint_mem A hreg f
  exact K.eq_edges_of_regular_zero_point A hreg e.property.1 f.property.1
    e.property.2.card f.property.2.card he.1 (hef ▸ hf.1) he.2

/-- A finite geometric complex has finitely many crossing
labels. See Alexander p. 6 and M76 derivation 93. -/
theorem finite_regularCrossingEdges (K : SimplicialComplex ℝ E) (A : E →ᵃ[ℝ] ℝ)
    (hK : K.faces.Finite) : (K.regularCrossingEdges A).Finite :=
  hK.subset (fun _ he => he.1)

/-- The closed-surface two-coface condition gives two graph
neighbors at every crossing. See Alexander p. 6 and M76
derivation 93. -/
theorem regularSliceGraph_two_neighbors (K : SimplicialComplex ℝ E) (A : E →ᵃ[ℝ] ℝ)
    (hcofaces : ∀ e ∈ K.faces, e.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ e ⊆ t}.ncard = 2)
    (e : K.regularCrossingEdges A) : ((K.regularSliceGraph A).neighborSet e).ncard = 2 :=
  K.toPreAbstractSimplicialComplex.crossingEdgeGraph_two_neighbors _
    (fun e he hc => hcofaces e he hc.card) e

/-- Every graph edge realizes exactly one triangle section.
See Alexander p. 6 and M76 derivation 93. -/
theorem regularSliceGraph_segment (K : SimplicialComplex ℝ E) (A : E →ᵃ[ℝ] ℝ)
    (hreg : ∀ v ∈ K.vertices, A v ≠ 0) {e f : K.regularCrossingEdges A}
    (hef : (K.regularSliceGraph A).Adj e f) :
    ∃ t ∈ K.faces, t.card = 3 ∧ e.val ⊆ t ∧ f.val ⊆ t ∧
      segment ℝ (K.regularCrossingPoint A hreg e) (K.regularCrossingPoint A hreg f) =
        convexHull ℝ (t : Set E) ∩ {x | A x = 0} := by
  obtain ⟨hne, t, ht, hcard, het, hft⟩ := hef
  refine ⟨t, ht, hcard, het, hft, ?_⟩
  apply A.segment_straddlingPoints_eq_triangleSlice
    (K.straddlesZero_of_regularCrossingEdge A hreg e)
    (K.straddlesZero_of_regularCrossingEdge A hreg f) hcard
  · intro v hv
    exact hreg v (K.down_closed ht (Finset.singleton_subset_iff.mpr hv)
      (Finset.singleton_nonempty v))
  · exact het
  · exact hft
  · exact fun h => hne (Subtype.ext h)

end Geometry.SimplicialComplex
