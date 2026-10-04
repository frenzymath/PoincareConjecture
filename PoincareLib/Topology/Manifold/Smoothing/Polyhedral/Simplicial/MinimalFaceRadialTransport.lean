import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Simplicial.FiniteCarrierFaceInteriors
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Coverings.ClosedStarProjectionCoverage

/-!
# Radial transport in the same original maximal face

A finite closed-hull exclusion fixes one ambient neighborhood
in which every original face meeting it contains the center.
Radial segments there retain the intrinsic interior of their
original maximal face, even when the center is not an original
vertex. See Cairns 1940, pp. 799, 801--802, Hudson 1969,
pp. 12--19 and M76 derivation 286au.
-/

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- One ambient neighborhood of an arbitrary point meets
only original face hulls containing that same point. The
point need not be an original vertex or belong to the carrier.
See Cairns pp. 799, 801--802 and M76 derivation 286au. -/
theorem exists_open_face_hulls_contain_point
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (q : E) :
    ∃ U : Set E, IsOpen U ∧ q ∈ U ∧
      ∀ t ∈ K.faces, (convexHull ℝ (t : Set E) ∩ U).Nonempty →
        q ∈ convexHull ℝ (t : Set E) := by
  let T := {t : Finset E | t ∈ K.faces ∧ q ∉ convexHull ℝ (t : Set E)}
  have hT : T.Finite := hK.subset fun _ ht => ht.1
  let D := ⋃ t ∈ T, convexHull ℝ (t : Set E)
  have hD : IsClosed D :=
    (hT.isCompact_biUnion (fun t _ => t.finite_toSet.isCompact_convexHull ℝ)).isClosed
  have hqD : q ∉ D := by
    intro hq
    obtain ⟨t, ht, hqt⟩ := mem_iUnion₂.mp hq
    exact ht.2 hqt
  refine ⟨Dᶜ, hD.isOpen_compl, hqD, ?_⟩
  intro t ht hmeet
  by_contra hqt
  obtain ⟨p, hpt, hpD⟩ := hmeet
  exact hpD (mem_iUnion₂.mpr ⟨t, ⟨ht, hqt⟩, hpt⟩)

/-- A segment through the interior of an original maximal
face has its far endpoint in that same face interior when
every original endpoint face also contains the center.
The center need not be an original vertex. See Cairns
pp. 801--802 and M76 derivation 286au. -/
theorem mem_intrinsicInterior_of_segment_face_incidence
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {s : Finset E} (hs : s ∈ K.faces)
    (hmax : ∀ t ∈ K.faces, s ⊆ t → t = s)
    {q a p : E} (ha : a ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)))
    (hp : p ∈ K.space)
    (hface : ∀ t ∈ K.faces, p ∈ convexHull ℝ (t : Set E) →
      q ∈ convexHull ℝ (t : Set E))
    (hsegment : a ∈ segment ℝ q p) :
    q ∈ convexHull ℝ (s : Set E) ∧
      p ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)) := by
  obtain ⟨t, ht, hpt⟩ := K.exists_face_intrinsicInterior_of_finite hK hp
  have hqt := hface t ht (intrinsicInterior_subset hpt)
  have hat : a ∈ convexHull ℝ (t : Set E) :=
    (convex_convexHull ℝ _).segment_subset hqt (intrinsicInterior_subset hpt) hsegment
  have hts : t = s := hmax t ht (K.subset_of_mem_intrinsicInterior_face hs ht ha hat)
  exact hts ▸ ⟨hqt, hpt⟩

/-- An actual radial endpoint in an original face-incidence
neighborhood stays in the same original triangle interior.
Auxiliary star geometry may supply the endpoint; no vertex
or link premise is imposed on the original complex here.
See Alexander 1924, pp. 6--8 and M76 derivation 286au. -/
theorem mem_triangle_interior_of_radial_face_neighborhood
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hbound : ∀ t ∈ K.faces, t.card ≤ 3)
    {s : Finset E} (hs : s ∈ K.faces) (hcard : s.card = 3)
    {a p : E} (ha : a ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)))
    (hpK : p ∈ K.space) {C : Set E} (hpC : p ∈ C)
    (hfaceC : ∀ t ∈ K.faces, (convexHull ℝ (t : Set E) ∩ C).Nonempty →
      (0 : E) ∈ convexHull ℝ (t : Set E))
    {ρ : ℝ} (hρ : 1 ≤ ρ) (hpa : p = ρ • a) :
    (0 : E) ∈ convexHull ℝ (s : Set E) ∧
      p ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)) := by
  have hmax : ∀ t ∈ K.faces, s ⊆ t → t = s := by
    intro t ht hst
    exact (Finset.eq_of_subset_of_card_le hst
      (by simpa only [hcard] using hbound t ht)).symm
  have hρpos : 0 < ρ := zero_lt_one.trans_le hρ
  have hinv : ρ⁻¹ ∈ Icc (0 : ℝ) 1 :=
    ⟨inv_nonneg.mpr hρpos.le, (inv_le_one₀ hρpos).mpr hρ⟩
  have haeq : a = ρ⁻¹ • p := by rw [hpa, inv_smul_smul₀ hρpos.ne']
  have hsegment : a ∈ segment ℝ (0 : E) p := by
    rw [haeq]
    exact (convex_segment (0 : E) p).smul_mem_of_zero_mem
      (left_mem_segment ℝ 0 p) (right_mem_segment ℝ 0 p) hinv
  exact K.mem_intrinsicInterior_of_segment_face_incidence hK hs hmax ha hpK
    (fun t ht hpt => hfaceC t ht ⟨p, hpt, hpC⟩) hsegment

end Geometry.SimplicialComplex
