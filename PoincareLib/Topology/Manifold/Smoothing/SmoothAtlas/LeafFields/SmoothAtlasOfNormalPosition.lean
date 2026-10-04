import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.LeafFields.SmoothLeafFieldChart
import PoincareLib.Topology.Manifold.Smoothing.SmoothAtlas.LeafFields.LeafProjectionAtlas
import PoincareLib.Topology.Manifold.Smoothing.SmoothAtlas.LeafFields.SmoothNormalPosition

/-!
# Compatible smooth atlases from finite normal position

Smooth transverse leaf fields give a chart at every carrier point,
and these charts have smooth transitions. The finite field theorem
then supplies smoothing from the closed-manifold link conditions
and initial vertex planes. See Cairns 1940, Sections 7--9, pp. 803--806,
Section 11, p. 807 and M76 derivations 65, 70--72.
-/

set_option autoImplicit false

open Set Geometry
open scoped Manifold ContDiff

namespace PoincareMT.M76.Smoothing

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

/-- Smooth normal position gives a compatible smooth atlas on
the carrier of a finite pure three-complex with paired triangle
facets. See Cairns p. 806 and M76 derivations 70--72. -/
theorem exists_smooth_atlas_of_smoothLeafField (K : SimplicialComplex ℝ E)
    (hfinite : K.faces.Finite)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 4)
    (htriangles : ∀ t ∈ K.faces, t.card = 3 → (K.faceLink t).vertices.ncard = 2)
    {P : E → EuclideanSubspace E} {U : Set E}
    (hP : EuclideanSubspace.IsSmoothLeafFieldOn P U)
    (hU : IsOpen U) (hKU : K.space ⊆ U)
    (hdim : ∀ y ∈ U, Module.finrank ℝ (P y).subspace + 3 = Module.finrank ℝ E)
    (htrans : ∀ s ∈ K.faces, ∀ y ∈ convexHull ℝ (s : Set E),
      (P y).subspace.IsSecantTransverse (K.closedFaceStar s).space) :
    ∃ atlas : ChartedSpace (EuclideanSpace ℝ (Fin 3)) K.space,
      letI := atlas; IsManifold (𝓡 3) ∞ K.space := by
  have hcharts (a : K.space) :
      ∃ e : OpenPartialHomeomorph K.space (EuclideanSpace ℝ (Fin 3)),
      ∃ b : EuclideanSpace ℝ (Fin 3) →ᴬ[ℝ] E,
      ∃ Q : E → E →L[ℝ] EuclideanSpace ℝ (Fin 3),
        a ∈ e.source ∧
        (∀ z ∈ e.target, ContDiffAt ℝ ∞ Q (b z)) ∧
        ∀ y ∈ e.source, Function.RightInverse b.contLinear (Q y) ∧
          (Q y).ker = (P y).subspace ∧ Q (b (e y)) = Q y ∧
          b (e y) - y ∈ (P y).subspace := by
    obtain ⟨s, hs, has⟩ := K.exists_face_intrinsicInterior_of_finite hfinite a.property
    apply K.exists_chart_of_smoothLeafField hfinite (by simpa using hpure) hs
      (fun t ht _ hcard => ?_) a has hP hU (hKU a.property)
      (by simpa using hdim) (htrans s hs a (intrinsicInterior_subset has))
    apply K.hasTwoFullCofaces_of_faceLink_ncard_eq_two hcard
    exact htriangles t ht (by simpa using hcard)
  choose c b Q hc hQ hspec using hcharts
  exact exists_smooth_atlas_of_leaf_coordinates c (fun a => ⟨a, hc a⟩)
    Subtype.val (fun y => (P y).subspace) b Q hQ hspec

/-- Finite independent three-complexes satisfying the closed
link conditions and admitting initial vertex transverse planes
have compatible smooth atlases. See Cairns pp. 803--807 and M76
derivations 65, 70--72. -/
theorem exists_smooth_atlas_of_vertexStarPlanes (K : SimplicialComplex ℝ E)
    (hK : AffineIndependent ℝ ((↑) : K.vertices → E)) (hfinite : K.faces.Finite)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 4)
    (hedges : ∀ t ∈ K.faces, t.card = 2 → IsConnected (K.faceLink t).space)
    (htriangles : ∀ t ∈ K.faces, t.card = 3 → (K.faceLink t).vertices.ncard = 2)
    (hvertices : ∀ s ∈ K.faces, s.card = 1 →
      Nonempty (SecantTransversePlaneSpace 3 (K.closedFaceStar s).space)) :
    ∃ atlas : ChartedSpace (EuclideanSpace ℝ (Fin 3)) K.space,
      letI := atlas; IsManifold (𝓡 3) ∞ K.space := by
  obtain ⟨U, hU, hKU, P, hP, hdim, htrans⟩ :=
    exists_smooth_transverse_leafField K hK hfinite hpure hedges htriangles hvertices
  exact exists_smooth_atlas_of_smoothLeafField K hfinite hpure htriangles hP hU hKU hdim htrans

/-- Simplexwise affine Brouwer vertex stars give the initial
planes and hence a compatible smooth atlas. Their realization
remains an explicit hypothesis. See Cairns pp. 799, 803--807 and
M76 derivations 51, 65, 70--72. -/
theorem exists_smooth_atlas_of_brouwerStars (K : SimplicialComplex ℝ E)
    (hK : AffineIndependent ℝ ((↑) : K.vertices → E)) (hfinite : K.faces.Finite)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 4)
    (hedges : ∀ t ∈ K.faces, t.card = 2 → IsConnected (K.faceLink t).space)
    (htriangles : ∀ t ∈ K.faces, t.card = 3 → (K.faceLink t).vertices.ncard = 2)
    (hbrouwer : ∀ p : E, {p} ∈ K.faces →
      ∃ f : E → EuclideanSpace ℝ (Fin 3),
        (K.closedFaceStar {p}).AffineOnFaces f ∧
        InjOn f (K.closedFaceStar {p}).space ∧
        (interior (f '' (K.closedFaceStar {p}).space)).Nonempty) :
    ∃ atlas : ChartedSpace (EuclideanSpace ℝ (Fin 3)) K.space,
      letI := atlas; IsManifold (𝓡 3) ∞ K.space := by
  obtain ⟨U, hU, hKU, P, hP, hdim, htrans⟩ :=
    exists_smooth_transverse_leafField_of_brouwerStars K hK hfinite hpure hedges htriangles hbrouwer
  exact exists_smooth_atlas_of_smoothLeafField K hfinite hpure htriangles hP hU hKU hdim htrans

end PoincareMT.M76.Smoothing
