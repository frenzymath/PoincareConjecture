import PoincareLib.Geometry.CurveShortening.Comparison.IntrinsicComparison.Marked.CoordinateParents
import PoincareLib.Geometry.CurveShortening.Comparison.IntrinsicComparison.Region.RefinementCorner

/-! One synchronized coordinate triangulation with actual marked vertices.
Source: MT Claim 19.40, pp. 470-471; combined-boundary-collar derivation,
Section 9. All contacts and marked vertices belong to the same refinement. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold
open PoincareMT.Topology.Surface Poincare.Topology.Plane.Meshes

namespace PoincareMT

/-- An actual finite smooth coordinate triangulation with exact support and full edge or
vertex contacts. Source: MT Claim 19.40; combined-boundary-collar derivation, Section 9.
Source: Morgan--Tian Proposition 19.35, printed pp. 467-481, especially the regional
Gauss--Bonnet argument of Lemma 19.45, p. 474; the explicit coordinate construction is
reviewed in `proof-work/tasks/M64/reviews/2026-09-27-round1-intrinsic-contacts.md`,
Mathematical Checks. -/
structure M64IntrinsicCoordinateTriangulation (K : Set AnnulusCoordinates) where
  count : ℕ
  face : Fin count → SmoothFace AnnulusCoordinates
  coordinates : Fin count → OpenPartialHomeomorph Plane AnnulusCoordinates
  basis : Fin count → AffineBasis (Fin 3) ℝ Plane
  smooth : ∀ p, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (coordinates p) (coordinates p).source
  inverse_smooth : ∀ p,
    ContMDiffOn (𝓡 2) (𝓡 2) ∞ (coordinates p).symm (coordinates p).target
  source : ∀ p, convexHull ℝ (range (basis p)) ⊆ (coordinates p).source
  carrier : ∀ p, (face p).carrier = coordinates p '' convexHull ℝ (range (basis p))
  boundary : ∀ p k, ((face p).boundary k).map = coordinates p ∘
    affineChartSegment (basis p (k.succAbove 0)) (basis p (k.succAbove 1))
  intersection_frontier : ∀ p q, p ≠ q →
    (face p).carrier ∩ (face q).carrier ⊆ frontier (face p).carrier
  intersections : ∀ p q, p ≠ q →
    (∃ k l : Fin 3, (face p).carrier ∩ (face q).carrier =
      ((face p).boundary k).map '' Icc (0 : ℝ) 1 ∧
      ((face p).boundary k).map '' Icc (0 : ℝ) 1 = ((face q).boundary l).map '' Icc (0 : ℝ) 1) ∨
    ∃ v : Fin 3, (face p).carrier ∩ (face q).carrier ⊆ {coordinates p (basis p v)}
  cover : (⋃ p, (face p).carrier) = K

/-- Compatible actual parents give one synchronized triangulation that retains every
prescribed support point as a vertex. Source: MT Claim 19.40; combined-boundary-collar
derivation, Section 9. Source: Morgan--Tian Proposition 19.35, printed pp. 467-481,
especially the regional Gauss--Bonnet argument of Lemma 19.45, p. 474; the explicit
coordinate construction is reviewed in
`proof-work/tasks/M64/reviews/2026-09-27-round1-intrinsic-contacts.md`, Mathematical Checks. -/
theorem m64Intrinsic_exists_marked_region_triangulation
    {I : Type*} [Finite I]
    (F : I → OpenPartialHomeomorph Plane AnnulusCoordinates)
    (b : I → AffineBasis (Fin 3) ℝ Plane)
    (hF : ∀ i, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (F i) (F i).source)
    (hFi : ∀ i, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (F i).symm (F i).target)
    (hsource : ∀ i, convexHull ℝ (range (b i)) ⊆ (F i).source)
    (hparents : ∀ i j, i ≠ j → CoordinateTriangleBoundaryIntersection (F i) (F j) (b i) (b j))
    {K : Set AnnulusCoordinates} (hcover : (⋃ i, F i '' convexHull ℝ (range (b i))) = K)
    (marks : Finset AnnulusCoordinates) (hmarks : (marks : Set AnnulusCoordinates) ⊆ K) :
    ∃ R : M64IntrinsicCoordinateTriangulation K,
      ∀ q ∈ marks, ∃ v : Euler.CoordinateVertex R.coordinates R.basis, v.1 = q := by
  classical
  obtain ⟨n, G, d, hG, hGi, hGs, hGp, hGc, hkeep⟩ :=
    m64Intrinsic_exists_marked_coordinate_parents F b hF hFi hsource hparents marks
      (hmarks.trans hcover.symm.subset)
  obtain ⟨_, R, hcompat, hcov⟩ :=
    m64Intrinsic_exists_compatible_region_refinement G d hG hGi hGs hGp
  let Child := (i : Fin n) × (R i).mesh.Triangle
  let _ := Fintype.ofFinite Child
  let index := Fintype.equivFin Child
  let face (p : Fin (Fintype.card Child)) := (R (index.symm p).1).face (index.symm p).2
  let C (p : Fin (Fintype.card Child)) := G (index.symm p).1
  let basis (p : Fin (Fintype.card Child)) :=
    meshTriangleBasis (R (index.symm p).1).mesh (index.symm p).2
  have htotal : (⋃ p, (face p).carrier) = K := by
    rw [← hcover, ← hGc, ← hcov]
    ext x
    constructor
    · intro hx
      obtain ⟨p, hp⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨index.symm p, hp⟩
    · intro hx
      obtain ⟨p, hp⟩ := mem_iUnion.mp hx
      apply mem_iUnion.mpr
      refine ⟨index p, ?_⟩
      change x ∈ ((R (index.symm (index p)).1).face (index.symm (index p)).2).carrier
      rw [index.symm_apply_apply]
      exact hp
  let triangulation : M64IntrinsicCoordinateTriangulation K :=
    { count := Fintype.card Child
      face := face
      coordinates := C
      basis := basis
      smooth := fun p => hG _
      inverse_smooth := fun p => hGi _
      source := fun p => (R (index.symm p).1).source_subset (index.symm p).2
      carrier := fun p => (R (index.symm p).1).carrier_eq (index.symm p).2
      boundary := fun p k => (R (index.symm p).1).boundary_map (index.symm p).2 k
      intersection_frontier := fun p q hpq => (hcompat (index.symm p) (index.symm q)
        (fun h => hpq (index.symm.injective h))).2
      intersections := fun p q hpq => (hcompat (index.symm p) (index.symm q)
        (fun h => hpq (index.symm.injective h))).1
      cover := htotal }
  refine ⟨triangulation, ?_⟩
  intro q hq
  obtain ⟨p, k, hpk⟩ := hkeep q hq
  obtain ⟨v, hv⟩ := m64Intrinsic_coordinate_parent_corner_retained G d R p k
  obtain ⟨⟨s, j⟩, hsj⟩ := v.property
  refine ⟨Euler.coordinateCorner C basis (index s) j, ?_⟩
  change G (index.symm (index s)).1
    (meshTriangleBasis (R (index.symm (index s)).1).mesh (index.symm (index s)).2 j) = q
  rw [index.symm_apply_apply]
  exact hsj.trans (hv.trans hpk)

end PoincareMT
