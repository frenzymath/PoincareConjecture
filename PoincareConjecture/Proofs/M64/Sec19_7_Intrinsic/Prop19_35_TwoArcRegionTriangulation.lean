import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_TwoArcParentConstruction
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RegionRefinementCorner












noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold Matrix
open PoincareConjecture.Topology.Surface Poincare.Topology.Plane.Meshes

namespace PoincareConjecture






theorem m64Intrinsic_exists_two_arc_region_triangulation
    {alpha beta : ℝ → AnnulusCoordinates} (ha : ContDiff ℝ ∞ alpha)
    (hb : ContDiff ℝ ∞ beta) {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hai : InjOn alpha (Icc 0 A)) (hbi : InjOn beta (Icc 0 B))
    (hareg : ∀ t ∈ Ioo (0 : ℝ) A, deriv alpha t ≠ 0)
    (hbreg : ∀ t ∈ Ioo (0 : ℝ) B, deriv beta t ≠ 0)
    (hinter : (alpha '' Icc 0 A) ∩ (beta '' Icc 0 B) ⊆ {alpha 0, alpha A})
    (hbase : beta 0 = alpha 0) (hend : beta B = alpha A)
    (hind0 : LinearIndependent ℝ
      (![deriv alpha 0, deriv beta 0] : Fin 2 → AnnulusCoordinates))
    (hind1 : LinearIndependent ℝ
      (![-deriv alpha A, -deriv beta B] : Fin 2 → AnnulusCoordinates))
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hdisj : Disjoint U V) (hfU : frontier U = alpha '' Icc 0 A ∪ beta '' Icc 0 B)
    (hfV : frontier V = frontier U) (hcompact : IsCompact (closure U)) :
    ∃ (m : ℕ) (face : Fin m → SmoothFace AnnulusCoordinates)
      (C : Fin m → OpenPartialHomeomorph Plane AnnulusCoordinates)
      (b : Fin m → AffineBasis (Fin 3) ℝ Plane),
      (∀ p, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (C p) (C p).source) ∧
      (∀ p, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (C p).symm (C p).target) ∧
      (∀ p, convexHull ℝ (range (b p)) ⊆ (C p).source) ∧
      (∀ p, (face p).carrier = C p '' convexHull ℝ (range (b p))) ∧
      (∀ p k, ((face p).boundary k).map = C p ∘
        affineChartSegment (b p (k.succAbove 0)) (b p (k.succAbove 1))) ∧
      (∀ p q, p ≠ q → (face p).carrier ∩ (face q).carrier ⊆ frontier (face p).carrier) ∧
      (∀ p q, p ≠ q →
        (∃ k l : Fin 3, (face p).carrier ∩ (face q).carrier =
          ((face p).boundary k).map '' Icc (0 : ℝ) 1 ∧
          ((face p).boundary k).map '' Icc (0 : ℝ) 1 =
            ((face q).boundary l).map '' Icc (0 : ℝ) 1) ∨
        ∃ v : Fin 3, (face p).carrier ∩ (face q).carrier ⊆ {C p (b p v)}) ∧
      (⋃ p, (face p).carrier) = closure U ∧
      ∃ v0 v1 : Euler.CoordinateVertex C b, v0.1 = alpha 0 ∧ v1.1 = alpha A := by
  classical
  obtain ⟨n, F, d, p0, p1, hF, hFi, hsource, hparents, hregion, hp0, hp1⟩ :=
    m64Intrinsic_exists_two_arc_region_coordinate_parents ha hb hA hB hai hbi hareg hbreg
      hinter hbase hend hind0 hind1 hU hV hdisj hfU hfV hcompact
  obtain ⟨marks, R, hcompat, hcover⟩ :=
    m64Intrinsic_exists_compatible_region_refinement F d hF hFi hsource hparents
  obtain ⟨q0, hq0⟩ := m64Intrinsic_coordinate_parent_corner_retained F d R p0 0
  obtain ⟨q1, hq1⟩ := m64Intrinsic_coordinate_parent_corner_retained F d R p1 0
  let Child := (i : Fin n) × (R i).mesh.Triangle
  let _ := Fintype.ofFinite Child
  let index := Fintype.equivFin Child
  let face (p : Fin (Fintype.card Child)) := (R (index.symm p).1).face (index.symm p).2
  let C (p : Fin (Fintype.card Child)) := F (index.symm p).1
  let b (p : Fin (Fintype.card Child)) :=
    meshTriangleBasis (R (index.symm p).1).mesh (index.symm p).2
  have hvertex (q : Euler.CoordinateVertex (fun s : Child => F s.1)
      (fun s => meshTriangleBasis (R s.1).mesh s.2)) :
      ∃ v : Euler.CoordinateVertex C b, v.1 = q.1 := by
    obtain ⟨⟨s, k⟩, hsk⟩ := q.property
    refine ⟨Euler.coordinateCorner C b (index s) k, ?_⟩
    change F (index.symm (index s)).1
      (meshTriangleBasis (R (index.symm (index s)).1).mesh
        (index.symm (index s)).2 k) = q.1
    rw [index.symm_apply_apply]
    exact hsk
  obtain ⟨v0, hv0⟩ := hvertex q0
  obtain ⟨v1, hv1⟩ := hvertex q1
  refine ⟨Fintype.card Child, face, C, b, fun p => hF _, fun p => hFi _,
    fun p => (R (index.symm p).1).source_subset (index.symm p).2,
    fun p => (R (index.symm p).1).carrier_eq (index.symm p).2,
    fun p k => (R (index.symm p).1).boundary_map (index.symm p).2 k, ?_, ?_, ?_,
    v0, v1, hv0.trans (hq0.trans hp0), hv1.trans (hq1.trans hp1)⟩
  · intro p q hpq
    exact (hcompat (index.symm p) (index.symm q)
      (fun h => hpq (index.symm.injective h))).2
  · intro p q hpq
    exact (hcompat (index.symm p) (index.symm q)
      (fun h => hpq (index.symm.injective h))).1
  · rw [← hregion, ← hcover]
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

end PoincareConjecture
