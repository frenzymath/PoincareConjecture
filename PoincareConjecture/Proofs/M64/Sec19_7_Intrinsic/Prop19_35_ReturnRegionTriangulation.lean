import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ReturnParentConstruction

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold Matrix
open PoincareConjecture.Topology.Surface Poincare.Topology.Plane.Meshes

namespace PoincareConjecture

theorem m64Intrinsic_exists_return_region_triangulation
    {gamma : ℝ → AnnulusCoordinates} (hg : ContDiff ℝ ∞ gamma) {T : ℝ} (hT : 0 < T)
    (hend : gamma 0 = gamma T) (hinj : InjOn gamma (Ico 0 T))
    (hregular : ∀ t ∈ Ioo (0 : ℝ) T, deriv gamma t ≠ 0)
    (hind : LinearIndependent ℝ
      (![deriv gamma 0, -deriv gamma T] : Fin 2 → AnnulusCoordinates))
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hdisj : Disjoint U V) (hfU : frontier U = gamma '' Icc 0 T)
    (hfV : frontier V = gamma '' Icc 0 T) (hcompact : IsCompact (closure U))
    (hray : ∀ t ∈ Ioo (0 : ℝ) T, ∀ᶠ z in 𝓝[>] (0 : ℝ),
      gamma t + z • Poincare.Topology.Plane.Curves.quarterTurn (deriv gamma t) ∈ U) :
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
      (⋃ p, (face p).carrier) = closure U := by
  classical
  obtain ⟨n, F, d, hF, hFi, hsource, hparents, hregion⟩ :=
    m64Intrinsic_exists_return_region_coordinate_parents hg hT hend hinj hregular hind
      hU hV hdisj hfU hfV hcompact hray
  obtain ⟨marks, R, hinter, hcover⟩ :=
    m64Intrinsic_exists_compatible_region_refinement F d hF hFi hsource hparents
  let A := (i : Fin n) × (R i).mesh.Triangle
  let _ := Fintype.ofFinite A
  let index := Fintype.equivFin A
  let face (p : Fin (Fintype.card A)) := (R (index.symm p).1).face (index.symm p).2
  let C (p : Fin (Fintype.card A)) := F (index.symm p).1
  let b (p : Fin (Fintype.card A)) :=
    meshTriangleBasis (R (index.symm p).1).mesh (index.symm p).2
  refine ⟨Fintype.card A, face, C, b, fun p => hF _, fun p => hFi _,
    fun p => (R (index.symm p).1).source_subset (index.symm p).2,
    fun p => (R (index.symm p).1).carrier_eq (index.symm p).2,
    fun p k => (R (index.symm p).1).boundary_map (index.symm p).2 k, ?_, ?_, ?_⟩
  · intro p q hpq
    exact (hinter (index.symm p) (index.symm q)
      (fun h => hpq (index.symm.injective h))).2
  · intro p q hpq
    exact (hinter (index.symm p) (index.symm q)
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
