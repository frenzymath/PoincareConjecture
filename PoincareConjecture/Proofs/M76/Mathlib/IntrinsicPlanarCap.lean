import PoincareConjecture.Proofs.M76.Mathlib.AffineTouchingPolygonDisk
import PoincareConjecture.Proofs.M76.Mathlib.AffineHyperplaneCoordinates
import PoincareConjecture.Proofs.M76.Mathlib.PolygonSliceCoordinates
import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedralUnions

set_option autoImplicit false

open Set Geometry

namespace Polygon

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Finite ι] [Nonempty ι]

theorem exists_intrinsic_plane_cap
    (hdim : Module.finrank ℝ E = 3) (A : E →ᵃ[ℝ] ℝ) (hA : A.linear ≠ 0)
    (n : ι → ℕ) (P : ∀ i, Polygon E (n i + 3))
    (hP : ∀ i, Function.Injective (P i) ∧ (P i).HasSimplicialEdges)
    (q : E) (hpair : Pairwise (fun i j =>
      (P i).boundary ℝ ∩ (P j).boundary ℝ ⊆ {q}))
    (S : Set E) (hsection : S ∩ {x | A x = 0} = ⋃ i, (P i).boundary ℝ) :
    ∃ (j : ι) (d : Set E) (N : SimplicialComplex ℝ E),
      IsFinitePLBallPair (ℝ × ℝ) d ((P j).boundary ℝ) ∧
      d ⊆ {x | A x = 0} ∧ d ∩ S = (P j).boundary ℝ ∧
      N.faces.Finite ∧ S ∩ {x | A x = 0} = (P j).boundary ℝ ∪ N.space ∧
      d ∩ N.space ⊆ {q} ∧
      N.space = ⋃ i : {i : ι // i ≠ j}, (P i.val).boundary ℝ := by
  classical
  obtain ⟨a, r, hleft, hright, ha⟩ := A.exists_zeroLevel_coordinates hA
    (F := ℝ × ℝ) (by simp [hdim, Module.finrank_prod])
  have hplane (i : ι) : (P i).boundary ℝ ⊆ {x | A x = 0} :=
    fun _ hx => (hsection.symm.subset (mem_iUnion.mpr ⟨i, hx⟩)).2
  let Q := fun i => (P i).affineImage r.toAffineMap
  have hQ (i : ι) : Function.Injective (Q i) ∧ (Q i).HasSimplicialEdges ∧
      a '' (Q i).boundary ℝ = (P i).boundary ℝ :=
    (P i).affineImage_of_leftInvOn (hP i).2 (hP i).1 r.toAffineMap a.toAffineMap
      (fun x hx => hright (hplane i hx))
  have hsectionQ : a ⁻¹' S = ⋃ i, (Q i).boundary ℝ := by
    ext y
    constructor
    · intro hy
      obtain ⟨i, hi⟩ := mem_iUnion.mp (hsection.subset ⟨hy, ha y⟩)
      rw [← (hQ i).2.2] at hi
      obtain ⟨z, hz, hzy⟩ := hi
      exact mem_iUnion.mpr ⟨i, hleft.injective hzy ▸ hz⟩
    · intro hy
      obtain ⟨i, hi⟩ := mem_iUnion.mp hy
      have hai : a y ∈ (P i).boundary ℝ := (hQ i).2.2.subset ⟨y, hi, rfl⟩
      exact (hsection.symm.subset (mem_iUnion.mpr ⟨i, hai⟩)).1
  have hpairQ : Pairwise (fun i j =>
      (Q i).boundary ℝ ∩ (Q j).boundary ℝ ⊆ {r q}) := by
    intro i j hij y hy
    have hayq : a y = q := hpair hij
      ⟨(hQ i).2.2.subset ⟨y, hy.1, rfl⟩, (hQ j).2.2.subset ⟨y, hy.2, rfl⟩⟩
    change y = r q
    rw [← hleft y, hayq]
  obtain ⟨j, _, hd, _, _, hmeet, _⟩ :=
    exists_innermost_affine_disk_of_singleton_inter n Q
      (fun i => (hQ i).2.1) (fun i => (hQ i).1) (r q) hpairQ
      a hleft.injective S hsectionQ
  rw [(hQ j).2.2] at hd hmeet
  obtain ⟨N, hN, hNspace, _⟩ := SimplicialComplex.exists_finite_triangulation_iUnion
    (fun i : {i : ι // i ≠ j} => (P i.val).simplicialComplex (hP i.val).2)
    (fun i => (P i.val).finite_simplicialComplex_faces (hP i.val).2)
  simp only [Polygon.simplicialComplex_space] at hNspace
  refine ⟨j, a '' closure (Q j).inside, N, hd, ?_, hmeet, hN, ?_, ?_, hNspace⟩
  · rintro _ ⟨y, _, rfl⟩
    exact ha y
  · rw [hsection, hNspace]
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      by_cases hij : i = j
      · exact Or.inl (hij ▸ hi)
      · exact Or.inr (mem_iUnion.mpr ⟨⟨i, hij⟩, hi⟩)
    · rintro (hx | hx)
      · exact mem_iUnion.mpr ⟨j, hx⟩
      · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
        exact mem_iUnion.mpr ⟨i.val, hi⟩
  · rintro x ⟨hxd, hxN⟩
    rw [hNspace] at hxN
    obtain ⟨i, hi⟩ := mem_iUnion.mp hxN
    have hxS : x ∈ S := (hsection.symm.subset (mem_iUnion.mpr ⟨i.val, hi⟩)).1
    exact hpair (Ne.symm i.property) ⟨hmeet.subset ⟨hxd, hxS⟩, hi⟩

end Polygon
