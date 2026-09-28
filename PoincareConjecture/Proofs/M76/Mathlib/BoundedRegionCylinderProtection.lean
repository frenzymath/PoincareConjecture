import PoincareConjecture.Proofs.M76.Mathlib.ConvexFrontierSubcomplex
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseProductTriangulation
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLIntervals












set_option autoImplicit false

open Set Geometry

namespace Set

variable {E : Type*} [TopologicalSpace E]




theorem cylinder_frontier_sdiff_top_interior {D : Set E} (hD : IsClosed D) :
    frontier (D ×ˢ Icc (-1 : ℝ) 1) \ interior D ×ˢ {1} =
      (D ×ˢ {-1}) ∪ (frontier D ×ˢ Icc (-1 : ℝ) 1) := by
  rw [frontier_prod_eq, hD.closure_eq, isClosed_Icc.closure_eq,
    frontier_Icc (by norm_num : (-1 : ℝ) ≤ 1)]
  ext p
  constructor
  · rintro ⟨hp, hpnot⟩
    rcases hp with ⟨hpD, hpt⟩ | hpside
    · have hpt' : p.2 = -1 ∨ p.2 = 1 := by
        simpa only [mem_insert_iff, mem_singleton_iff] using hpt
      rcases hpt' with ht | ht
      · exact Or.inl ⟨hpD, ht⟩
      · exact Or.inr ⟨⟨subset_closure hpD, fun hi => hpnot ⟨hi, ht⟩⟩,
          by rw [ht]; constructor <;> norm_num⟩
    · exact Or.inr hpside
  · intro hp
    rcases hp with ⟨hpD, hpt⟩ | hpside
    · have ht : p.2 = -1 := hpt
      refine ⟨Or.inl ⟨hpD, ?_⟩, ?_⟩
      · simp only [ht, mem_insert_iff, mem_singleton_iff, true_or]
      · intro hi
        have htop : p.2 = 1 := hi.2
        linarith
    · exact ⟨Or.inr hpside, fun hi => hpside.1.2 hi.1⟩

end Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]




theorem exists_finite_triangulation_cylinder_nonTop
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {D : Set E} (hD : IsCompact D) (hcv : Convex ℝ D)
    (hne : (interior D).Nonempty) (hKD : K.space = D) :
    ∃ L : SimplicialComplex ℝ (E × ℝ), L.faces.Finite ∧
      L.space = frontier (D ×ˢ Icc (-1 : ℝ) 1) \ interior D ×ˢ {1} := by
  let a : E →ᴬ[ℝ] E × ℝ :=
    (ContinuousAffineMap.id ℝ E).prod (ContinuousAffineMap.const ℝ E (-1))
  have ha : Function.Injective a := fun _ _ h => congrArg Prod.fst h
  have hKa := K.affineOnFaces_affine a
  let B := hKa.embeddedImage ha.injOn
  have hB : B.faces.Finite := hKa.embeddedImage_finite ha.injOn hK
  have hBD : B.space = D ×ˢ {(-1 : ℝ)} := by
    rw [hKa.embeddedImage_space, hKD]
    exact (prod_singleton (s := D) (b := (-1 : ℝ))).symm
  let J := K.frontierSubcomplex D
  have hJ : J.faces.Finite := K.frontierSubcomplex_finite D hK
  have hJD : J.space = frontier D := K.frontierSubcomplex_space hD.isClosed hcv hne hKD
  have hinterval := isFinitePLBallPair_Icc (by norm_num : (-1 : ℝ) < 1)
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨R, hR, hRI, _⟩, _⟩, _⟩ := hinterval
  obtain ⟨C, hC, hCs, _⟩ := J.exists_finite_triangulation_prod R hJ hR
  rw [hJD, hRI] at hCs
  obtain ⟨L, hL, hLs⟩ := B.exists_finite_triangulation_union C hB hC
  refine ⟨L, hL, ?_⟩
  rw [hLs, hBD, hCs, cylinder_frontier_sdiff_top_interior hD.isClosed]

end Geometry.SimplicialComplex
