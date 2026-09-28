import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Mathlib.SquareAnnulusEulerCount
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseProductBall
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLIntervals

set_option autoImplicit false

open Set Metric Geometry Geometry.SimplicialComplex

namespace PoincareConjecture.M76.CompressionCylinder

abbrev Plane := Fin 2 → ℝ
abbrev Ambient := Plane × ℝ

def rectangle : Set (ℝ × ℝ) := Icc (-1 : ℝ) 1 ×ˢ Icc (-1 / 2 : ℝ) (1 / 2)

noncomputable def sideMap (i : Fin 4) : (ℝ × ℝ) →ᴬ[ℝ] Ambient := by
  let x := (LinearMap.fst ℝ ℝ ℝ).toAffineMap
  let t := (LinearMap.snd ℝ ℝ ℝ).toAffineMap
  let p := AffineMap.const ℝ (ℝ × ℝ) (1 : ℝ)
  let n := AffineMap.const ℝ (ℝ × ℝ) (-1 : ℝ)
  let f : Fin 4 → (ℝ × ℝ) →ᵃ[ℝ] Ambient :=
    ![(AffineMap.pi ![x, n]).prod t, (AffineMap.pi ![p, x]).prod t,
      (AffineMap.pi ![x, p]).prod t, (AffineMap.pi ![n, x]).prod t]
  exact ⟨f i, (f i).continuous_of_finiteDimensional⟩

def side (i : Fin 4) : Set Ambient := sideMap i '' rectangle

def carrier : Set Ambient :=
  sphere (0 : Plane) 1 ×ˢ Icc (-1 / 2 : ℝ) (1 / 2)

noncomputable def sidePlane (i : Fin 4) : AffineSubspace ℝ Ambient :=
  AffineSubspace.map (sideMap i).toAffineMap ⊤

theorem sidePlane_dim (i : Fin 4) :
    Module.finrank ℝ (sidePlane i).direction ≤ 2 := by
  rw [sidePlane, AffineSubspace.map_direction, AffineSubspace.direction_top]
  exact (Submodule.finrank_map_le _ _).trans (by simp [Module.finrank_prod])

theorem side_subset_plane (i : Fin 4) : side i ⊆ sidePlane i := by
  rintro _ ⟨x, _, rfl⟩
  exact AffineSubspace.mem_map.mpr ⟨x, by trivial, rfl⟩

theorem side_convex (i : Fin 4) : Convex ℝ (side i) :=
  ((convex_Icc (-1 : ℝ) 1).prod (convex_Icc (-1 / 2 : ℝ) (1 / 2))).affine_image
    (sideMap i).toAffineMap

theorem side_nonempty (i : Fin 4) : (side i).Nonempty := by
  exact ⟨sideMap i (0, 0), mem_image_of_mem _ (by norm_num [rectangle])⟩

theorem mem_side (i : Fin 4) (z : Ambient) : z ∈ side i ↔
    z.2 ∈ Icc (-1 / 2 : ℝ) (1 / 2) ∧
      ![z.1 1 = -1 ∧ z.1 0 ∈ Icc (-1) 1,
        z.1 0 = 1 ∧ z.1 1 ∈ Icc (-1) 1,
        z.1 1 = 1 ∧ z.1 0 ∈ Icc (-1) 1,
        z.1 0 = -1 ∧ z.1 1 ∈ Icc (-1) 1] i := by
  fin_cases i <;> constructor
  all_goals try
    (rintro ⟨p, hp, rfl⟩
     exact ⟨hp.2, rfl, hp.1⟩)
  all_goals
    rintro ⟨ht, hx, hy⟩
  · refine ⟨(z.1 0, z.2), ⟨hy, ht⟩, ?_⟩
    apply Prod.ext
    · ext j
      fin_cases j <;> simp [sideMap, hx]
    · rfl
  · refine ⟨(z.1 1, z.2), ⟨hy, ht⟩, ?_⟩
    apply Prod.ext
    · ext j
      fin_cases j <;> simp [sideMap, hx]
    · rfl
  · refine ⟨(z.1 0, z.2), ⟨hy, ht⟩, ?_⟩
    apply Prod.ext
    · ext j
      fin_cases j <;> simp [sideMap, hx]
    · rfl
  · refine ⟨(z.1 1, z.2), ⟨hy, ht⟩, ?_⟩
    apply Prod.ext
    · ext j
      fin_cases j <;> simp [sideMap, hx]
    · rfl

theorem iUnion_side : (⋃ i, side i) = carrier := by
  ext z
  constructor
  · intro hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp hz
    obtain ⟨ht, hi⟩ := (mem_side i z).mp hi
    refine ⟨mem_sphere_zero_iff_norm.mpr (le_antisymm ?_ ?_), ht⟩
    · apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
      intro j
      fin_cases i <;> fin_cases j <;>
        norm_num [Real.norm_eq_abs, abs_le] at hi ⊢ <;> aesop
    · fin_cases i
      · simpa [hi.1] using norm_le_pi_norm z.1 1
      · simpa [hi.1] using norm_le_pi_norm z.1 0
      · simpa [hi.1] using norm_le_pi_norm z.1 1
      · simpa [hi.1] using norm_le_pi_norm z.1 0
  · rintro ⟨hq, ht⟩
    have hn := mem_sphere_zero_iff_norm.mp hq
    have hbound (j : Fin 2) : z.1 j ∈ Icc (-1 : ℝ) 1 := by
      have h := norm_le_pi_norm z.1 j
      rw [hn, Real.norm_eq_abs, abs_le] at h
      exact h
    obtain ⟨j, hj⟩ := (IsGreatest.pi_norm z.1).1
    change ‖z.1 j‖ = ‖z.1‖ at hj
    rw [hn, Real.norm_eq_abs] at hj
    have heq : z.1 j = 1 ∨ z.1 j = -1 := (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp hj
    fin_cases j <;> rcases heq with heq | heq
    · exact mem_iUnion.mpr ⟨1, (mem_side 1 z).mpr ⟨ht, heq, hbound 1⟩⟩
    · exact mem_iUnion.mpr ⟨3, (mem_side 3 z).mpr ⟨ht, heq, hbound 1⟩⟩
    · exact mem_iUnion.mpr ⟨2, (mem_side 2 z).mpr ⟨ht, heq, hbound 0⟩⟩
    · exact mem_iUnion.mpr ⟨0, (mem_side 0 z).mpr ⟨ht, heq, hbound 0⟩⟩

theorem adjacent_intersections_nonempty :
    (side 0 ∩ side 1).Nonempty ∧ (side 2 ∩ side 3).Nonempty ∧
      (side 0 ∩ side 3).Nonempty ∧ (side 1 ∩ side 2).Nonempty := by
  refine ⟨⟨(![1, -1], 0), ?_⟩, ⟨(![-1, 1], 0), ?_⟩,
    ⟨(![-1, -1], 0), ?_⟩, ⟨(![1, 1], 0), ?_⟩⟩ <;>
    norm_num [mem_side] <;> trivial

theorem opposite_disjoint : Disjoint (side 0) (side 2) ∧
    Disjoint (side 1) (side 3) := by
  constructor
  · apply disjoint_left.mpr
    intro z hz₀ hz₂
    have h₀ := (mem_side 0 z).mp hz₀
    have h₂ := (mem_side 2 z).mp hz₂
    have h : z.1 1 = -1 := h₀.2.1
    have h' : z.1 1 = 1 := h₂.2.1
    linarith
  · apply disjoint_left.mpr
    intro z hz₁ hz₃
    have h₁ := (mem_side 1 z).mp hz₁
    have h₃ := (mem_side 3 z).mp hz₃
    have h : z.1 0 = 1 := h₁.2.1
    have h' : z.1 0 = -1 := h₃.2.1
    linarith

theorem exists_side_complex (i : Fin 4) :
    ∃ C : SimplicialComplex ℝ Ambient, C.faces.Finite ∧ C.space = side i := by
  have hrect := (isFinitePLBallPair_Icc (by norm_num : (-1 : ℝ) < 1)).prod
    (isFinitePLBallPair_Icc (by norm_num : (-1 / 2 : ℝ) < 1 / 2))
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨J, hJ, hJrect, _⟩, _⟩, _⟩ := hrect
  have hmap := (J.affineOnFaces_affine (sideMap i)).finitePiecewiseAffineOn hJ
  obtain ⟨C, hC, hCs⟩ := hmap.exists_finite_triangulation_image
  exact ⟨C, hC, hCs.trans (congrArg (fun U => sideMap i '' U) hJrect)⟩

theorem face_card_le_three (K : SimplicialComplex ℝ Ambient)
    (hK : K.space ⊆ carrier) : ∀ s ∈ K.faces, s.card ≤ 3 := by
  classical
  intro s hs
  apply K.face_card_le_of_finite_affine_cover
    (Finset.univ.image sidePlane) (d := 2) ?_ ?_ hs
  · intro P hP
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hP
    exact sidePlane_dim i
  · intro x hx
    have hc : x ∈ ⋃ i, side i := iUnion_side.symm ▸ hK hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hc
    exact ⟨sidePlane i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩,
      side_subset_plane i hi⟩

end PoincareConjecture.M76.CompressionCylinder
