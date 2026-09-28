import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Regions.ProperArcPairNeighborhood



set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn

local notation "V" => (ℝ × ℝ)

theorem exists_lower_residual_wedge_bound
    (K : SimplicialComplex ℝ V) (hK : K.faces.Finite) {a b : V}
    (hab : a.1 < b.1) (ha : a.2 = 0) (hb : b.2 = 0)
    (hlower : ∀ x ∈ K.space, x.2 ≤ 0)
    (haxis : ∀ x ∈ K.space, x.2 = 0 → x = a ∨ x = b) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ C ≥ C₀, ∀ x ∈ K.space,
      (a.1 - x.1 ≤ C * x.2 ∧ x.1 - b.1 ≤ C * x.2) → x = a ∨ x = b := by
  classical
  have hv : K.vertices.Finite := hK.preimage Finset.singleton_injective.injOn
  let ratio (x : V) := (|a.1 - x.1| + |x.1 - b.1|) / (-x.2)
  obtain ⟨R, hR⟩ := (hv.image ratio).bddAbove
  let C₀ := max R 0 + 2
  refine ⟨C₀, by dsimp [C₀]; linarith [le_max_right R 0], ?_⟩
  intro C hC x hx hinside
  by_cases hxzero : x.2 = 0
  · exact haxis x hx hxzero
  have hxneg : x.2 < 0 := lt_of_le_of_ne (hlower x hx) hxzero
  have hvertex (y : V) (hy : y ∈ K.vertices) (hyneg : y.2 < 0) :
      0 < a.1 - y.1 - (C - 1) * y.2 ∧
        0 < y.1 - b.1 - (C - 1) * y.2 := by
    have hr := hR (mem_image_of_mem ratio hy)
    have hbound : |a.1 - y.1| + |y.1 - b.1| < (C - 1) * (-y.2) := by
      apply (div_lt_iff₀ (by linarith : 0 < -y.2)).mp
      change ratio y < C - 1
      apply hr.trans_lt
      dsimp [C₀] at hC
      linarith [le_max_left R 0]
    constructor <;> nlinarith [neg_abs_le (a.1 - y.1), neg_abs_le (y.1 - b.1),
      abs_nonneg (a.1 - y.1), abs_nonneg (y.1 - b.1)]
  obtain ⟨s, hs, hxs⟩ := SimplicialComplex.mem_space_iff.mp hx
  have hnotboth : ¬ (a ∈ s ∧ b ∈ s) := by
    rintro ⟨has, hbs⟩
    let m : V := (1 / 2 : ℝ) • a + (1 / 2 : ℝ) • b
    have hm : m ∈ convexHull ℝ (s : Set V) :=
      (convex_convexHull ℝ (s : Set V)) (subset_convexHull ℝ _ has)
        (subset_convexHull ℝ _ hbs) (by norm_num) (by norm_num) (by norm_num)
    have hmK : m ∈ K.space := SimplicialComplex.mem_space_iff.mpr ⟨s, hs, hm⟩
    have hmzero : m.2 = 0 := by simp [m, ha, hb]
    rcases haxis m hmK hmzero with hma | hmb
    · have hh := congrArg Prod.fst hma
      change (1 / 2 : ℝ) * a.1 + (1 / 2 : ℝ) * b.1 = a.1 at hh
      linarith
    · have hh := congrArg Prod.fst hmb
      change (1 / 2 : ℝ) * a.1 + (1 / 2 : ℝ) * b.1 = b.1 at hh
      linarith
  by_cases hbs : b ∈ s
  · have has : a ∉ s := fun has => hnotboth ⟨has, hbs⟩
    let L : V →ᵃ[ℝ] ℝ := (LinearMap.fst ℝ ℝ ℝ).toAffineMap -
      AffineMap.const ℝ V b.1 - (C - 1) • (LinearMap.snd ℝ ℝ ℝ).toAffineMap
    have hL : 0 ≤ L x := convexHull_min (fun y hy => by
      have hyK := K.vertices_subset_space (K.face_subset_vertices hs hy)
      by_cases hyzero : y.2 = 0
      · rcases haxis y hyK hyzero with hya | hyb
        · exact (has (hya ▸ hy)).elim
        · change 0 ≤ y.1 - b.1 - (C - 1) * y.2
          simp [hyb, hb]
      · exact (hvertex y (K.face_subset_vertices hs hy)
          (lt_of_le_of_ne (hlower y hyK) hyzero)).2.le)
      ((convex_Ici (0 : ℝ)).affine_preimage L) hxs
    change 0 ≤ x.1 - b.1 - (C - 1) * x.2 at hL
    nlinarith [hinside.2]
  · let L : V →ᵃ[ℝ] ℝ := AffineMap.const ℝ V a.1 -
      (LinearMap.fst ℝ ℝ ℝ).toAffineMap -
      (C - 1) • (LinearMap.snd ℝ ℝ ℝ).toAffineMap
    have hL : 0 ≤ L x := convexHull_min (fun y hy => by
      have hyK := K.vertices_subset_space (K.face_subset_vertices hs hy)
      by_cases hyzero : y.2 = 0
      · rcases haxis y hyK hyzero with hya | hyb
        · change 0 ≤ a.1 - y.1 - (C - 1) * y.2
          simp [hya, ha]
        · exact (hbs (hyb ▸ hy)).elim
      · exact (hvertex y (K.face_subset_vertices hs hy)
          (lt_of_le_of_ne (hlower y hyK) hyzero)).1.le)
      ((convex_Ici (0 : ℝ)).affine_preimage L) hxs
    change 0 ≤ a.1 - x.1 - (C - 1) * x.2 at hL
    nlinarith [hinside.1]

end PoincareConjecture.M76.Dehn
