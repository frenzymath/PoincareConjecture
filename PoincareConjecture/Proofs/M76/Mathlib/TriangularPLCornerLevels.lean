import PoincareConjecture.Proofs.M76.Mathlib.FinitePLSmallEndpointLevels
import PoincareConjecture.Proofs.M76.Mathlib.TriangularRoof










set_option autoImplicit false

open Set Geometry

namespace TriangularRoofModel




theorem frontier_base_eq_edges : frontier base =
    (segment ℝ (0, 0) (1, 0) ∪ segment ℝ (0, 0) (0, 1)) ∪
      segment ℝ (1, 0) (0, 1) := by
  have h : frontier base = segment ℝ (0, 0) (1, 0) ∪
      segment ℝ (1, 0) (0, 1) ∪ segment ℝ (0, 1) (0, 0) := by
    rw [base_eq_triangle,
      TriangleDiskModel.rightTriangle.frontier_convexHull_triangle
        TriangleDiskModel.independent_rightTriangle]
    ext x
    simp [Polygon.boundary, Polygon.edgeSet, TriangleDiskModel.rightTriangle,
      Fin.exists_fin_succ, affineSegment_eq_segment, or_assoc]
  rw [h, segment_symm ℝ ((0, 1) : ℝ × ℝ) (0, 0)]
  ac_rfl






theorem exists_small_corner_level_comparisons {f : (ℝ × ℝ) → ℝ}
    (hf : FinitePiecewiseAffineOn f (frontier base)) (hzero : f (0, 0) = 0)
    (hpos : ∀ p ∈ frontier base, p ≠ (0, 0) → 0 < f p) :
    ∃ m₁ m₂ η : ℝ, 0 < m₁ ∧ 0 < m₂ ∧ 0 < η ∧ η < min m₁ m₂ ∧
      ∀ c ∈ Icc 0 η, ∀ p ∈ frontier base,
        (f p ≤ c ↔ m₁ * p.1 + m₂ * p.2 ≤ c) ∧
        (f p = c ↔ m₁ * p.1 + m₂ * p.2 = c) ∧
        (c ≤ f p ↔ c ≤ m₁ * p.1 + m₂ * p.2) := by
  let ax : ℝ →ᴬ[ℝ] (ℝ × ℝ) :=
    (ContinuousAffineMap.id ℝ ℝ).prod (ContinuousAffineMap.const ℝ ℝ 0)
  let ay : ℝ →ᴬ[ℝ] (ℝ × ℝ) :=
    (ContinuousAffineMap.const ℝ ℝ 0).prod (ContinuousAffineMap.id ℝ ℝ)
  have hxseg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ax t ∈ segment ℝ (0, 0) (1, 0) := by
    simpa [ax, AffineMap.lineMap_apply_module'] using
      lineMap_mem_segment ℝ ((0, 0) : ℝ × ℝ) (1, 0) ht
  have hyseg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ay t ∈ segment ℝ (0, 0) (0, 1) := by
    simpa [ay, AffineMap.lineMap_apply_module'] using
      lineMap_mem_segment ℝ ((0, 0) : ℝ × ℝ) (0, 1) ht
  have hax : MapsTo ax (Icc (0 : ℝ) 1) (frontier base) := by
    intro t ht
    rw [frontier_base_eq_edges]
    exact Or.inl (Or.inl (hxseg t ht))
  have hay : MapsTo ay (Icc (0 : ℝ) 1) (frontier base) := by
    intro t ht
    rw [frontier_base_eq_edges]
    exact Or.inl (Or.inr (hyseg t ht))
  obtain ⟨η₁, hη₁, m₁, hm₁, hlevels₁⟩ := hf.exists_small_endpoint_levels ax hax hzero
    (fun t ht => hpos _ (hax ⟨ht.1.le, ht.2⟩)
      (fun h => ht.1.ne' (congrArg Prod.fst h)))
  obtain ⟨η₂, hη₂, m₂, hm₂, hlevels₂⟩ := hf.exists_small_endpoint_levels ay hay hzero
    (fun t ht => hpos _ (hay ⟨ht.1.le, ht.2⟩)
      (fun h => ht.1.ne' (congrArg Prod.snd h)))
  have hoff : segment ℝ ((1, 0) : ℝ × ℝ) (0, 1) ⊆ frontier base := by
    rw [frontier_base_eq_edges]
    exact subset_union_right
  have hoffsum (p : ℝ × ℝ) (hp : p ∈ segment ℝ (1, 0) (0, 1)) : p.1 + p.2 = 1 := by
    let L := LinearMap.fst ℝ ℝ ℝ + LinearMap.snd ℝ ℝ ℝ
    have hL : p ∈ {z | L z = 1} := convexHull_min
      (s := ({(1, 0), (0, 1)} : Set (ℝ × ℝ)))
      (by rintro z (rfl | rfl) <;> norm_num [L])
      ((convex_singleton (1 : ℝ)).linear_preimage L)
      (by simpa only [convexHull_pair] using hp)
    exact hL
  have hoffcompact : IsCompact (segment ℝ ((1, 0) : ℝ × ℝ) (0, 1)) := by
    rw [← convexHull_pair]
    exact ((finite_singleton ((0, 1) : ℝ × ℝ)).insert (1, 0)).isCompact_convexHull ℝ
  obtain ⟨b, hb, hbound⟩ := hoffcompact.exists_forall_le'
    (hf.continuousOn.mono hoff) (fun p hp => hpos p (hoff hp) (by
      intro h
      have hsum := hoffsum p hp
      rw [h] at hsum
      norm_num at hsum))
  let θ := min (min η₁ η₂) (min (min m₁ m₂) b)
  let η := θ / 2
  have hθ : 0 < θ := lt_min (lt_min hη₁ hη₂) (lt_min (lt_min hm₁ hm₂) hb)
  have hη : 0 < η := half_pos hθ
  have hηθ : η < θ := half_lt_self hθ
  have hη₁le : η ≤ η₁ := hηθ.le.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hη₂le : η ≤ η₂ := hηθ.le.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hηtop : η < min m₁ m₂ :=
    hηθ.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hηb : η < b := hηθ.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨m₁, m₂, η, hm₁, hm₂, hη, hηtop, fun c hc p hp => ?_⟩
  rw [frontier_base_eq_edges] at hp
  rcases hp with (hp | hp) | hp
  · rw [segment_eq_image_lineMap] at hp
    obtain ⟨t, ht, rfl⟩ := hp
    have hcmp := (hlevels₁ c ⟨hc.1, hc.2.trans hη₁le⟩).2 t ht
    have h := And.intro (hcmp.1.trans (le_div_iff₀ hm₁))
      (And.intro (hcmp.2.1.trans (eq_div_iff hm₁.ne')) (hcmp.2.2.trans (div_le_iff₀ hm₁)))
    simpa [ax, AffineMap.lineMap_apply_module', mul_comm] using h
  · rw [segment_eq_image_lineMap] at hp
    obtain ⟨t, ht, rfl⟩ := hp
    have hcmp := (hlevels₂ c ⟨hc.1, hc.2.trans hη₂le⟩).2 t ht
    have h := And.intro (hcmp.1.trans (le_div_iff₀ hm₂))
      (And.intro (hcmp.2.1.trans (eq_div_iff hm₂.ne')) (hcmp.2.2.trans (div_le_iff₀ hm₂)))
    simpa [ay, AffineMap.lineMap_apply_module', mul_comm] using h
  · let L := m₁ • LinearMap.fst ℝ ℝ ℝ + m₂ • LinearMap.snd ℝ ℝ ℝ
    have hL : min m₁ m₂ ≤ m₁ * p.1 + m₂ * p.2 := by
      have hpL : p ∈ {z | min m₁ m₂ ≤ L z} := convexHull_min
        (s := ({(1, 0), (0, 1)} : Set (ℝ × ℝ)))
        (by
          rintro z (rfl | rfl)
          · simp [L]
          · simp [L])
        ((convex_Ici (min m₁ m₂)).linear_preimage L)
        (by simpa only [convexHull_pair] using hp)
      exact hpL
    have hcf : c < f p := (hc.2.trans_lt hηb).trans_le (hbound p hp)
    have hcL : c < m₁ * p.1 + m₂ * p.2 := (hc.2.trans_lt hηtop).trans_le hL
    exact ⟨iff_of_false hcf.not_ge hcL.not_ge, iff_of_false hcf.ne' hcL.ne',
      iff_of_true hcf.le hcL.le⟩

end TriangularRoofModel
