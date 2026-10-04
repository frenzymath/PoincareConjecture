import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Polygons.TaperedTriangleDomain

/-!
# The residual triangle beside a tapered collar

The truncated original triangle is the union of its tapered
collar and an explicit residual triangle, meeting exactly
along the collar's upper edge. See Alexander 1924, p. 8,
Hudson 1969, pp. 12--19 and M76 derivation 201.
-/

set_option autoImplicit false

open Set Geometry

namespace TaperedStrip

/-- The closed residual region beside a collar of width beta
in a triangle of height gamma. The geometric triangular use
assumes `0 < beta < gamma`. See M76 derivation 201. -/
def residualDomain (β γ : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ∈ Icc 0 1 ∧ p.2 ∈ Icc (β * p.1) β ∧ p.2 ≤ γ * p.1}

/-- The residual region is an intersection of affine
halfspaces, hence convex. See M76 derivation 201. -/
theorem convex_residualDomain (β γ : ℝ) : Convex ℝ (residualDomain β γ) := by
  let X := LinearMap.fst ℝ ℝ ℝ
  let Y := LinearMap.snd ℝ ℝ ℝ
  have h := ((convex_Icc (0 : ℝ) 1).linear_preimage X).inter
    (((convex_Ici (0 : ℝ)).linear_preimage (Y - β • X)).inter
      (((convex_Iic β).linear_preimage Y).inter
        ((convex_Iic (0 : ℝ)).linear_preimage (Y - γ • X))))
  have hset : residualDomain β γ = X ⁻¹' Icc 0 1 ∩
      ((Y - β • X) ⁻¹' Ici 0 ∩ (Y ⁻¹' Iic β ∩ (Y - γ • X) ⁻¹' Iic 0)) := by
    ext p
    change ((p.1 ∈ Icc 0 1) ∧ (β * p.1 ≤ p.2 ∧ p.2 ≤ β) ∧ p.2 ≤ γ * p.1) ↔
      (p.1 ∈ Icc 0 1 ∧ 0 ≤ p.2 - β * p.1 ∧ p.2 ≤ β ∧ p.2 - γ * p.1 ≤ 0)
    simp only [sub_nonneg, sub_nonpos]
    tauto
  rw [hset]
  exact h

/-- The actual truncated triangle is covered by the collar
and its closed residual region, including every boundary.
See Alexander p. 8 and M76 derivation 201. -/
theorem slab_eq_domain_union_residual {β γ : ℝ} (hβ : 0 ≤ β) (hβγ : β ≤ γ) :
    domain γ ∩ {p : ℝ × ℝ | p.2 ≤ β} = domain β ∪ residualDomain β γ := by
  ext p
  constructor
  · rintro ⟨hp, ht⟩
    by_cases hc : p.2 ≤ β * p.1
    · exact Or.inl ⟨hp.1, hp.2.1, hc⟩
    · exact Or.inr ⟨hp.1, ⟨le_of_not_ge hc, ht⟩, hp.2.2⟩
  · rintro (hp | hp)
    · refine ⟨⟨hp.1, hp.2.1, hp.2.2.trans
        (mul_le_mul_of_nonneg_right hβγ hp.1.1)⟩, ?_⟩
      exact hp.2.2.trans (by simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hp.1.2 hβ)
    · exact ⟨⟨hp.1, (mul_nonneg hβ hp.1.1).trans hp.2.1.1, hp.2.2⟩, hp.2.1.2⟩

/-- Collar and residual region meet exactly along the full
upper edge, with the collapsed corner included.
See Alexander p. 8 and M76 derivation 201. -/
theorem domain_inter_residual {β γ : ℝ} (hβ : 0 ≤ β) (hβγ : β ≤ γ) :
    domain β ∩ residualDomain β γ = segment ℝ ((0, 0) : ℝ × ℝ) (1, β) := by
  have hline (s : ℝ) : AffineMap.lineMap ((0, 0) : ℝ × ℝ) (1, β) s = (s, β * s) := by
    apply Prod.ext <;> simp [AffineMap.lineMap_apply_module', mul_comm]
  ext p
  rw [segment_eq_image_lineMap]
  constructor
  · rintro ⟨hp, hr⟩
    have ht : p.2 = β * p.1 := le_antisymm hp.2.2 hr.2.1.1
    exact ⟨p.1, hp.1, (hline p.1).trans (Prod.ext rfl ht.symm)⟩
  · rintro ⟨s, hs, rfl⟩
    rw [hline]
    refine ⟨⟨hs, mul_nonneg hβ hs.1, le_rfl⟩, hs, ⟨le_rfl, ?_⟩, ?_⟩
    · simpa only [mul_one] using mul_le_mul_of_nonneg_left hs.2 hβ
    · exact mul_le_mul_of_nonneg_right hβγ hs.1

/-- For distinct positive collar and original heights, the
residual region is exactly the triangle whose top side joins
the two original height-beta crossings. See M76 derivation 201. -/
theorem residualDomain_eq_convexHull {β γ : ℝ} (hβ : 0 < β) (hβγ : β < γ) :
    residualDomain β γ =
      convexHull ℝ (range ![((0, 0) : ℝ × ℝ), (1, β), (β / γ, β)]) := by
  have hγ : 0 < γ := hβ.trans hβγ
  have hgap : 0 < γ - β := sub_pos.mpr hβγ
  apply Subset.antisymm
  · intro p hp
    apply mem_convexHull_of_exists_fintype
      ![1 - p.2 / β, (γ * p.1 - p.2) / (γ - β),
        γ * (p.2 - β * p.1) / (β * (γ - β))]
      ![((0, 0) : ℝ × ℝ), (1, β), (β / γ, β)]
    · intro i
      fin_cases i
      · exact sub_nonneg.mpr ((div_le_one hβ).mpr hp.2.1.2)
      · exact div_nonneg (sub_nonneg.mpr hp.2.2) hgap.le
      · exact div_nonneg (mul_nonneg hγ.le (sub_nonneg.mpr hp.2.1.1))
          (mul_nonneg hβ.le hgap.le)
    · simp [Fin.sum_univ_succ]
      field_simp [hβ.ne', hγ.ne', hgap.ne']
      ring
    · exact mem_range_self
    · apply Prod.ext <;> simp [Fin.sum_univ_succ] <;>
        field_simp [hβ.ne', hγ.ne', hgap.ne'] <;> ring
  · apply convexHull_min ?_ (convex_residualDomain β γ)
    rintro p ⟨i, rfl⟩
    fin_cases i
    · simp [residualDomain, hβ.le]
    · simp [residualDomain, hβγ.le]
    · have hfrac : β / γ ≤ 1 := (div_le_one hγ).mpr hβγ.le
      change (β / γ, β) ∈ residualDomain β γ
      refine ⟨⟨div_nonneg hβ.le hγ.le, hfrac⟩, ⟨?_, le_rfl⟩, ?_⟩
      · simpa only [mul_one] using mul_le_mul_of_nonneg_left hfrac hβ.le
      · have heq : γ * (β / γ) = β := by field_simp
        rw [heq]

end TaperedStrip
