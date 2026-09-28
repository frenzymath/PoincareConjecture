import PoincareConjecture.Proofs.M76.Mathlib.FiniteAffineHalfspaceGeometry










set_option autoImplicit false

open Set Geometry

namespace TaperedStrip




def domain (β : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ∈ Icc 0 1 ∧ p.2 ∈ Icc 0 (β * p.1)}



theorem convex_domain (β : ℝ) : Convex ℝ (domain β) := by
  let X := LinearMap.fst ℝ ℝ ℝ
  let Y := LinearMap.snd ℝ ℝ ℝ
  have h := ((convex_Icc (0 : ℝ) 1).linear_preimage X).inter
    (((convex_Ici (0 : ℝ)).linear_preimage Y).inter
      ((convex_Iic (0 : ℝ)).linear_preimage (Y - β • X)))
  have hset : domain β = X ⁻¹' Icc 0 1 ∩
      (Y ⁻¹' Ici 0 ∩ (Y - β • X) ⁻¹' Iic 0) := by
    ext p
    change (p.1 ∈ Icc 0 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ β * p.1) ↔
      (p.1 ∈ Icc 0 1 ∧ 0 ≤ p.2 ∧ p.2 - β * p.1 ≤ 0)
    rw [sub_nonpos]
  rw [hset]
  exact h




theorem domain_eq_convexHull {β : ℝ} (hβ : 0 < β) :
    domain β = convexHull ℝ (range ![((0, 0) : ℝ × ℝ), (1, 0), (1, β)]) := by
  apply Subset.antisymm
  · intro p hp
    have hfrac : p.2 / β ≤ p.1 := (div_le_iff₀ hβ).mpr (by
      simpa only [mul_comm] using hp.2.2)
    apply mem_convexHull_of_exists_fintype
      ![1 - p.1, p.1 - p.2 / β, p.2 / β] ![((0, 0) : ℝ × ℝ), (1, 0), (1, β)]
    · intro i
      fin_cases i
      · exact sub_nonneg.mpr hp.1.2
      · exact sub_nonneg.mpr hfrac
      · exact div_nonneg hp.2.1 hβ.le
    · simp [Fin.sum_univ_succ]
    · exact mem_range_self
    · apply Prod.ext
      · simp [Fin.sum_univ_succ]
      · simpa [Fin.sum_univ_succ] using (div_mul_cancel₀ p.2 hβ.ne')
  · apply convexHull_min ?_ (convex_domain β)
    rintro p ⟨i, rfl⟩
    fin_cases i <;> simp [domain, hβ.le]




theorem exists_finite_triangulation {β : ℝ} (hβ : 0 < β) :
    ∃ K : SimplicialComplex ℝ (ℝ × ℝ), K.faces.Finite ∧ K.space = domain β := by
  classical
  have hc : IsCompact (domain β) := by
    rw [domain_eq_convexHull hβ]
    exact (finite_range _).isCompact_convexHull ℝ
  let X := (LinearMap.fst ℝ ℝ ℝ).toAffineMap
  let Y := (LinearMap.snd ℝ ℝ ℝ).toAffineMap
  let C : (ℝ × ℝ) →ᵃ[ℝ] ℝ := AffineMap.const ℝ (ℝ × ℝ) 1
  apply hc.exists_finite_triangulation_of_halfspaces {-X, X - C, -Y, Y - β • X}
  ext p
  simp only [domain, mem_ofPred_eq, mem_Icc, Finset.mem_insert,
    Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  change ((0 ≤ p.1 ∧ p.1 ≤ 1) ∧ 0 ≤ p.2 ∧ p.2 ≤ β * p.1) ↔
    (-p.1 ≤ 0 ∧ p.1 - 1 ≤ 0 ∧ -p.2 ≤ 0 ∧ p.2 - β * p.1 ≤ 0)
  simp only [neg_nonpos, sub_nonpos]
  tauto

end TaperedStrip
