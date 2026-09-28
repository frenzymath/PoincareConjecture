import PoincareConjecture.Proofs.M76.Mathlib.FinitePiecewiseAffine











set_option autoImplicit false

open Set
open scoped BigOperators

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]





theorem FinitePiecewiseAffineOn.exists_le_pos_mul
    {f g : E → ℝ} {S : Set E} (hf : FinitePiecewiseAffineOn f S)
    (hg : FinitePiecewiseAffineOn g S) (hgn : ∀ x ∈ S, 0 ≤ g x)
    (hzero : ∀ x ∈ S, g x = 0 → f x ≤ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ S, f x ≤ C * g x := by
  classical
  obtain ⟨K, hK, hKs, hKf⟩ := hf
  obtain ⟨L, hL, hLs, hLg⟩ := hg
  obtain ⟨R, hR, hRK, hRL⟩ := K.exists_common_finite_subdivision L hK hL
    (hKs.trans hLs.symm)
  have hRs : R.space = S := hRK.space_eq.trans hKs
  have hRf := hRK.affineOnFaces hKf
  have hRg := hRL.affineOnFaces hLg
  let V := hR.toFinset.biUnion id
  let M : ℝ := ∑ v ∈ V, max (f v / g v) 0
  have hM : 0 ≤ M := Finset.sum_nonneg (fun _ _ => le_max_right _ _)
  have hratio (v : E) (hv : v ∈ V) : f v / g v ≤ 1 + M := by
    have hm : max (f v / g v) 0 ≤ M :=
      Finset.single_le_sum (f := fun v => max (f v / g v) 0)
        (fun _ _ => le_max_right _ _) hv
    exact (le_max_left _ _).trans (hm.trans (by linarith))
  have hvert (v : E) (hv : v ∈ V) (hvS : v ∈ S) : f v ≤ (1 + M) * g v := by
    by_cases hgv : g v = 0
    · rw [hgv, mul_zero]
      exact hzero v hvS hgv
    · exact (div_le_iff₀ (lt_of_le_of_ne (hgn v hvS) (Ne.symm hgv))).mp (hratio v hv)
  refine ⟨1 + M, by linarith, fun x hx => ?_⟩
  obtain ⟨s, hs, hxs⟩ := SimplicialComplex.mem_space_iff.mp (hRs.symm.subset hx)
  obtain ⟨a, ha⟩ := hRf s hs
  obtain ⟨b, hb⟩ := hRg s hs
  let A : E →ᵃ[ℝ] ℝ := a.toAffineMap - (1 + M) • b.toAffineMap
  have hA (v : E) (hv : v ∈ s) : A v ≤ 0 := by
    have hvV : v ∈ V := Finset.mem_biUnion.mpr ⟨s, hR.mem_toFinset.mpr hs, hv⟩
    have hvS : v ∈ S := hRs.subset (R.subset_space hs hv)
    have hvh := subset_convexHull ℝ (s : Set E) hv
    change a v - (1 + M) * b v ≤ 0
    rw [← ha hvh, ← hb hvh]
    exact sub_nonpos.mpr (hvert v hvV hvS)
  have hxA : A x ≤ 0 := convexHull_min hA ((convex_Iic (0 : ℝ)).affine_preimage A) hxs
  change a x - (1 + M) * b x ≤ 0 at hxA
  rw [← ha hxs, ← hb hxs] at hxA
  exact sub_nonpos.mp hxA





theorem FinitePiecewiseAffineOn.exists_small_mul_lt_of_pos
    {f g : E → ℝ} {S : Set E} (hf : FinitePiecewiseAffineOn f S)
    (hg : FinitePiecewiseAffineOn g S) (hgn : ∀ x ∈ S, 0 ≤ g x)
    (hzero : ∀ x ∈ S, g x = 0 → f x ≤ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t ∈ Icc 0 ε, ∀ x ∈ S, 0 < g x → t * f x < g x := by
  obtain ⟨C, hC, hbound⟩ := hf.exists_le_pos_mul hg hgn hzero
  let ε := 1 / (C + 1)
  have hε : 0 < ε := one_div_pos.mpr (by linarith)
  have hεC : ε * C < 1 := by
    have heq : ε * C = C / (C + 1) := by dsimp [ε]; ring
    rw [heq]
    exact (div_lt_one (by linarith : 0 < C + 1)).mpr (by linarith)
  refine ⟨ε, hε, fun t ht x hx hgx => ?_⟩
  have htC : t * C < 1 :=
    (mul_le_mul_of_nonneg_right ht.2 hC.le).trans_lt hεC
  calc
    t * f x ≤ t * (C * g x) := mul_le_mul_of_nonneg_left (hbound x hx) ht.1
    _ = (t * C) * g x := (mul_assoc _ _ _).symm
    _ < 1 * g x := mul_lt_mul_of_pos_right htC hgx
    _ = g x := one_mul _

end Geometry
