import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Polygons.FinitePLReturningBigon

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn

local notation "V" => (ℝ × ℝ)

theorem exists_finitePL_returning_disk_above_level
    {W C : Set V} {a b : V} {c : ℝ}
    (hW : IsFinitePLBallPair ℝ W {a, b}) (hab : a ≠ b)
    (hup : ∀ x ∈ W, c ≤ x.2) (haxis : W ∩ {x | x.2 = c} = {a, b})
    (hC : Convex ℝ C) (hWC : W ⊆ C) :
    ∃ B : Set V, IsFinitePLBallPair V B (W ∪ segment ℝ a b) ∧
      IsCompact B ∧ B ⊆ C ∧ B ∩ {x | x.2 = c} = segment ℝ a b := by
  let A : V ≃ᴬ[ℝ] V := ContinuousAffineEquiv.constVAdd ℝ V (0, -c)
  have hA (x : V) : (A x).2 = x.2 - c := by change -c + x.2 = x.2 - c; ring
  have hpair : IsFinitePLBallPair ℝ (A '' W) {A a, A b} := by
    simpa only [ContinuousAffineEquiv.coe_toContinuousAffineMap, image_pair] using
      hW.affine_image A.toContinuousAffineMap A.injective.injOn
  have haxisA : (A '' W) ∩ {x : V | x.2 = 0} = {A a, A b} := by
    apply Subset.antisymm
    · rintro y ⟨⟨x, hx, rfl⟩, hx0⟩
      change (A x).2 = 0 at hx0
      rw [hA] at hx0
      have he := haxis.subset ⟨hx, sub_eq_zero.mp hx0⟩
      exact image_pair A a b ▸ mem_image_of_mem A he
    · rintro y (rfl | rfl)
      · have hh := haxis.symm.subset (show a ∈ ({a, b} : Set V) by simp)
        refine ⟨mem_image_of_mem A hh.1, ?_⟩
        change (A a).2 = 0
        rw [hA, hh.2, sub_self]
      · have hh := haxis.symm.subset (show b ∈ ({a, b} : Set V) by simp)
        refine ⟨mem_image_of_mem A hh.1, ?_⟩
        change (A b).2 = 0
        rw [hA, hh.2, sub_self]
  obtain ⟨n, P, _, _, _, _, hB, hcompact, hbase, hcontain⟩ :=
    exists_finite_pl_returning_bigon hpair (fun h => hab (A.injective h))
      (by rintro y ⟨x, hx, rfl⟩; rw [hA]; exact sub_nonneg.mpr (hup x hx)) haxisA
  have hBsub : closure P.inside ⊆ A '' C :=
    hcontain (A '' C) (hC.affine_image A.toAffineEquiv.toAffineMap) (image_mono hWC)
  have hwinverse : A.symm '' (A '' W) = W := by
    ext x
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      simpa using hz
    · intro hx
      exact ⟨A x, mem_image_of_mem A hx, A.symm_apply_apply x⟩
  have hseginverse : A.symm '' segment ℝ (A a) (A b) = segment ℝ a b := by
    simpa using image_segment ℝ A.symm.toAffineEquiv.toAffineMap (A a) (A b)
  have hball : IsFinitePLBallPair V (A.symm '' closure P.inside) (W ∪ segment ℝ a b) := by
    have hh := hB.affine_image A.symm.toContinuousAffineMap A.symm.injective.injOn
    simp only [ContinuousAffineEquiv.coe_toContinuousAffineMap] at hh
    rwa [image_union, hwinverse, hseginverse] at hh
  refine ⟨A.symm '' closure P.inside, hball, hcompact.image A.symm.continuous, ?_, ?_⟩
  · rintro x ⟨y, hy, rfl⟩
    obtain ⟨z, hz, rfl⟩ := hBsub hy
    simpa using hz
  · apply Subset.antisymm
    · rintro x ⟨⟨y, hy, rfl⟩, hxc⟩
      have hy0 : y.2 = 0 := by
        have hh := hA (A.symm y)
        rw [A.apply_symm_apply, hxc, sub_self] at hh
        exact hh
      have hys := hbase.subset ⟨hy, hy0⟩
      exact hseginverse ▸ mem_image_of_mem A.symm hys
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := hseginverse.symm.subset hx
      have hyB := hbase.symm.subset hy
      refine ⟨mem_image_of_mem A.symm hyB.1, ?_⟩
      have hh := hA (A.symm y)
      rw [A.apply_symm_apply, show y.2 = 0 from hyB.2] at hh
      exact (sub_eq_zero.mp hh.symm)

end PoincareConjecture.M76.Dehn
