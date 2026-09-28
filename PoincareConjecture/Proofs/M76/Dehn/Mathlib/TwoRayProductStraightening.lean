import PoincareConjecture.Proofs.M76.Wall.Mathlib.DistinctRayStraightening
import PoincareConjecture.Proofs.M76.Mathlib.PiecewiseAffineProd










set_option autoImplicit false

open Set Geometry

namespace ContinuousLinearMap



theorem exists_whole_two_ray_straightening
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {u v : E} (hu : u ≠ 0) (hv : v ≠ 0)
    (hne : ∀ t : ℝ, 0 < t → u ≠ t • v) :
    ∃ (w : E) (H : E ≃ₜ E), w ≠ 0 ∧
      H.toOpenPartialHomeomorph ∈ piecewiseAffineGroupoid E ∧ H 0 = 0 ∧
      ∀ x : E,
        ((∃ t : ℝ, 0 ≤ t ∧ x = t • u) ∨ (∃ t : ℝ, 0 ≤ t ∧ x = t • v)) ↔
          ∃ t : ℝ, H x = t • w := by
  obtain ⟨ell, w, huell, hvell, hwell, H, hPL, hzero, _, hnegative, hpositive⟩ :=
    exists_straightening_of_distinct_rays hu hv hne
  have hw : w ≠ 0 := by
    intro h
    have h01 : (0 : ℝ) = 1 := by simpa only [h, map_zero] using hwell
    exact zero_ne_one h01
  refine ⟨w, H, hw, hPL, hzero, ?_⟩
  intro x
  constructor
  · rintro (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
    · exact ⟨t * ell u, hnegative t ht⟩
    · exact ⟨t, hpositive t ht⟩
  · rintro ⟨t, ht⟩
    by_cases ht0 : 0 ≤ t
    · exact Or.inr ⟨t, ht0, H.injective (ht.trans (hpositive t ht0).symm)⟩
    · have htneg : t < 0 := lt_of_not_ge ht0
      have hquot : 0 ≤ t / ell u := div_nonneg_of_nonpos htneg.le huell.le
      have heq : (t / ell u) * ell u = t := div_mul_cancel₀ t (ne_of_lt huell)
      refine Or.inl ⟨t / ell u, hquot, H.injective ?_⟩
      rw [ht, hnegative _ hquot, heq]




theorem exists_whole_two_ray_product_straightening
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {u v : E} (hu : u ≠ 0) (hv : v ≠ 0)
    (hne : ∀ t : ℝ, 0 < t → u ≠ t • v) :
    ∃ (w : E) (H : (E × ℝ) ≃ₜ (E × ℝ)), w ≠ 0 ∧
      H.toOpenPartialHomeomorph ∈ piecewiseAffineGroupoid (E × ℝ) ∧ H 0 = 0 ∧
      (∀ x : E × ℝ, (H x).2 = x.2) ∧
      ∀ x : E × ℝ,
        ((∃ t : ℝ, 0 ≤ t ∧ x.1 = t • u) ∨
          (∃ t : ℝ, 0 ≤ t ∧ x.1 = t • v)) ↔
          ∃ t : ℝ, (H x).1 = t • w := by
  obtain ⟨w, F, hw, hFPL, hFzero, hwhole⟩ :=
    exists_whole_two_ray_straightening hu hv hne
  let H := F.prodCongr (Homeomorph.refl ℝ)
  refine ⟨w, H, hw, ?_, ?_, fun _ => rfl, fun x => hwhole x.1⟩
  · have hF : LocallyPiecewiseAffineOn F univ ∧
        LocallyPiecewiseAffineOn F.symm univ := hFPL
    have hid : LocallyPiecewiseAffineOn (id : ℝ → ℝ) univ :=
      locallyPiecewiseAffineOn_affine (ContinuousAffineMap.id ℝ ℝ) isOpen_univ
    constructor
    · change LocallyPiecewiseAffineOn (Prod.map F id) univ
      simpa only [univ_prod_univ] using hF.1.prodMap hid
    · change LocallyPiecewiseAffineOn (Prod.map F.symm id) univ
      simpa only [univ_prod_univ] using hF.2.prodMap hid
  · change (F 0, (0 : ℝ)) = 0
    rw [hFzero]
    rfl

end ContinuousLinearMap
