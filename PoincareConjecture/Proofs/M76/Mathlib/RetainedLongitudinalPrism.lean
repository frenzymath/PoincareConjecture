import PoincareConjecture.Proofs.M76.Mathlib.FinitePLInterior
import Mathlib.Analysis.Convex.Join
import Mathlib.Topology.MetricSpace.Thickening












set_option autoImplicit false

open Set Geometry

namespace Homeomorph

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]





theorem IsFinitePL.smul_linear_cut_mem_interior
    {S : Set E} {T : Set F} {e : S ≃ₜ T} (he : e.IsFinitePL)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F)
    (hcv : Convex ℝ S) (hzero : (0 : E) ∈ interior S)
    {Q : Set E} {p a : E} (hpS : p ∈ S) (hpQ : p ∈ Q)
    {ρ : ℝ} (hρ : 1 < ρ) (hpa : p = ρ • a)
    (L : E →ₗ[ℝ] F)
    (hkeep : ∀ x : S, (x : E) ∈ convexJoin ℝ {0} Q → (e x : F) = L x)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : t • L a ∈ interior T := by
  have hρpos : 0 < ρ := zero_lt_one.trans hρ
  let c : ℝ := t / ρ
  have hc0 : 0 ≤ c := div_nonneg ht.1 hρpos.le
  have hc1 : c < 1 := (div_lt_one hρpos).mpr (ht.2.trans_lt hρ)
  have hxint : c • p ∈ interior S := by
    simpa only [smul_zero, zero_add] using
      hcv.combo_interior_self_mem_interior hzero hpS
        (sub_pos.mpr hc1) hc0 (sub_add_cancel 1 c)
  have hxcone : c • p ∈ convexJoin ℝ {0} Q := by
    apply segment_subset_convexJoin (mem_singleton (0 : E)) hpQ
    exact ⟨1 - c, c, sub_nonneg.mpr hc1.le, hc0, sub_add_cancel 1 c, by simp⟩
  have hxval : c • p = t • a := by
    change (t / ρ) • p = t • a
    rw [hpa, smul_smul, div_mul_cancel₀ _ hρpos.ne']
  have hmap : (e ⟨c • p, interior_subset hxint⟩ : F) = t • L a :=
    (hkeep _ hxcone).trans (by
      change L (c • p) = t • L a
      rw [hxval, map_smul])
  exact hmap ▸ he.mem_interior hdim hxint





theorem IsFinitePL.longitudinal_axis_mem_interior_of_linear_cones
    {S : Set E} {T : Set ((ℝ × ℝ) × ℝ)} {e : S ≃ₜ T} (he : e.IsFinitePL)
    (hdim : Module.finrank ℝ E = 3)
    (hcv : Convex ℝ S) (hzero : (0 : E) ∈ interior S)
    (Q : Bool → Set E) (p a : Bool → E)
    (hpS : ∀ j, p j ∈ S) (hpQ : ∀ j, p j ∈ Q j)
    (ρ : Bool → ℝ) (hρ : ∀ j, 1 < ρ j) (hpa : ∀ j, p j = ρ j • a j)
    (L : Bool → E ≃L[ℝ] ((ℝ × ℝ) × ℝ))
    (hkeep : ∀ j (x : S), (x : E) ∈ convexJoin ℝ {0} (Q j) →
      (e x : (ℝ × ℝ) × ℝ) = L j x)
    (σ : Bool → ℝ) (hσneg : σ false < 0) (hσpos : 0 < σ true)
    (hLa : ∀ j, L j (a j) = ((0, σ j), 0)) :
    ∀ s ∈ Icc (σ false) (σ true), ((0, s), 0) ∈ interior T := by
  have hdimF : Module.finrank ℝ ((ℝ × ℝ) × ℝ) = 3 := by
    simp [Module.finrank_prod]
  have hsegment (j : Bool) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ((0, t * σ j), 0) ∈ interior T := by
    have h := he.smul_linear_cut_mem_interior (hdim.trans hdimF.symm)
      hcv hzero (hpS j) (hpQ j) (hρ j) (hpa j) (L j).toLinearMap (hkeep j) ht
    change t • L j (a j) ∈ interior T at h
    simpa only [hLa j, Prod.smul_mk, smul_eq_mul, mul_zero] using h
  intro s hs
  by_cases hs0 : s ≤ 0
  · have ht : s / σ false ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg_of_nonpos hs0 hσneg.le, (div_le_one_of_neg hσneg).mpr hs.1⟩
    simpa only [div_mul_cancel₀ s hσneg.ne] using hsegment false (s / σ false) ht
  · have ht : s / σ true ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg (le_of_not_ge hs0) hσpos.le, (div_le_one₀ hσpos).mpr hs.2⟩
    simpa only [div_mul_cancel₀ s hσpos.ne'] using hsegment true (s / σ true) ht

end Homeomorph

namespace IsOpen






theorem exists_longitudinal_prism_subset
    {U : Set ((ℝ × ℝ) × ℝ)} (hU : IsOpen U) {a b : ℝ}
    (haxis : ∀ s ∈ Icc a b, ((0, s), 0) ∈ U) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, δ ∈ Ioo 0 ε ∧ (Icc (-δ) δ ×ˢ Icc a b) ×ˢ Icc (-δ) δ ⊆ U := by
  let K : Set ((ℝ × ℝ) × ℝ) := (fun s : ℝ => ((0, s), 0)) '' Icc a b
  have hK : IsCompact K :=
    isCompact_Icc.image ((continuous_const.prodMk continuous_id).prodMk continuous_const)
  have hKU : K ⊆ U := by
    rintro _ ⟨s, hs, rfl⟩
    exact haxis s hs
  obtain ⟨r, hr, hthick⟩ := hK.exists_cthickening_subset_open hU hKU
  obtain ⟨δ, hδpos, hδsmall⟩ := exists_between (lt_min hε hr)
  have hδε : δ < ε := hδsmall.trans_le (min_le_left _ _)
  have hδr : δ < r := hδsmall.trans_le (min_le_right _ _)
  refine ⟨δ, ⟨hδpos, hδε⟩, ?_⟩
  intro x hx
  apply hthick
  apply Metric.mem_cthickening_of_dist_le x ((0, x.1.2), 0) r K
    ⟨x.1.2, hx.1.2, rfl⟩
  simp only [Prod.dist_eq, dist_self, dist_zero_right, Real.norm_eq_abs]
  exact max_le (max_le ((abs_le.mpr hx.1.1).trans hδr.le) hr.le)
    ((abs_le.mpr hx.2).trans hδr.le)

end IsOpen
