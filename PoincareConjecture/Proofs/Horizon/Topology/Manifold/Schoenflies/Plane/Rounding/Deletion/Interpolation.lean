import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Rounding.Isotopy










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Plane

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (Module.finrank ℝ E = 2)] {n : ℕ} [NeZero n]

theorem exists_ambient_polygon_interpolation_tolerance
    (e : ℂ ≃ₗᵢ[ℝ] E) (o : Orientation ℝ E (Fin 2))
    {p : Polygon E n} (hp : IsSimplePolygon p) :
    ∃ η : ℝ, 0 < η ∧ ∀ α β : ℝ → E, ContDiff ℝ ∞ α → ContDiff ℝ ∞ β →
      Periodic α (n : ℝ) → Periodic β (n : ℝ) →
      (∀ t ∈ Icc (0 : ℝ) n, dist (α t) (polygonLinearParameter p t) < η) →
      (∀ t ∈ Icc (0 : ℝ) n, dist (β t) (polygonLinearParameter p t) < η) →
      (∀ i : ℤ, ∃ ℓ : E →L[ℝ] ℝ, ∀ t : ℝ, |t - i| < 3 / 4 →
        0 < ℓ (deriv α t) ∧ 0 < ℓ (deriv β t)) →
      ∃ F : E ≃ₘ[ℝ] E,
        (∃ K : Set E, IsCompact K ∧ ∀ x ∉ K, F x = x) ∧
        F '' range α = range β := by
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
  obtain ⟨η, hη, hstable⟩ := exists_periodic_injection_tolerance
    (K := Icc (0 : ℝ) 1) isCompact_Icc (T := (n : ℝ)) (r := 1 / 8)
    (by linarith) (by norm_num) (by linarith)
    (fun _ => polygonLinearParameter p)
    (continuous_polygonLinearParameter (fun _ => continuous_const)).continuousOn
    (fun _ _ => periodic_polygonLinearParameter p)
    (fun _ _ => hp.injOn_polygonLinearParameter)
  refine ⟨η, hη, ?_⟩
  intro α β hα hβ hαper hβper hαclose hβclose hprojection
  let H : ℝ → ℝ → E := fun u t => (1 - u) • α t + u • β t
  have hH : ContDiff ℝ ∞ (fun x : ℝ × ℝ => H x.1 x.2) :=
    ((contDiff_const.sub contDiff_fst).smul (hα.comp contDiff_snd)).add
      (contDiff_fst.smul (hβ.comp contDiff_snd))
  have hper (u : ℝ) : Periodic (H u) (n : ℝ) := by
    intro t
    simp only [H, hαper t, hβper t]
  have hder (u t : ℝ) : HasDerivAt (H u)
      ((1 - u) • deriv α t + u • deriv β t) t :=
    ((hα.differentiable (by simp) t).hasDerivAt.const_smul (1 - u)).add
      ((hβ.differentiable (by simp) t).hasDerivAt.const_smul u)
  have hpositive (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) (i : ℤ)
      (ℓ : E →L[ℝ] ℝ)
      (hℓ : ∀ t : ℝ, |t - i| < 3 / 4 → 0 < ℓ (deriv α t) ∧ 0 < ℓ (deriv β t))
      (t : ℝ) (ht : |t - i| < 3 / 4) :
      0 < ℓ ((1 - u) • deriv α t + u • deriv β t) := by
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    obtain ⟨ha, hb⟩ := hℓ t ht
    by_cases hu0 : u = 0
    · simpa [hu0] using ha
    · have hup : 0 < u := lt_of_le_of_ne hu.1 (Ne.symm hu0)
      have := mul_pos hup hb
      have := mul_nonneg (sub_nonneg.mpr hu.2) ha.le
      linarith
  have hlocal (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) (s t : ℝ)
      (hst : |s - t| < 1 / 8) (heq : H u s = H u t) : s = t := by
    let i : ℤ := ⌊s + 1 / 2⌋
    have hlo : (i : ℝ) ≤ s + 1 / 2 := Int.floor_le _
    have hhi : s + 1 / 2 < (i : ℝ) + 1 := Int.lt_floor_add_one _
    obtain ⟨ℓ, hℓ⟩ := hprojection i
    have hs : s ∈ Ioo ((i : ℝ) - 3 / 4) ((i : ℝ) + 3 / 4) := by
      constructor <;> linarith
    have ht : t ∈ Ioo ((i : ℝ) - 3 / 4) ((i : ℝ) + 3 / 4) := by
      obtain ⟨hl, hr⟩ := abs_lt.mp hst
      constructor <;> linarith
    have hmono : StrictMonoOn (fun v => ℓ (H u v))
        (Ioo ((i : ℝ) - 3 / 4) ((i : ℝ) + 3 / 4)) := by
      apply strictMonoOn_of_deriv_pos (convex_Ioo _ _)
        ((ℓ.continuous.comp
          (continuous_iff_continuousAt.mpr (fun v => (hder u v).continuousAt))).continuousOn)
      intro v hv
      have hv' := interior_subset hv
      have habs : |v - i| < 3 / 4 := by
        apply abs_lt.mpr
        exact ⟨by linarith [hv'.1], by linarith [hv'.2]⟩
      rw [(ℓ.hasFDerivAt.comp_hasDerivAt v (hder u v)).deriv]
      exact hpositive u hu i ℓ hℓ v habs
    exact hmono.injOn hs ht (congrArg ℓ heq)
  have hregular (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) (t : ℝ) : deriv (H u) t ≠ 0 := by
    let i : ℤ := ⌊t + 1 / 2⌋
    have hlo : (i : ℝ) ≤ t + 1 / 2 := Int.floor_le _
    have hhi : t + 1 / 2 < (i : ℝ) + 1 := Int.lt_floor_add_one _
    obtain ⟨ℓ, hℓ⟩ := hprojection i
    have ht : |t - i| < 3 / 4 := by
      apply abs_lt.mpr
      constructor <;> linarith
    have hpos := hpositive u hu i ℓ hℓ t ht
    rw [← (hder u t).deriv] at hpos
    intro hz
    simp [hz] at hpos
  have hclose (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) n) :
      dist (H u t) (polygonLinearParameter p t) < η := by
    let z := polygonLinearParameter p t
    have hdiff : H u t - z = (1 - u) • (α t - z) + u • (β t - z) := by dsimp [H]; module
    rw [dist_eq_norm, hdiff]
    calc
      ‖(1 - u) • (α t - z) + u • (β t - z)‖ ≤
          ‖(1 - u) • (α t - z)‖ + ‖u • (β t - z)‖ := norm_add_le _ _
      _ = (1 - u) * dist (α t) z + u * dist (β t) z := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (sub_nonneg.mpr hu.2), abs_of_nonneg hu.1, ← dist_eq_norm, ← dist_eq_norm]
      _ < η := by
        have ha := hαclose t ht
        have hb := hβclose t ht
        by_cases hu0 : u = 0
        · simpa [hu0, z] using ha
        · have hup : 0 < u := lt_of_le_of_ne hu.1 (Ne.symm hu0)
          have hstrict := mul_lt_mul_of_pos_left hb hup
          have hweak := mul_le_mul_of_nonneg_left ha.le (sub_nonneg.mpr hu.2)
          dsimp [z]
          nlinarith
  obtain ⟨Phi, _, _, ⟨K, hK, hfix⟩, hmotion⟩ :=
    exists_ambient_isotopy_of_periodic_family e o (by linarith) zero_le_one H hH hper
      (hstable H (fun u _ => hper u) hclose hlocal) hregular
  refine ⟨Phi 1, ⟨K, hK, hfix 1⟩, ?_⟩
  simpa only [H, sub_zero, sub_self, one_smul, zero_smul, add_zero, zero_add]
    using hmotion 1 (by simp)

end Poincare.Manifold.Schoenflies.Plane
