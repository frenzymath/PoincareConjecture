import PoincareConjecture.Proofs.M63.Sec19_3_Ramps.Def19_12_PositiveDegree

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}

theorem m63PositiveDegree_preserved
    {F : RicciFlow n M (Icc a b)} {circumference T : ℝ}
    (P : M62.CircleProductData F circumference) (c : ℝ → ℝ → P.charts.Point)
    (hcont : ContinuousOn (fun z : ℝ × ℝ => c z.1 z.2) (univ ×ˢ Icc a T))
    (hper : ∀ t ∈ Icc a T, Function.Periodic (fun x => c x t) curvePeriod)
    (hreg : ∀ t ∈ Icc a T, ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) 2 (fun x => c x t))
    (hramp : ∀ t ∈ Icc a T, M63IsRampAt P (fun x => c x t) t)
    (L0 : M63PositiveDegreeLift P (fun x => c x a)) {t : ℝ} (ht : t ∈ Icc a T) :
    ∃ Lt : M63PositiveDegreeLift P (fun x => c x t), Lt.degree = L0.degree := by
  let := P.charts.chartedSpace
  have htime (s : unitInterval) : a + (s : ℝ) * (t - a) ∈ Icc a T := by
    have hleft := mul_nonneg s.property.1 (sub_nonneg.mpr ht.1)
    have hright := mul_nonneg (sub_nonneg.mpr s.property.2) (sub_nonneg.mpr ht.1)
    constructor <;> nlinarith only [hleft, hright, ht.2]
  have hcontinuous : Continuous
      (fun z : unitInterval × ℝ => c z.2 (a + (z.1 : ℝ) * (t - a))) :=
    hcont.comp_continuous
      (continuous_snd.prodMk (continuous_const.add
        ((continuous_subtype_val.comp continuous_fst).mul continuous_const)))
      (fun z => ⟨mem_univ _, htime z.1⟩)
  let H : C(unitInterval × ℝ, AddCircle circumference) :=
    ⟨fun z => (c z.2 (a + (z.1 : ℝ) * (t - a))).2, hcontinuous.snd⟩
  obtain ⟨L, _, hproj, hshift⟩ := AddCircle.exists_homotopy_lift_periodShift
    H ⟨L0.lift, L0.regular.continuous⟩
    (fun x => by simpa [H, M62.CircleGeometry.quotient] using (L0.quotient_eq x).symm)
    (fun s x => congrArg Prod.snd (hper _ (htime s) x)) L0.period_shift
  have hL : Continuous (fun x => L (1, x)) :=
    L.continuous.comp (continuous_const.prodMk continuous_id)
  have hquot (x : ℝ) : P.circle.quotient (L (1, x)) = (c x t).2 := by
    simpa [H, M62.CircleGeometry.quotient]
      using hproj (1, x)
  have hprojreg : ContMDiff 𝓘(ℝ, ℝ) (𝓡 1) 2 (fun x => (c x t).2) :=
    (contMDiff_snd.comp P.charts.to_product_smooth).of_le (by decide) |>.comp (hreg t ht)
  have hregular := m63CircleLift_contDiff P.circle hprojreg hL hquot
  have hpositive (x : ℝ) : 0 < deriv (fun y => L (1, y)) x := by
    have h := hramp t ht x
    rw [m63Slope_eq_lift_deriv_div_speed P ((hreg t ht).mdifferentiable (by norm_num))
      (hregular.differentiable (by norm_num)) hquot] at h
    have hv : 0 ≤ curveSpeed P.flow (fun y _ => c y t) t x := Real.sqrt_nonneg _
    rcases div_pos_iff.mp h with h | h
    · exact h.1
    · exact (not_lt_of_ge hv h.2).elim
  exact ⟨⟨(fun x => L (1, x)), hregular, L0.degree, L0.degree_positive,
    hquot, hshift 1, hpositive⟩, rfl⟩

end PoincareConjecture
