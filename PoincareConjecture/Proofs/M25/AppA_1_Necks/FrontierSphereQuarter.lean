import PoincareConjecture.Proofs.M25.AppA_1_Necks.PositiveFrontier










set_option autoImplicit false

open Set
open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareConjecture.EpsilonNeck



theorem exists_positive_frontier_quarter_control_at_sphere :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T3Space M] {g : RiemannianMetric 3 M},
      ∀ (N N' : EpsilonNeck g),
      N.epsilon ≤ epsilon0 → N'.epsilon = N.epsilon →
      ∀ y : M, y ∈ N'.central_sphere →
      y ∈ closure (N.region 0 N.epsilon⁻¹) →
      y ∉ N.carrier →
      N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹ ⊆ N'.carrier := by
  obtain ⟨epsilonS, hS, hScap, hscale⟩ :=
    exists_intersecting_scale_control.{u} (α := 1 / 100) (by norm_num)
  let C := Real.sqrt 2 * (Real.pi + 1)
  have hC : 0 < C := by dsimp only [C]; positivity
  have hden : 0 < 1000 * (C + 1) := by positivity
  refine ⟨min epsilonS (1 / (1000 * (C + 1))),
    lt_min hS (div_pos zero_lt_one hden), (min_le_left _ _).trans hScap, ?_⟩
  intro M _ _ _ _ _ _ g N N' hN hepsilon y hysphere hy hyout
  have hNscale : 0 < N.scale := N.scale_pos
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
  let L := N.epsilon⁻¹
  have hL : 0 < L := inv_pos.mpr N.epsilon_pos
  have hNs : N.epsilon ≤ epsilonS := hN.trans (min_le_left _ _)
  have hN's : N'.epsilon ≤ epsilonS := by rw [hepsilon]; exact hNs
  have hcap : N.epsilon ≤ 1 / 200 := hNs.trans hScap
  have hsmall : N.epsilon ≤ 1 / (1000 * (C + 1)) := hN.trans (min_le_right _ _)
  have hCe : (C + 1) * N.epsilon ≤ 1 / 1000 := by
    have h := (le_div_iff₀ hden).mp hsmall
    nlinarith
  have hCee : C * N.epsilon ≤ 1 / 1000 := by nlinarith [N.epsilon_pos]
  have hCL : C ≤ L / 1000 := by
    calc
      C ≤ (1 / 1000) / N.epsilon := (le_div_iff₀ N.epsilon_pos).mpr hCee
      _ = L / 1000 := by dsimp only [L]; ring
  have hb : (99 : ℝ) / 100 ≤ Real.sqrt (1 - N.epsilon) :=
    Real.le_sqrt_of_sq_le (by nlinarith)
  have hp : Real.sqrt (1 + N.epsilon) ≤ (101 : ℝ) / 100 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by nlinarith⟩
  have hc' := (N'.mem_central_sphere_iff y).mp hysphere
  have hinter : (N.carrier ∩ N'.carrier).Nonempty := by
    obtain ⟨z, hz', hz⟩ := mem_closure_iff.mp hy N'.carrier N'.carrier_open hc'.1
    exact ⟨z, hz.1, hz'⟩
  have hratio := (hscale N N' hNs hN's hinter).2
  have hratioLower : (99 : ℝ) / 100 < N'.scale / N.scale := by
    linarith [(abs_lt.mp hratio).1]
  have hscaleLower : (99 : ℝ) / 100 * N.scale ≤ N'.scale :=
    ((lt_div_iff₀ N.scale_pos).mp hratioLower).le
  intro x hx
  by_contra hxout
  have hupper := N.edist_le_positive_frontier hx.1 hy hyout
  have hupperReal : N.scale * Real.sqrt (1 + N.epsilon) *
      (L - (N.coordinate_inverse x).2 + C) ≤
      (50601 : ℝ) / 100000 * N.scale * L := by
    calc
      _ ≤ N.scale * Real.sqrt (1 + N.epsilon) * (L / 2 + C) :=
        mul_le_mul_of_nonneg_left (by linarith [hx.2.1])
          (mul_nonneg N.scale_pos.le (Real.sqrt_nonneg _))
      _ ≤ N.scale * (101 / 100) * (L / 2 + C) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hp N.scale_pos.le) (by positivity)
      _ ≤ N.scale * (101 / 100) * (L / 2 + L / 1000) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl hCL) (by positivity)
      _ = _ := by ring
  have hu : g.edist x y ≤
      ENNReal.ofReal ((50601 : ℝ) / 100000 * N.scale * L) :=
    hupper.trans (ENNReal.ofReal_le_ofReal hupperReal)
  have hd : ENNReal.ofReal (N'.scale * Real.sqrt (1 - N.epsilon) * L) ≤
      g.edist x y := by
    simpa only [axialDepth, if_neg hxout, if_pos hc'.1, hc'.2, abs_zero,
      sub_zero, zero_sub, abs_neg, hepsilon,
      abs_of_pos (inv_pos.mpr N.epsilon_pos)] using N'.axialDepth_edist_le x y
  have hlowerReal : (9801 : ℝ) / 10000 * N.scale * L ≤
      N'.scale * Real.sqrt (1 - N.epsilon) * L := by
    calc
      _ = ((99 / 100) * N.scale) * (99 / 100) * L := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul hscaleLower hb (by norm_num) N'.scale_pos.le) hL.le
  have hbad := ((ENNReal.ofReal_le_ofReal hlowerReal).trans hd).trans hu
  have hstrict : ENNReal.ofReal ((50601 : ℝ) / 100000 * N.scale * L) <
      ENNReal.ofReal ((9801 : ℝ) / 10000 * N.scale * L) := by
    apply (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
    nlinarith [mul_pos N.scale_pos hL]
  exact (not_le_of_gt hstrict) hbad

end PoincareConjecture.EpsilonNeck
