import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.C2TraceEmbeddingBounds
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.C2TraceEmbeddedEquation
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.C2TraceInverseSpeed
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.C2TracePeriodicCurvature

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u v

namespace PoincareConjecture.M63

open M62

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [T2Space M] {ι : Type v} [Fintype ι] {a b : ℝ}

local notation "W" => EuclideanSpace ℝ ι

theorem exists_uniform_embeddedCurvature_forcing_bounds
    (F : RicciFlow n M (Icc a b)) (hab : a < b)
    (hcompact : IsCompact (univ : Set M)) {e : M → W}
    (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e)
    {K R J m0 V0 : ℝ} (hK : 0 ≤ K) (hR : 0 ≤ R) (hJ : 0 ≤ J)
    (hBounds : CurveEvolutionAmbientBounds F K K K) (hm0 : 0 < m0) (hmV : m0 ≤ V0) :
    ∃ A B C : ℝ, (0 ≤ A ∧ 0 ≤ B ∧ 0 ≤ C) ∧
      ∀ (c : ℝ → ℝ → M) (_hc : M62ShrinkingCurve F c) (v0 : ℝ), v0 ∈ Icc m0 V0 →
      (∀ x, curveSpeed F c a x = v0) →
      (∀ t ∈ Ioo a b, ∀ x, m62CurvatureSquared F c t x ≤ R) →
      (∀ t ∈ Ioo a b, ∀ x,
        (F.metric t).tangentNorm (c x t) (m63CurvatureJet F c 1 t x) ≤
          J / Real.sqrt (t - a)) →
      let H : ℝ → ℝ → W := fun t x =>
        mfderiv (𝓡 n) 𝓘(ℝ, W) e (c x t) (m62CurvatureVector F c t x)
      let η : ℝ → ℝ → ℝ := fun t x => (curveSpeed F c t x ^ 2)⁻¹ - (v0 ^ 2)⁻¹
      let G : ℝ → ℝ → W := fun t x =>
        (deriv (fun r => H r x) t - (curveSpeed F c t x ^ 2)⁻¹ • iteratedDeriv 2 (H t) x) -
          deriv (η t) x • deriv (H t) x
      ∀ t ∈ Ioo a b, ∀ x,
        HasDerivAt (fun y => η t y • deriv (H t) y)
          (deriv (η t) x • deriv (H t) x + η t x • iteratedDeriv 2 (H t) x) x ∧
        deriv (fun r => H r x) t - (v0 ^ 2)⁻¹ • iteratedDeriv 2 (H t) x =
          (deriv (η t) x • deriv (H t) x + η t x • iteratedDeriv 2 (H t) x) + G t x ∧
        ‖η t x • deriv (H t) x‖ ≤ A * Real.sqrt (t - a) ∧
        ‖G t x‖ ≤ B + C / Real.sqrt (t - a) := by
  obtain ⟨E1, E2, E3, ⟨hE1, hE2, hE3⟩, hE⟩ :=
    exists_uniform_embedding_derivative_bounds F hcompact he
  let δ := b - a
  let S := Real.sqrt δ
  let κ := Real.sqrt R
  let D0 := K + R
  let m := m0 * Real.exp (-D0 * δ)
  let V := V0 * Real.exp (D0 * δ)
  let α := K + 2 * K * κ
  let β := 4 * κ * J
  let D := V ^ 2 * (α * S + β)
  let Z := E1 * J + E2 * κ * S
  let P := V * Z
  let N := 2 * V * D0 / m ^ 3
  let N1 := 2 * D / m ^ 3
  let R0 := E1 * (2 * κ ^ 3 + 5 * K * κ + 4 * K) + E3 * κ + D * Z / m ^ 2
  let R1 := 2 * J * (E1 * κ + E2)
  have hδ : 0 < δ := sub_pos.mpr hab
  have hS : 0 ≤ S := Real.sqrt_nonneg _
  have hκ : 0 ≤ κ := Real.sqrt_nonneg _
  have hD0 : 0 ≤ D0 := add_nonneg hK hR
  have hm : 0 < m := mul_pos hm0 (Real.exp_pos _)
  have hV : 0 < V := mul_pos (hm0.trans_le hmV) (Real.exp_pos _)
  have hα : 0 ≤ α := by dsimp only [α]; positivity
  have hβ : 0 ≤ β := by dsimp only [β]; positivity
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hZ : 0 ≤ Z := by dsimp only [Z]; positivity
  have hP : 0 ≤ P := mul_nonneg hV.le hZ
  have hN : 0 ≤ N := by dsimp only [N]; positivity
  have hN1 : 0 ≤ N1 := by dsimp only [N1]; positivity
  have hR0 : 0 ≤ R0 := by dsimp only [R0]; positivity
  have hR1 : 0 ≤ R1 := by dsimp only [R1]; positivity
  refine ⟨N * P, R0 + N1 * P, R1, ⟨mul_nonneg hN hP,
    add_nonneg hR0 (mul_nonneg hN1 hP), hR1⟩, ?_⟩
  intro c hc v0 hv0 hInitial hCurv hJet
  dsimp only
  let H : ℝ → ℝ → W := fun r y =>
    mfderiv (𝓡 n) 𝓘(ℝ, W) e (c y r) (m62CurvatureVector F c r y)
  let η : ℝ → ℝ → ℝ := fun r y => (curveSpeed F c r y ^ 2)⁻¹ - (v0 ^ 2)⁻¹
  let m' := v0 * Real.exp (-D0 * δ)
  let V' := v0 * Real.exp (D0 * δ)
  have hv0pos : 0 < v0 := hm0.trans_le hv0.1
  have hm' : 0 < m' := mul_pos hv0pos (Real.exp_pos _)
  have hV' : 0 < V' := mul_pos hv0pos (Real.exp_pos _)
  have hmm' : m ≤ m' := mul_le_mul_of_nonneg_right hv0.1 (Real.exp_pos _).le
  have hV'V : V' ≤ V := mul_le_mul_of_nonneg_right hv0.2 (Real.exp_pos _).le
  intro t ht x
  let τ := t - a
  let σ := Real.sqrt τ
  let v := curveSpeed F c t x
  let k := m62Curvature F c t x
  let u := (F.metric t).tangentNorm (c x t) (m63CurvatureJet F c 1 t x)
  have htclosed := Ioo_subset_Icc_self ht
  have hτ : 0 < τ := sub_pos.mpr ht.1
  have hτδ : τ ≤ δ := sub_le_sub_right ht.2.le a
  have hσ : 0 < σ := Real.sqrt_pos.mpr hτ
  have hσS : σ ≤ S := Real.sqrt_le_sqrt hτδ
  have hσsq : σ ^ 2 = τ := Real.sq_sqrt hτ.le
  have hτsqrt : τ ≤ S * σ := by
    nlinarith only [mul_le_mul_of_nonneg_right hσS hσ.le, hσsq]
  have hv : 0 < v := speed_pos F c hc htclosed x
  have hk0 : 0 ≤ k := curvature_nonneg F c t x
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have hk : k ≤ κ := by
    nlinarith only [curvature_sq F c t x, hCurv t ht x, Real.sq_sqrt hR, hκ]
  have hu : u ≤ J / σ := hJet t ht x
  have hspeed := curveSpeed_exp_bounds F c hc hBounds x (fun r hr => hCurv r hr x)
    ⟨le_rfl, hab.le⟩ htclosed ht.1.le
  rw [hInitial] at hspeed
  change v0 * Real.exp (-D0 * τ) ≤ v ∧ v ≤ v0 * Real.exp (D0 * τ) at hspeed
  have hDτ : D0 * τ ≤ D0 * δ := mul_le_mul_of_nonneg_left hτδ hD0
  have hvm : m ≤ v := calc
    m ≤ m' := hmm'
    _ ≤ v0 * Real.exp (-D0 * τ) := mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by nlinarith only [hDτ])) hv0pos.le
    _ ≤ v := hspeed.1
  have hvV : v ≤ V := calc
    v ≤ v0 * Real.exp (D0 * τ) := hspeed.2
    _ ≤ V' := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hDτ) hv0pos.le
    _ ≤ V := hV'V
  have hQ : α * τ + β * σ ≤ (α * S + β) * σ := by
    nlinarith only [mul_le_mul_of_nonneg_left hτsqrt hα]
  have hvx : |deriv (curveSpeed F c t) x| ≤ D * σ := by
    have hb := curveSpeed_spatial_abs_bound F c hc hK hR hJ hv0pos
      hBounds hInitial hCurv hJet htclosed x
    change |deriv (curveSpeed F c t) x| ≤ V' ^ 2 * (α * τ + β * σ) at hb
    calc
      _ ≤ V' ^ 2 * (α * τ + β * σ) := hb
      _ ≤ V ^ 2 * ((α * S + β) * σ) := mul_le_mul
        (pow_le_pow_left₀ hV'.le hV'V 2) hQ (by positivity) (sq_nonneg _)
      _ = D * σ := by dsimp only [D]; ring
  have hη : |η t x| ≤ N * τ := by
    have hb := (curveSpeed_inverseSquared_initial_bounds F c hc hK hR hJ hv0pos
      hBounds hInitial hCurv hJet htclosed x).2.1
    change |η t x| ≤ (2 * V' * D0 / m' ^ 3) * τ at hb
    apply hb.trans
    apply mul_le_mul_of_nonneg_right _ hτ.le
    calc
      2 * V' * D0 / m' ^ 3 ≤ 2 * V * D0 / m' ^ 3 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hV'V (by norm_num)) hD0) (by positivity)
      _ ≤ N := div_le_div_of_nonneg_left (by positivity) (by positivity)
        (pow_le_pow_left₀ hm.le hmm' 3)
  have hηder := curveSpeed_inverseSquared_hasDerivAt F c hc v0 htclosed x
  change HasDerivAt (η t) (-2 * deriv (curveSpeed F c t) x / v ^ 3) x at hηder
  have hηx : |deriv (η t) x| ≤ N1 * σ := by
    rw [hηder.deriv, abs_div, abs_mul, abs_pow, abs_of_pos hv]
    norm_num only [abs_neg]
    calc
      2 * |deriv (curveSpeed F c t) x| / v ^ 3 ≤ 2 * (D * σ) / v ^ 3 := by
        gcongr
      _ ≤ 2 * (D * σ) / m ^ 3 := div_le_div_of_nonneg_left
        (by positivity) (by positivity) (pow_le_pow_left₀ hm.le hvm 3)
      _ = N1 * σ := by dsimp only [N1]; ring
  have hb := embeddedCurvature_derivative_remainder_bounds F c hc he hK hK hK hBounds
    ht x hE1 hE2 hE3
    (fun Y => (hE t htclosed (c x t) Y 0 0).1)
    (fun Y Z => (hE t htclosed (c x t) Y Z 0).2.1)
    (fun Y Z U => (hE t htclosed (c x t) Y Z U).2.2)
  change ‖deriv (H t) x‖ ≤ v * (E1 * u + E2 * k) ∧
    ‖deriv (fun r => H r x) t - (v ^ 2)⁻¹ • iteratedDeriv 2 (H t) x‖ ≤
      E1 * (2 * k ^ 3 + (K + 4 * K) * k + 4 * K + 2 * k * u) +
        (|deriv (curveSpeed F c t) x| / v ^ 2) * (E1 * u + E2 * k) +
        2 * E2 * u + E3 * k at hb
  have hku : E1 * u + E2 * k ≤ Z / σ := calc
    _ ≤ E1 * (J / σ) + E2 * κ := add_le_add
      (mul_le_mul_of_nonneg_left hu hE1) (mul_le_mul_of_nonneg_left hk hE2)
    _ = (E1 * J + E2 * κ * σ) / σ := by field_simp
    _ ≤ Z / σ := div_le_div_of_nonneg_right
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left hσS (mul_nonneg hE2 hκ))) hσ.le
  have hhx : ‖deriv (H t) x‖ ≤ P / σ := calc
    _ ≤ v * (E1 * u + E2 * k) := hb.1
    _ ≤ v * (Z / σ) := mul_le_mul_of_nonneg_left hku hv.le
    _ ≤ V * (Z / σ) := mul_le_mul_of_nonneg_right hvV (by positivity)
    _ = P / σ := by dsimp only [P]; ring
  have hdrift : (|deriv (curveSpeed F c t) x| / v ^ 2) * (E1 * u + E2 * k) ≤
      D * Z / m ^ 2 := by
    have hfrac : |deriv (curveSpeed F c t) x| / v ^ 2 ≤ D * σ / m ^ 2 :=
      (div_le_div_of_nonneg_right hvx (sq_nonneg _)).trans
        (div_le_div_of_nonneg_left (by positivity) (by positivity)
          (pow_le_pow_left₀ hm.le hvm 2))
    calc
      _ ≤ (D * σ / m ^ 2) * (Z / σ) := mul_le_mul hfrac hku (by positivity) (by positivity)
      _ = D * Z / m ^ 2 := by field_simp
  have hrest : E1 * (2 * k ^ 3 + (K + 4 * K) * k + 4 * K + 2 * k * u) +
      2 * E2 * u + E3 * k ≤
      E1 * (2 * κ ^ 3 + 5 * K * κ + 4 * K) + E3 * κ + R1 / σ := by
    calc
      _ ≤ E1 * (2 * κ ^ 3 + (K + 4 * K) * κ + 4 * K + 2 * κ * (J / σ)) +
          2 * E2 * (J / σ) + E3 * κ := by gcongr
      _ = _ := by dsimp only [R1]; ring
  have hrem : ‖deriv (fun r => H r x) t - (v ^ 2)⁻¹ • iteratedDeriv 2 (H t) x‖ ≤
      R0 + R1 / σ := by
    dsimp only [R0]
    linarith only [hb.2, hrest, hdrift]
  have hsmall : ‖η t x • deriv (H t) x‖ ≤ N * P * σ := by
    rw [norm_smul, Real.norm_eq_abs]
    calc
      _ ≤ (N * τ) * (P / σ) := mul_le_mul hη hhx (norm_nonneg _) (by positivity)
      _ = N * P * σ := by rw [← hσsq]; field_simp
  have hcross : ‖deriv (η t) x • deriv (H t) x‖ ≤ N1 * P := by
    rw [norm_smul, Real.norm_eq_abs]
    calc
      _ ≤ (N1 * σ) * (P / σ) := mul_le_mul hηx hhx (norm_nonneg _) (by positivity)
      _ = N1 * P := by field_simp
  have hspace : ContDiff ℝ ∞ (H t) := by
    rw [contDiff_iff_contDiffAt]
    intro y
    have hjoint := (embeddedCurvature_closed_periodic_data F c hab hc he).2.2
    exact (hjoint.contDiffAt ((isOpen_univ.prod isOpen_Ioo).mem_nhds
      ⟨mem_univ y, ht⟩)).comp y (contDiffAt_id.prodMk contDiffAt_const)
  have hxx : HasDerivAt (deriv (H t)) (iteratedDeriv 2 (H t) x) x := by
    have hd := ((contDiff_infty_iff_deriv.mp hspace).2.differentiable (by simp) x).hasDerivAt
    simpa only [show (2 : ℕ) = 1 + 1 from rfl,
      iteratedDeriv_succ, iteratedDeriv_zero] using! hd
  refine ⟨?_, ?_, hsmall, ?_⟩
  · simpa only [add_comm] using hηder.differentiableAt.hasDerivAt.fun_smul hxx
  · change deriv (fun r => H r x) t - (v0 ^ 2)⁻¹ • iteratedDeriv 2 (H t) x =
      (deriv (η t) x • deriv (H t) x + η t x • iteratedDeriv 2 (H t) x) +
        ((deriv (fun r => H r x) t - (v ^ 2)⁻¹ • iteratedDeriv 2 (H t) x) -
          deriv (η t) x • deriv (H t) x)
    dsimp only [η, v]
    rw [sub_smul]
    abel
  · exact (norm_sub_le _ _).trans ((add_le_add hrem hcross).trans_eq (by ring))

end PoincareConjecture.M63
