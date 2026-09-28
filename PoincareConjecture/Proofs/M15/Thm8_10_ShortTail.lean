import PoincareConjecture.Proofs.M15.Thm8_10_ShortCurve
import PoincareConjecture.Proofs.M09.SmoothSquarePath











set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology intervalIntegral

universe u

namespace PoincareConjecture.Proofs.M15

set_option backward.isDefEq.respectTransparency false in



theorem exists_backwardPath_short_tail
    {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {J : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T taumax : ℝ)
    (htau : 0 < taumax) (hwindow : Icc (T - taumax) T ⊆ J)
    {c b : ℝ} (hc : 0 < c) (hcb : c < b) (hb : b < taumax)
    (g : RiemannianMetric n M) (p q : M) {R C S : ℝ}
    (hR : 0 < R) (hC : 0 ≤ C) (hS : 0 ≤ S)
    (hcompact : IsCompact (closure (g.ball p R))) (hq : q ∈ g.ball p R)
    (hnorm : ∀ t ∈ Icc c b, ∀ x (v : TangentSpace (𝓡 n) x),
      (F.metric (T - t)).tangentNorm x v ≤ C * g.tangentNorm x v)
    (hscalar : ∀ t ∈ Icc c b, ∀ x,
      (F.connection (T - t)).scalarCurvature x ≤ S) :
    ∃ Q : BackwardTimePath F T c b, Nonempty (SqrtRegularPath Q) ∧
      Q.curve c = p ∧ Q.curve b = q ∧
      backwardLLength F T c b Q.curve ≤
        Real.sqrt b * (S + (C * R / (b - c)) ^ 2) * (b - c) := by
  obtain ⟨γ, hγ, hγ0, hγ1, hspeed⟩ := g.exists_smooth_short_curve p q hR hcompact hq
  have hbc : 0 < b - c := sub_pos.mpr hcb
  let α : ℝ → M := fun s => γ ((s ^ 2 - c) / (b - c))
  have hα : ContMDiff 𝓘(ℝ) (𝓡 n) ∞ α :=
    hγ.comp (((contMDiff_id.pow 2).sub contMDiff_const).div_const (b - c))
  obtain ⟨P, hP, _⟩ := M09.exists_backwardPath_of_smoothSquareCurve F hM04
    T taumax htau hwindow b (hc.trans hcb) hb α univ isOpen_univ
      (subset_univ _) hα.contMDiffOn
  have hsub : Icc c b ⊆ Icc 0 b := fun _ ht => ⟨hc.le.trans ht.1, ht.2⟩
  let Q : BackwardTimePath F T c b := {
    curve := P.curve
    nonnegative := hc.le
    ordered := hcb
    terminal_mem := P.terminal_mem
    time_mem := fun t ht => P.time_mem t (hsub ht)
    continuous := P.continuous.mono hsub
    regular := P.regular.mono (fun _ ht => ⟨hc.trans ht.1, ht.2⟩)
    l_integrable := P.l_integrable.mono_set (by
      rw [uIcc_of_le hcb.le, uIcc_of_le (hc.trans hcb).le]
      exact hsub)
  }
  have hQ (t : ℝ) (ht : 0 ≤ t) : Q.curve t = γ ((t - c) / (b - c)) := by
    change P.curve t = _
    rw [hP]
    dsimp only [α]
    rw [Real.sq_sqrt ht]
  have hregular : Nonempty (SqrtRegularPath Q) := ⟨{
    curve := α
    domain := univ
    open_domain := isOpen_univ
    interval_subset := subset_univ _
    smooth := hα.contMDiffOn
    agrees := fun s _ => by rw [hQ _ (sq_nonneg s)]
  }⟩
  have hQc : Q.curve c = p := by simpa only [hQ c hc.le, sub_self, zero_div] using hγ0
  have hQb : Q.curve b = q := by
    simpa only [hQ b (hc.trans hcb).le, div_self hbc.ne'] using hγ1
  refine ⟨Q, hregular, hQc, hQb, ?_⟩
  have hintegrand (t : ℝ) (ht : t ∈ Icc c b) :
      backwardLIntegrand F T Q.curve t ≤
        Real.sqrt b * (S + (C * R / (b - c)) ^ 2) := by
    have htpos : 0 < t := hc.trans_le ht.1
    have hparam : (t - c) / (b - c) ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg (sub_nonneg.mpr ht.1) hbc.le,
        (div_le_one hbc).mpr (sub_le_sub_right ht.2 c)⟩
    have heq : Q.curve =ᶠ[𝓝 t] (fun s => γ ((s - c) / (b - c))) :=
      Filter.eventually_of_mem (Ioi_mem_nhds htpos) (fun s hs => hQ s hs.le)
    have hd : HasDerivAt (fun s : ℝ => (s - c) / (b - c)) (1 / (b - c)) t :=
      ((hasDerivAt_id t).sub_const c).div_const (b - c)
    have hmap : mfderiv 𝓘(ℝ) 𝓘(ℝ) (fun s : ℝ => (s - c) / (b - c)) t 1 =
        (1 / (b - c)) • (1 : ℝ) := by
      rw [hd.hasFDerivAt.hasMFDerivAt.mfderiv]
      change (ContinuousLinearMap.toSpanSingleton ℝ (1 / (b - c))) (1 : ℝ) =
        (1 / (b - c)) * 1
      simp only [ContinuousLinearMap.toSpanSingleton_apply, one_smul, mul_one]
    have hvelocity : curveVelocity (n := n) Q.curve t =
        (1 / (b - c)) • curveVelocity (n := n) γ ((t - c) / (b - c)) := by
      unfold curveVelocity
      rw [heq.mfderiv_eq]
      have hm := mfderiv_comp_apply (I := 𝓘(ℝ)) (I' := 𝓘(ℝ)) (I'' := 𝓡 n)
        t (f := fun s : ℝ => (s - c) / (b - c)) (g := γ)
        (hγ.contMDiffAt.mdifferentiableAt (by simp)) hd.differentiableAt.mdifferentiableAt
          (1 : ℝ)
      rw [hmap, map_smul] at hm
      exact hm
    have hgnorm : g.tangentNorm (Q.curve t) (curveVelocity Q.curve t) =
        (1 / (b - c)) *
          g.tangentNorm (γ ((t - c) / (b - c)))
            (curveVelocity γ ((t - c) / (b - c))) := by
      rw [hvelocity, hQ t htpos.le]
      simp only [RiemannianMetric.tangentNorm, map_smul, smul_apply, smul_eq_mul]
      rw [← mul_assoc, ← pow_two, Real.sqrt_mul (sq_nonneg (1 / (b - c))),
        Real.sqrt_sq (by positivity : 0 ≤ 1 / (b - c))]
    have hflow : (F.metric (T - t)).tangentNorm (Q.curve t) (curveVelocity Q.curve t) ≤
        C * R / (b - c) := by
      calc
        _ ≤ C * g.tangentNorm (Q.curve t) (curveVelocity Q.curve t) :=
          hnorm t ht _ _
        _ = C * ((1 / (b - c)) *
            g.tangentNorm (γ ((t - c) / (b - c)))
              (curveVelocity γ ((t - c) / (b - c)))) := by rw [hgnorm]
        _ ≤ C * ((1 / (b - c)) * R) := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hspeed _ hparam) (by positivity)) hC
        _ = C * R / (b - c) := by ring
    have henergy : (F.metric (T - t)).inner (Q.curve t)
        (curveVelocity Q.curve t) (curveVelocity Q.curve t) ≤
          (C * R / (b - c)) ^ 2 := by
      have hnonneg : 0 ≤ (F.metric (T - t)).inner (Q.curve t)
          (curveVelocity Q.curve t) (curveVelocity Q.curve t) := by
        by_cases hv : curveVelocity (n := n) Q.curve t = 0
        · simp [hv]
        · exact ((F.metric (T - t)).pos _ _ hv).le
      have hsquare : ((F.metric (T - t)).tangentNorm (Q.curve t)
          (curveVelocity Q.curve t)) ^ 2 =
          (F.metric (T - t)).inner (Q.curve t)
            (curveVelocity Q.curve t) (curveVelocity Q.curve t) := Real.sq_sqrt hnonneg
      rw [← hsquare]
      exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hflow 2
    unfold backwardLIntegrand
    calc
      _ ≤ Real.sqrt t * (S + (C * R / (b - c)) ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add (hscalar t ht _) henergy) (Real.sqrt_nonneg t)
      _ ≤ Real.sqrt b * (S + (C * R / (b - c)) ^ 2) :=
        mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt ht.2) (add_nonneg hS (sq_nonneg _))
  have hi := intervalIntegral.integral_mono_on hcb.le Q.l_integrable
    (intervalIntegrable_const : IntervalIntegrable
      (fun _ : ℝ => Real.sqrt b * (S + (C * R / (b - c)) ^ 2)) volume c b) hintegrand
  simpa only [backwardLLength, intervalIntegral.integral_const, smul_eq_mul, mul_comm] using hi

end PoincareConjecture.Proofs.M15
