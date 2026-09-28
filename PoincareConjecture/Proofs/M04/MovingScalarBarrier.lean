import PoincareConjecture.Proofs.M04.ExponentialBarrierProfile
import PoincareConjecture.Proofs.M04.SpacetimeScalarCoefficients
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.SpecialFunctions.ExpDeriv








set_option autoImplicit false

open scoped Manifold ContDiff Bundle
open Set Topology Filter Function Polynomial

universe u

namespace PoincareConjecture.M04

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

private theorem deriv_affine_expNegInvGlue (c b s : ℝ) :
    deriv (fun r : ℝ ↦ expNegInvGlue (c + b * r)) s =
      deriv expNegInvGlue (c + b * s) * b := by
  have hbase : HasDerivAt expNegInvGlue
      (deriv expNegInvGlue (c + b * s)) (c + b * s) := by
    exact ((contDiff_infty_iff_deriv.mp expNegInvGlue.contDiff).1
      (c + b * s)).hasDerivAt
  have harg : HasDerivAt (fun r : ℝ ↦ c + b * r) b s := by
    have hlin : HasDerivAt (fun r : ℝ ↦ b * r) b s := by
      simpa only [id_eq, mul_one] using (hasDerivAt_id s).const_mul b
    simpa only [Pi.add_apply, zero_add] using! (hasDerivAt_const s c).add hlin
  exact (hbase.comp s harg).deriv

theorem hasDerivAt_moving_scalar_barrier (q : M → ℝ) (A b epsilon t : ℝ) (x : M) :
    HasDerivAt
      (fun s : ℝ ↦ epsilon * Real.exp (-A * s) *
        expNegInvGlue (q x + b * s))
      (epsilon * Real.exp (-A * t) *
        (-A * expNegInvGlue (q x + b * t) +
          b * deriv expNegInvGlue (q x + b * t))) t := by
  have harg : HasDerivAt (fun s : ℝ ↦ q x + b * s) b t := by
    have hlin : HasDerivAt (fun s : ℝ ↦ b * s) b t := by
      simpa only [id_eq, mul_one] using (hasDerivAt_id t).const_mul b
    simpa only [Pi.add_apply, zero_add] using! (hasDerivAt_const t (q x)).add hlin
  have hψ : HasDerivAt (fun s : ℝ ↦ expNegInvGlue (q x + b * s))
      (deriv expNegInvGlue (q x + b * t) * b) t := by
    have hbase : HasDerivAt expNegInvGlue
        (deriv expNegInvGlue (q x + b * t)) (q x + b * t) := by
      exact ((contDiff_infty_iff_deriv.mp expNegInvGlue.contDiff).1
        (q x + b * t)).hasDerivAt
    exact hbase.comp t harg
  have he : HasDerivAt (fun s : ℝ ↦ Real.exp (-A * s))
      (-A * Real.exp (-A * t)) t := by
    convert ((hasDerivAt_id t).const_mul (-A)).exp using 1 <;> simp only [id_eq] <;> ring
  have hc : HasDerivAt (fun s : ℝ ↦ epsilon * Real.exp (-A * s))
      (epsilon * (-A * Real.exp (-A * t))) t := by
    have hfun : (fun s : ℝ ↦ epsilon * Real.exp (-A * s)) =
        (fun x : ℝ ↦ epsilon) * (fun s : ℝ ↦ Real.exp (-A * s)) := by
      funext s
      rfl
    rw [hfun]
    simpa only [zero_mul, zero_add] using (hasDerivAt_const t epsilon).mul he
  have hfun : (fun s : ℝ ↦ epsilon * Real.exp (-A * s) *
      expNegInvGlue (q x + b * s)) =
      (fun s : ℝ ↦ epsilon * Real.exp (-A * s)) *
        (fun s : ℝ ↦ expNegInvGlue (q x + b * s)) := by
    funext s
    rfl
  rw [hfun]
  convert! hc.mul hψ using 1 <;>
    first | (funext s; rfl) | ring

theorem laplacian_moving_scalar_barrier
    {g : RiemannianMetric n M} (D : LeviCivitaData g) {U : Set M}
    {q : M → ℝ} (hU : IsOpen U)
    (hq : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ q U)
    (A b epsilon t : ℝ) {x : M} (hx : x ∈ U) :
    D.laplacian (fun y ↦ epsilon * Real.exp (-A * t) *
        expNegInvGlue (q y + b * t)) x =
      epsilon * Real.exp (-A * t) *
        (deriv expNegInvGlue (q x + b * t) * D.laplacian q x +
          deriv (deriv expNegInvGlue) (q x + b * t) * scalarGradientSq g q x) := by
  let c : ℝ := epsilon * Real.exp (-A * t)
  let φ : ℝ → ℝ := fun s ↦ c * expNegInvGlue (s + b * t)
  have harg : ContDiff ℝ ∞ (fun s : ℝ ↦ s + b * t) :=
    contDiff_id.add contDiff_const
  have hφ : ContDiff ℝ ∞ φ := by
    exact contDiff_const.mul (expNegInvGlue.contDiff.comp harg)
  have h := laplacian_comp D hU hq hφ hx
  have hφ1 : deriv φ (q x) = c * deriv expNegInvGlue (q x + b * t) := by
    change deriv (fun s : ℝ ↦ c * expNegInvGlue (s + b * t)) (q x) = _
    have hbase : HasDerivAt expNegInvGlue
        (deriv expNegInvGlue (q x + b * t)) (q x + b * t) := by
      exact ((contDiff_infty_iff_deriv.mp expNegInvGlue.contDiff).1
        (q x + b * t)).hasDerivAt
    have hcomp : HasDerivAt (fun s : ℝ ↦ expNegInvGlue (s + b * t))
        (deriv expNegInvGlue (q x + b * t)) (q x) :=
      hbase.comp_add_const (q x) (b * t)
    have hfun : (fun s : ℝ ↦ c * expNegInvGlue (s + b * t)) =
        (fun x : ℝ ↦ c) * (fun s : ℝ ↦ expNegInvGlue (s + b * t)) := by
      funext s
      simp only [Pi.mul_apply]
    rw [hfun]
    simpa only [zero_mul, zero_add] using ((hasDerivAt_const (q x) c).mul hcomp).deriv
  have hφ2 : deriv (deriv φ) (q x) =
      c * deriv (deriv expNegInvGlue) (q x + b * t) := by
    have hfirst : deriv φ = fun s ↦ c * deriv expNegInvGlue (s + b * t) := by
      funext s
      change deriv (fun r : ℝ ↦ c * expNegInvGlue (r + b * t)) s = _
      have hbase : HasDerivAt expNegInvGlue
          (deriv expNegInvGlue (s + b * t)) (s + b * t) := by
        exact ((contDiff_infty_iff_deriv.mp expNegInvGlue.contDiff).1
          (s + b * t)).hasDerivAt
      have hcomp : HasDerivAt (fun r : ℝ ↦ expNegInvGlue (r + b * t))
          (deriv expNegInvGlue (s + b * t)) s :=
        hbase.comp_add_const s (b * t)
      have hfun : (fun r : ℝ ↦ c * expNegInvGlue (r + b * t)) =
          (fun x : ℝ ↦ c) * (fun r : ℝ ↦ expNegInvGlue (r + b * t)) := by
        funext r
        simp only [Pi.mul_apply]
      rw [hfun]
      simpa only [zero_mul, zero_add] using ((hasDerivAt_const s c).mul hcomp).deriv
    rw [hfirst]
    have hbase : HasDerivAt (deriv expNegInvGlue)
        (deriv (deriv expNegInvGlue) (q x + b * t)) (q x + b * t) := by
      have hderiv : Differentiable ℝ (deriv expNegInvGlue) :=
        (contDiff_infty_iff_deriv.mp expNegInvGlue.contDiff).2.differentiable
          (by norm_num)
      exact (hderiv (q x + b * t)).hasDerivAt
    have hcomp : HasDerivAt (fun r : ℝ ↦ deriv expNegInvGlue (r + b * t))
        (deriv (deriv expNegInvGlue) (q x + b * t)) (q x) :=
      hbase.comp_add_const (q x) (b * t)
    have hfun : (fun r : ℝ ↦ c * deriv expNegInvGlue (r + b * t)) =
        (fun x : ℝ ↦ c) * (fun r : ℝ ↦ deriv expNegInvGlue (r + b * t)) := by
      funext r
      simp only [Pi.mul_apply]
    rw [hfun]
    simpa only [zero_mul, zero_add] using ((hasDerivAt_const (q x) c).mul hcomp).deriv
  rw [hφ1, hφ2] at h
  convert h using 1 <;> simp [φ, c, mul_assoc, mul_left_comm, mul_comm] <;> ring

set_option maxHeartbeats 1000000 in

set_option backward.isDefEq.respectTransparency false in
theorem exists_moving_scalar_barrier_decay [T2Space M]
    {T : ℝ} {U : Set M} (hU : IsOpen U) {q : M → ℝ}
    (hq : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ q U)
    (F : RicciFlow n M (Set.Icc 0 T)) {C : Set M} (hC : IsCompact C) (hCU : C ⊆ U)
    {b : ℝ}
    (hcritical : ∀ t ∈ Set.Icc 0 T, ∀ x ∈ C,
      q x + b * t = 0 → mfderiv (𝓡 n) 𝓘(ℝ, ℝ) q x ≠ 0) :
    ∃ A : ℝ, 0 < A ∧ ∀ epsilon : ℝ, 0 ≤ epsilon → ∀ t ∈ Set.Icc 0 T, ∀ x ∈ C,
      epsilon * Real.exp (-A * t) *
          (-A * expNegInvGlue (q x + b * t) +
            b * deriv expNegInvGlue (q x + b * t)) ≤
        (F.connection t).laplacian
          (fun y ↦ epsilon * Real.exp (-A * t) *
            expNegInvGlue (q y + b * t)) x := by
  have hK : IsCompact (Set.Icc (0 : ℝ) T ×ˢ C) := isCompact_Icc.prod hC
  have hqP : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M ↦ q p.2) (Set.Icc 0 T ×ˢ U) := by
    exact hq.comp contMDiffOn_snd (fun _ hp ↦ hp.2)
  have hQ : ContinuousOn (fun p : ℝ × M ↦ q p.2 + b * p.1)
      (Set.Icc 0 T ×ˢ C) := by
    apply (hqP.continuousOn.mono (prod_mono Subset.rfl hCU)).add
    exact (continuous_const.mul continuous_fst).continuousOn
  have hL : ContinuousOn (fun p : ℝ × M ↦
      (F.connection p.1).laplacian q p.2) (Set.Icc 0 T ×ˢ C) := by
    apply (continuousOn_flow_laplacian F hU hq).mono
    exact prod_mono Subset.rfl hCU
  have hG : ContinuousOn (fun p : ℝ × M ↦
      scalarGradientSq (F.metric p.1) q p.2) (Set.Icc 0 T ×ˢ C) := by
    apply (continuousOn_flow_scalarGradientSq F hU hq).mono
    exact prod_mono Subset.rfl hCU
  have hGzero : ∀ p ∈ Set.Icc 0 T ×ˢ C,
      q p.2 + b * p.1 = 0 → scalarGradientSq (F.metric p.1) q p.2 > 0 := by
    intro p hp hz
    apply (scalarGradientSq_pos_iff (F.metric p.1) q p.2).2
    exact hcritical p.1 hp.1 p.2 hp.2 hz
  obtain ⟨A, hA, hbar⟩ := exists_exponential_barrier_decay (X := ℝ × M)
    (q := fun p : ℝ × M ↦ q p.2 + b * p.1)
    (L := fun p : ℝ × M ↦ (F.connection p.1).laplacian q p.2)
    (G := fun p : ℝ × M ↦ scalarGradientSq (F.metric p.1) q p.2)
    hK hQ hL hG hGzero b
  refine ⟨A, hA, ?_⟩
  intro epsilon hepsilon t ht x hx
  let c : ℝ := epsilon * Real.exp (-A * t)
  have hc : 0 ≤ c := mul_nonneg hepsilon (Real.exp_pos _).le
  have hineq := hbar (t, x) ⟨ht, hx⟩
  simp only [Prod.fst, Prod.snd] at hineq
  have hmul := mul_le_mul_of_nonneg_left hineq hc
  have hlap := laplacian_moving_scalar_barrier (F.connection t) hU hq A b epsilon t (hCU hx)
  rw [hlap]
  change c * (-A * expNegInvGlue (q x + b * t) +
      b * deriv expNegInvGlue (q x + b * t)) ≤
    c * (deriv expNegInvGlue (q x + b * t) * (F.connection t).laplacian q x +
      deriv (deriv expNegInvGlue) (q x + b * t) *
        scalarGradientSq (F.metric t) q x)
  nlinarith [hmul]

end PoincareConjecture.M04

