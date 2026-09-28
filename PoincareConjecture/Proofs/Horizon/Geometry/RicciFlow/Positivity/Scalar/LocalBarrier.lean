import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Positivity.Scalar.MovingBarrier
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.Maximum.CompactSlab











set_option autoImplicit false

open scoped Manifold ContDiff Bundle
open Set Topology Filter

universe u

namespace PoincareConjecture.RicciFlowAnalysis

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

set_option maxHeartbeats 1000000 in

set_option backward.isDefEq.respectTransparency false in
theorem laplacian_sub_of_contMDiffOn {g : RiemannianMetric n M}
    (D : LeviCivitaData g) {U : Set M} (hU : IsOpen U) {f q : M → ℝ}
    (hf : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f U)
    (hq : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ q U) {x : M} (hx : x ∈ U) :
    D.laplacian (fun y ↦ f y - q y) x = D.laplacian f x - D.laplacian q x := by
  have hfd {y : M} (hy : y ∈ U) : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f y :=
    (hf.contMDiffAt (hU.mem_nhds hy)).mdifferentiableAt (by simp)
  have hqd {y : M} (hy : y ∈ U) : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) q y :=
    (hq.contMDiffAt (hU.mem_nhds hy)).mdifferentiableAt (by simp)
  have hH (a b : TangentSpace (𝓡 n) x) :
      D.hessian (fun y ↦ f y - q y) x a b = D.hessian f x a b - D.hessian q x a b := by
    let X := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) a
    let Y := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) b
    let df := fun y ↦ mvfderiv (𝓡 n) f y (Y y)
    let dq := fun y ↦ mvfderiv (𝓡 n) q y (Y y)
    have hdf : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) df x :=
      (contMDiffAt_directional_derivative (hf.contMDiffAt (hU.mem_nhds hx))
        (FiberBundle.contMDiffAt_extend (k := ∞) (𝓡 n)
          (EuclideanSpace ℝ (Fin n)) b)).mdifferentiableAt (by simp)
    have hdq : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) dq x :=
      (contMDiffAt_directional_derivative (hq.contMDiffAt (hU.mem_nhds hx))
        (FiberBundle.contMDiffAt_extend (k := ∞) (𝓡 n)
          (EuclideanSpace ℝ (Fin n)) b)).mdifferentiableAt (by simp)
    have heq : (fun y ↦ mvfderiv (𝓡 n) (fun z ↦ f z - q z) y (Y y)) =ᶠ[𝓝 x]
        (fun y ↦ df y - dq y) := by
      filter_upwards [hU.mem_nhds hx] with y hy
      erw [mvfderiv_sub (hfd hy) (hqd hy)]
      rfl
    have he : mvfderiv (𝓡 n) (fun y ↦ mvfderiv (𝓡 n) (fun z ↦ f z - q z) y (Y y)) x =
        mvfderiv (𝓡 n) (fun y ↦ df y - dq y) x := heq.mfderiv_eq
    change mvfderiv (𝓡 n)
        (fun y ↦ mvfderiv (𝓡 n) (fun z ↦ f z - q z) y (Y y)) x (X x) -
        mvfderiv (𝓡 n) (fun z ↦ f z - q z) x (D.connection Y x (X x)) =
      (mvfderiv (𝓡 n) df x (X x) - mvfderiv (𝓡 n) f x (D.connection Y x (X x))) -
        (mvfderiv (𝓡 n) dq x (X x) - mvfderiv (𝓡 n) q x (D.connection Y x (X x)))
    rw [he]
    erw [mvfderiv_sub hdf hdq, mvfderiv_sub (hfd hx) (hqd hx)]
    simp only [sub_apply]
    ring
  simp only [LeviCivitaData.laplacian, hH, Finset.sum_sub_distrib]

set_option maxHeartbeats 1000000 in

set_option backward.isDefEq.respectTransparency false in
theorem exists_moving_scalar_barrier_decay_Icc [T2Space M]
    {J : Set ℝ} (F : RicciFlow n M J) {a b : ℝ} (hJ : Icc a b ⊆ J)
    {U : Set M} (hU : IsOpen U) {q : M → ℝ}
    (hq : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ q U)
    {C : Set M} (hC : IsCompact C) (hCU : C ⊆ U) {speed : ℝ}
    (hcritical : ∀ t ∈ Icc a b, ∀ x ∈ C,
      q x + speed * (t - a) = 0 → mfderiv (𝓡 n) 𝓘(ℝ, ℝ) q x ≠ 0) :
    ∃ A : ℝ, 0 < A ∧ ∀ epsilon : ℝ, 0 ≤ epsilon → ∀ t ∈ Icc a b, ∀ x ∈ C,
      epsilon * Real.exp (-A * (t - a)) *
          (-A * expNegInvGlue (q x + speed * (t - a)) +
            speed * deriv expNegInvGlue (q x + speed * (t - a))) ≤
        (F.connection t).laplacian
          (fun y ↦ epsilon * Real.exp (-A * (t - a)) *
            expNegInvGlue (q y + speed * (t - a))) x := by
  have hK : IsCompact (Icc a b ×ˢ C) := isCompact_Icc.prod hC
  have hqP : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M ↦ q p.2) (Icc a b ×ˢ U) :=
    hq.comp contMDiffOn_snd (fun _ hp ↦ hp.2)
  have hQ : ContinuousOn (fun p : ℝ × M ↦ q p.2 + speed * (p.1 - a))
      (Icc a b ×ˢ C) :=
    (hqP.continuousOn.mono (prod_mono Subset.rfl hCU)).add
      (continuous_const.mul (continuous_fst.sub continuous_const)).continuousOn
  have hL : ContinuousOn (fun p : ℝ × M ↦ (F.connection p.1).laplacian q p.2)
      (Icc a b ×ˢ C) :=
    (continuousOn_flow_laplacian F hU hq).mono (prod_mono hJ hCU)
  have hG : ContinuousOn (fun p : ℝ × M ↦ scalarGradientSq (F.metric p.1) q p.2)
      (Icc a b ×ˢ C) :=
    (continuousOn_flow_scalarGradientSq F hU hq).mono (prod_mono hJ hCU)
  have hGzero : ∀ p ∈ Icc a b ×ˢ C,
      q p.2 + speed * (p.1 - a) = 0 → 0 < scalarGradientSq (F.metric p.1) q p.2 := by
    intro p hp hz
    exact (scalarGradientSq_pos_iff (F.metric p.1) q p.2).2
      (hcritical p.1 hp.1 p.2 hp.2 hz)
  obtain ⟨A, hA, hbar⟩ := exists_exponential_barrier_decay (X := ℝ × M)
    (q := fun p : ℝ × M ↦ q p.2 + speed * (p.1 - a))
    (L := fun p : ℝ × M ↦ (F.connection p.1).laplacian q p.2)
    (G := fun p : ℝ × M ↦ scalarGradientSq (F.metric p.1) q p.2)
    hK hQ hL hG hGzero speed
  refine ⟨A, hA, ?_⟩
  intro epsilon hepsilon t ht x hx
  have hc : 0 ≤ epsilon * Real.exp (-A * (t - a)) :=
    mul_nonneg hepsilon (Real.exp_pos _).le
  have hineq := hbar (t, x) ⟨ht, hx⟩
  have hmul := mul_le_mul_of_nonneg_left hineq hc
  rw [laplacian_moving_scalar_barrier (F.connection t) hU hq A speed epsilon
    (t - a) (hCU hx)]
  nlinarith [hmul]

set_option maxHeartbeats 1000000 in

set_option backward.isDefEq.respectTransparency false in
theorem ricciFlow_compactDomain_moving_barrier [T2Space M]
    {J : Set ℝ} {a b : ℝ} (hab : a < b) (F : RicciFlow n M J)
    (hJ : Icc a b ⊆ J) {U C : Set M}
    (hU : IsOpen U) (hC : IsCompact C) (hCU : C ⊆ U)
    {q : M → ℝ} (hq : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ q U) {speed : ℝ}
    (hcritical : ∀ t ∈ Icc a b, ∀ x ∈ C,
      q x + speed * (t - a) = 0 → mfderiv (𝓡 n) 𝓘(ℝ, ℝ) q x ≠ 0)
    (f v : ℝ → M → ℝ)
    (hf : ContinuousOn (Function.uncurry f) (Icc a b ×ˢ C))
    (hderiv : ∀ t ∈ Icc a b, ∀ x ∈ C,
      HasDerivWithinAt (fun s ↦ f s x) (v t x) (Icc a b) t)
    (hsmooth : ∀ t ∈ Icc a b, ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (f t) U)
    (hnonneg : ∀ t ∈ Icc a b, ∀ x ∈ C, 0 ≤ f t x)
    (hevol : ∀ t ∈ Ioc a b, ∀ x ∈ interior C,
      (F.connection t).laplacian (f t) x ≤ v t x)
    (hboundary : ∀ t ∈ Icc a b, ∀ x ∈ C \ interior C,
      q x + speed * (t - a) ≤ 0) :
    ∃ A : ℝ, 0 < A ∧ ∀ epsilon : ℝ, 0 ≤ epsilon →
      (∀ x ∈ C, epsilon * expNegInvGlue (q x) ≤ f a x) →
      ∀ t ∈ Icc a b, ∀ x ∈ C,
        epsilon * Real.exp (-A * (t - a)) *
          expNegInvGlue (q x + speed * (t - a)) ≤ f t x := by
  obtain ⟨A, hA, hbar⟩ := exists_moving_scalar_barrier_decay_Icc F hJ hU hq hC hCU hcritical
  refine ⟨A, hA, ?_⟩
  intro epsilon hepsilon hinit
  let B : ℝ → M → ℝ := fun t x ↦ epsilon * Real.exp (-A * (t - a)) *
    expNegInvGlue (q x + speed * (t - a))
  let Bd : ℝ → M → ℝ := fun t x ↦ epsilon * Real.exp (-A * (t - a)) *
    (-A * expNegInvGlue (q x + speed * (t - a)) +
      speed * deriv expNegInvGlue (q x + speed * (t - a)))
  have hqC : ContinuousOn (fun p : ℝ × M ↦ q p.2) (Icc a b ×ˢ C) :=
    hq.continuousOn.comp continuous_snd.continuousOn (fun _ hp ↦ hCU hp.2)
  have hBC : ContinuousOn (Function.uncurry B) (Icc a b ×ˢ C) :=
    (continuousOn_const.mul
      ((continuous_const.mul (continuous_fst.sub continuous_const)).rexp.continuousOn)).mul
      ((expNegInvGlue.contDiff (n := (⊤ : ℕ∞))).continuous.comp_continuousOn
        (hqC.add (continuous_const.mul (continuous_fst.sub continuous_const)).continuousOn))
  have hBs (t : ℝ) : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (B t) U :=
    contMDiffOn_const.mul
      (expNegInvGlue.contDiff.contMDiff.comp_contMDiffOn (hq.add contMDiffOn_const))
  have hBd (t : ℝ) (x : M) :
      HasDerivAt (fun s ↦ B s x) (Bd t x) t := by
    have h := (hasDerivAt_moving_scalar_barrier q A speed epsilon (t - a) x).comp t
      ((hasDerivAt_id t).sub_const a)
    simpa only [Function.comp_def, id_eq, mul_one] using h
  have hwc : ContinuousOn (fun p : ℝ × M ↦ f p.1 p.2 - B p.1 p.2)
      (Icc a b ×ˢ C) := hf.sub hBC
  have hwd : ∀ t ∈ Icc a b, ∀ x ∈ C,
      HasDerivWithinAt (fun s ↦ f s x - B s x) (v t x - Bd t x) (Icc a b) t := by
    intro t ht x hx
    exact (hderiv t ht x hx).sub (hBd t x).hasDerivWithinAt
  have hwi : ∀ x ∈ C, 0 ≤ f a x - B a x := by
    intro x hx
    simpa only [B, sub_self, mul_zero, Real.exp_zero, mul_one, add_zero] using
      sub_nonneg.mpr (hinit x hx)
  have hws : ∀ t ∈ Icc a b,
      ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun x ↦ f t x - B t x) U := by
    intro t ht
    exact (hsmooth t ht).sub (hBs t)
  have hwb : ∀ t ∈ Icc a b, ∀ x ∈ C \ interior C, 0 ≤ f t x - B t x := by
    intro t ht x hx
    have hz := expNegInvGlue.zero_of_nonpos (hboundary t ht x hx)
    simpa only [B, hz, mul_zero, sub_zero] using hnonneg t ht x hx.1
  have hwe : ∀ t ∈ Ioc a b, ∀ x ∈ interior C,
      (F.connection t).laplacian (fun y ↦ f t y - B t y) x -
        0 * (f t x - B t x) ≤ v t x - Bd t x := by
    intro t ht x hx
    have ht' : t ∈ Icc a b := ⟨ht.1.le, ht.2⟩
    have hx' : x ∈ C := interior_subset hx
    rw [laplacian_sub_of_contMDiffOn (F.connection t) hU (hsmooth t ht')
      (hBs t) (hCU hx'), zero_mul, sub_zero]
    have hb : Bd t x ≤ (F.connection t).laplacian (B t) x :=
      hbar epsilon hepsilon t ht' x hx'
    linarith [hevol t ht x hx]
  have hw := ricciFlow_compactDomain_supersolution_nonnegative_Icc
    (K := 0) hab F hJ hU hC hCU (fun t x ↦ f t x - B t x)
    (fun t x ↦ v t x - Bd t x) hwc hwd hwi hws hwb hwe
  intro t ht x hx
  exact sub_nonneg.mp (hw t ht x hx)

end PoincareConjecture.RicciFlowAnalysis
