import PoincareConjecture.Proofs.M04.ShiBernsteinEnergy
import PoincareConjecture.Proofs.M04.ShiBarrierMaximum
import PoincareConjecture.Proofs.M04.ShiQuadraticMaximum
import PoincareConjecture.Proofs.M04.ScalarEstimates
import PoincareConjecture.Proofs.M04.ShiCutoffMaximum

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators
open Set Topology Filter

universe u

namespace PoincareConjecture.M04

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

set_option backward.isDefEq.respectTransparency false in
theorem mfderiv_eq_zero_of_isLocalMax {f : M → ℝ} {x : M}
    (hf : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f x) (hmax : IsLocalMax f x) :
    mfderiv (𝓡 n) 𝓘(ℝ, ℝ) f x = 0 := by
  apply ContinuousLinearMap.ext
  intro v
  let X := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v
  obtain ⟨γ, hγ0, hγ⟩ :=
    exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless 0
      (FiberBundle.contMDiffAt_extend (k := 1) (𝓡 n)
        (EuclideanSpace ℝ (Fin n)) v)
  have hmaxγ : IsLocalMax (f ∘ γ) 0 := by
    have htend : Tendsto γ (𝓝 0) (𝓝 x) := hγ0 ▸ hγ.continuousAt.tendsto
    filter_upwards [htend.eventually hmax] with t ht
    simpa [Function.comp_def, hγ0] using ht
  have hfγ : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f (γ 0) := by
    simpa [hγ0] using hf
  have hd : HasDerivAt (f ∘ γ)
      (mvfderiv (𝓡 n) f (γ 0) (X (γ 0))) 0 := by
    have hc := hfγ.hasMFDerivAt.comp 0 hγ.hasMFDerivAt
    rw [hasDerivAt_iff_hasFDerivAt, ← hasMFDerivAt_iff_hasFDerivAt]
    apply hc.congr_mfderiv
    ext
    simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.toSpanSingleton, LinearMap.toSpanSingleton, mvfderiv, X]
    change _ = (1 : ℝ) • (mfderiv (𝓡 n) 𝓘(ℝ, ℝ) f (γ 0)) (X (γ 0))
    rw [one_smul]
  have hz := hmaxγ.hasDerivAt_eq_zero hd
  have hz' : mvfderiv (𝓡 n) f x (X x) = 0 :=
    (congrArg (fun y => mvfderiv (𝓡 n) f y (X y)) hγ0).symm.trans hz
  change mvfderiv (𝓡 n) f x
    (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v x) = 0 at hz'
  rw [FiberBundle.extend_apply_self] at hz'
  change (mfderiv (𝓡 n) 𝓘(ℝ, ℝ) f x) v = 0 at hz'
  exact hz'

set_option backward.isDefEq.respectTransparency false in
private theorem contMDiffAt_mvfderiv_extend_one {f : M → ℝ} {x : M}
    (hf : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) 2 f x) (v : TangentSpace (𝓡 n) x) :
    ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) 1
      (fun y => mvfderiv (𝓡 n) f y
        (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v y)) x := by
  let X := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v
  have hϕ := hf.mfderiv_const (m := 1) (by norm_num)
  have hX := FiberBundle.contMDiffAt_extend
    (k := 1) (𝓡 n) (EuclideanSpace ℝ (Fin n)) v
  have hf1 : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) 1 f x := hf.of_le (by norm_num)
  have happ := ContMDiffAt.clm_apply_of_inCoordinates
    (F₁ := EuclideanSpace ℝ (Fin n)) (F₂ := ℝ)
    (B₁ := M) (B₂ := ℝ) (E₁ := fun y : M => TangentSpace (𝓡 n) y)
    (E₂ := fun y : ℝ => TangentSpace 𝓘(ℝ, ℝ) y)
    (b₁ := id) (b₂ := f) (m₀ := x)
    (ϕ := fun y => mfderiv (𝓡 n) 𝓘(ℝ, ℝ) f y)
    (v := X) hϕ hX hf1
  exact ((contMDiff_snd_tangentBundle_modelSpace (n := 1) ℝ 𝓘(ℝ, ℝ)) _).comp x happ

set_option maxHeartbeats 1200000 in

set_option backward.isDefEq.respectTransparency false in
theorem laplacian_mul_on (D : LeviCivitaData g) {U : Set M} {f h : M → ℝ}
    (hU : IsOpen U) (hf : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) 2 f U)
    (hh : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) 2 h U) {x : M} (hx : x ∈ U) :
    D.laplacian (fun y => f y * h y) x =
      f x * D.laplacian h x + h x * D.laplacian f x +
        2 * scalarGradientPairing g f h x := by
  have hfd {y : M} (hy : y ∈ U) :=
    (hf.contMDiffAt (hU.mem_nhds hy)).mdifferentiableAt (by norm_num)
  have hhd {y : M} (hy : y ∈ U) :=
    (hh.contMDiffAt (hU.mem_nhds hy)).mdifferentiableAt (by norm_num)
  have hprod {y : M} (hy : y ∈ U) (v : TangentSpace (𝓡 n) y) :
      mvfderiv (𝓡 n) (fun z => f z * h z) y v =
        f y * mvfderiv (𝓡 n) h y v + h y * mvfderiv (𝓡 n) f y v := by
    simp only [mvfderiv_fun_mul (hfd hy) (hhd hy),
      add_apply, smul_apply, smul_eq_mul]
  have hH (u v : TangentSpace (𝓡 n) x) :
      D.hessian (fun y => f y * h y) x u v =
        f x * D.hessian h x u v + h x * D.hessian f x u v +
          mvfderiv (𝓡 n) f x u * mvfderiv (𝓡 n) h x v +
          mvfderiv (𝓡 n) h x u * mvfderiv (𝓡 n) f x v := by
    let Y := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v
    let df := fun y => mvfderiv (𝓡 n) f y (Y y)
    let dh := fun y => mvfderiv (𝓡 n) h y (Y y)
    have hdf : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) df x :=
      (contMDiffAt_mvfderiv_extend_one (hf.contMDiffAt (hU.mem_nhds hx)) v).mdifferentiableAt
        (by norm_num)
    have hdh : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) dh x :=
      (contMDiffAt_mvfderiv_extend_one (hh.contMDiffAt (hU.mem_nhds hx)) v).mdifferentiableAt
        (by norm_num)
    have he : (fun y => mvfderiv (𝓡 n) (fun z => f z * h z) y (Y y)) =ᶠ[𝓝 x]
        (fun y => f y * dh y + h y * df y) := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact hprod hy (Y y)
    have hd : mvfderiv (𝓡 n)
        (fun y => mvfderiv (𝓡 n) (fun z => f z * h z) y (Y y)) x u =
        f x * mvfderiv (𝓡 n) dh x u +
          mvfderiv (𝓡 n) h x v * mvfderiv (𝓡 n) f x u +
          (h x * mvfderiv (𝓡 n) df x u +
            mvfderiv (𝓡 n) f x v * mvfderiv (𝓡 n) h x u) := by
      have hd' : mvfderiv (𝓡 n)
          (fun y => mvfderiv (𝓡 n) (fun z => f z * h z) y (Y y)) x =
          mvfderiv (𝓡 n) (fun y => f y * dh y + h y * df y) x := he.mfderiv_eq
      rw [hd']
      erw [mvfderiv_fun_add ((hfd hx).mul hdh) ((hhd hx).mul hdf),
        mvfderiv_fun_mul (hfd hx) hdh, mvfderiv_fun_mul (hhd hx) hdf]
      simp only [add_apply, smul_apply, smul_eq_mul, df, dh, Y,
        FiberBundle.extend_apply_self]
    change mvfderiv (𝓡 n)
      (fun y => mvfderiv (𝓡 n) (fun z => f z * h z) y (Y y)) x
        (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) u x) -
      mvfderiv (𝓡 n) (fun z => f z * h z) x
        (D.connection Y x (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) u x)) = _
    simp only [FiberBundle.extend_apply_self]
    rw [hd, hprod hx]
    simp only [LeviCivitaData.hessian, LeviCivitaData.hessianOnFields,
      FiberBundle.extend_apply_self]
    change _ = f x *
      (mvfderiv (𝓡 n) dh x u - mvfderiv (𝓡 n) h x (D.connection Y x u)) +
      h x * (mvfderiv (𝓡 n) df x u - mvfderiv (𝓡 n) f x (D.connection Y x u)) + _ + _
    ring
  simp only [LeviCivitaData.laplacian, hH, Finset.sum_add_distrib,
    ← Finset.mul_sum, scalarGradientPairing]
  have hcomm : (∑ i, mvfderiv (𝓡 n) h x (g.orthonormalBasis x i) *
      mvfderiv (𝓡 n) f x (g.orthonormalBasis x i)) = scalarGradientPairing g f h x := by
    unfold scalarGradientPairing
    apply Finset.sum_congr rfl
    intro i _
    exact mul_comm _ _
  rw [hcomm]
  unfold scalarGradientPairing
  ring

set_option backward.isDefEq.respectTransparency false in
theorem scalarGradientPairing_at_product_max {f h : M → ℝ} {x : M}
    (hf : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f x)
    (hh : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) h x)
    (hmax : IsLocalMax (fun y => f y * h y) x) :
    f x * scalarGradientPairing g f h x + h x * scalarGradientSq g f x = 0 := by
  have hz := mfderiv_eq_zero_of_isLocalMax (hf.mul hh) hmax
  change mfderiv (𝓡 n) 𝓘(ℝ, ℝ) (fun y => f y * h y) x = 0 at hz
  have hdir (v : TangentSpace (𝓡 n) x) :
      f x * mvfderiv (𝓡 n) h x v + h x * mvfderiv (𝓡 n) f x v = 0 := by
    have hv : mvfderiv (𝓡 n) (fun y => f y * h y) x v = 0 := by
      change (mfderiv (𝓡 n) 𝓘(ℝ, ℝ) (fun y => f y * h y) x) v = 0
      rw [hz]
      rfl
    simpa only [mvfderiv_fun_mul hf hh, add_apply, smul_apply, smul_eq_mul] using hv
  unfold scalarGradientPairing scalarGradientSq
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro i _
  have hi := congrArg (fun r => mvfderiv (𝓡 n) f x (g.orthonormalBasis x i) * r)
    (hdir (g.orthonormalBasis x i))
  nlinarith only [hi]

noncomputable def shiCutoffThreshold (c d L G Θ : ℝ) : ℝ :=
  max (2 * (1 / (2 * c)))
    (max 1 (4 * (d * Θ ^ 2 + 1 / (4 * c) + Θ * (L + 2 * G)) / c))

private theorem cutoff_contact_velocity_lt
    {κ c d L G Θ τ E q qd ed lq le p z ε : ℝ}
    (hκ : 0 ≤ κ) (hc : 0 < c) (hd : 0 ≤ d) (hL : 0 ≤ L)
    (hG : 0 ≤ G) (hΘ : 0 ≤ Θ) (hτ : 0 < τ) (hτΘ : τ ≤ Θ)
    (hE : 0 < E) (hE1 : E ≤ 1) (hq : 0 ≤ q)
    (hheat : qd - κ * lq ≤ -c * q ^ 2 + d)
    (heta : ed - κ * le ≤ L + ε) (hgrad : κ * z ≤ G * E)
    (hbalance : E * p + q * z = 0) (hmax : E * lq + q * le + 2 * p ≤ 0)
    (hW : shiCutoffThreshold c d L G Θ < τ * E * q) :
    E * q + τ * (ed * q + E * qd) < τ * q * ε := by
  let W := τ * E * q
  let b := 1 / (2 * c)
  let d0 := d * Θ ^ 2 + 1 / (4 * c)
  let V := E * q + τ * (ed * q + E * qd)
  let P := E * lq + q * le + 2 * p
  have hW0 : 0 ≤ W := mul_nonneg (mul_nonneg hτ.le hE.le) hq
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hd0 : 0 ≤ d0 := by dsimp [d0]; positivity
  have hR : -c * (W - E * b) ^ 2 + d0 * E ^ 2 + τ * (L + 2 * G) * W < 0 := by
    by_contra hnot
    have hi : c * (W - E * b) ^ 2 ≤ d0 * E ^ 2 + τ * (L + 2 * G) * W := by
      linarith [le_of_not_gt hnot]
    have hbnd := weighted_cutoff_quadratic_bound hc hb hd0 hL hG hΘ hτ hτΘ
      hE.le hE1 hW0 hi
    exact (not_le_of_gt hW) hbnd
  have ht2 : τ ^ 2 ≤ Θ ^ 2 := by nlinarith
  have htime : d * τ ^ 2 * E ^ 2 ≤ d * Θ ^ 2 * E ^ 2 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht2 hd) (sq_nonneg E)
  have hheat' := mul_le_mul_of_nonneg_left hheat
    (show 0 ≤ τ ^ 2 * E ^ 2 by positivity)
  have heta' := mul_le_mul_of_nonneg_left heta
    (show 0 ≤ τ ^ 2 * E * q by positivity)
  have hgrad' := mul_le_mul_of_nonneg_left hgrad
    (show 0 ≤ 2 * τ ^ 2 * q by positivity)
  have halg : τ * E * (V - κ * τ * P - τ * q * ε) =
      E * W + (τ ^ 2 * E ^ 2) * (qd - κ * lq) +
        (τ ^ 2 * E * q) * (ed - κ * le) + (2 * τ ^ 2 * q) * (κ * z) -
          τ ^ 2 * E * q * ε := by
    dsimp [V, P, W]
    linear_combination -2 * κ * τ ^ 2 * hbalance
  have hraw : τ * E * (V - κ * τ * P - τ * q * ε) ≤
      E * W - c * W ^ 2 + d * Θ ^ 2 * E ^ 2 + τ * (L + 2 * G) * W := by
    rw [halg]
    dsimp [W]
    nlinarith only [hheat', heta', hgrad', htime]
  have hcomplete : E * W - c * W ^ 2 + d * Θ ^ 2 * E ^ 2 + τ * (L + 2 * G) * W =
      -c * (W - E * b) ^ 2 + d0 * E ^ 2 + τ * (L + 2 * G) * W := by
    dsimp [b, d0]
    field_simp [ne_of_gt hc]
    ring
  rw [hcomplete] at hraw
  have hneg : V - κ * τ * P - τ * q * ε < 0 := by
    by_contra hn
    have hnonneg := mul_nonneg (mul_pos hτ hE).le (le_of_not_gt hn)
    exact (not_lt_of_ge hnonneg) (hraw.trans_lt hR)
  have hdiff : κ * τ * P ≤ 0 := mul_nonpos_of_nonneg_of_nonpos
    (mul_nonneg hκ hτ.le) hmax
  change V < τ * q * ε
  linarith

set_option maxHeartbeats 1600000 in

set_option backward.isDefEq.respectTransparency false in
theorem shi_cutoff_bound
    (g : ℝ → RiemannianMetric n M) (D : (t : ℝ) → LeviCivitaData (g t))
    {C : Set M} (hC : IsCompact C) {S κ c d L G Θ a I : ℝ}
    (hS : 0 < S) (hκ : 0 ≤ κ) (hc : 0 < c) (hd : 0 ≤ d)
    (hL : 0 ≤ L) (hG : 0 ≤ G) (ha : 0 ≤ a) (hI : 0 ≤ I) (hcap : a + S ≤ Θ)
    (Q η : ℝ → M → ℝ)
    (hQ : ContinuousOn (Function.uncurry Q) (Icc 0 S ×ˢ C))
    (hη : ContinuousOn (Function.uncurry η) (Icc 0 S ×ˢ C))
    (hQ0 : ∀ t ∈ Icc 0 S, ∀ x ∈ C, 0 ≤ Q t x)
    (hη0 : ∀ t ∈ Icc 0 S, ∀ x ∈ C, 0 ≤ η t x)
    (hη1 : ∀ t ∈ Icc 0 S, ∀ x ∈ C, η t x ≤ 1)
    (hboundary : ∀ t ∈ Icc 0 S, ∀ x ∈ C \ interior C, η t x = 0)
    (hinit : ∀ x ∈ C, a * η 0 x * Q 0 x ≤ I)
    (hspace : ∀ t ∈ Ioc 0 S, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (Q t))
    (hheat : ∀ t ∈ Ioc 0 S, ∀ x ∈ interior C, ∃ qd : ℝ,
      HasDerivWithinAt (fun s => Q s x) qd (Icc 0 t) t ∧
        qd - κ * (D t).laplacian (Q t) x ≤ -c * Q t x ^ 2 + d)
    (hsupport : ∀ t ∈ Ioc 0 S, ∀ x ∈ interior C, 0 < η t x →
      ∀ ε > 0, ∃ e : ℝ → M → ℝ, ∃ ed : ℝ, ∃ U : Set M,
        IsOpen U ∧ x ∈ U ∧ ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (e t) U ∧
        e t x = η t x ∧ (∀ᶠ y in 𝓝 x, e t y ≤ η t y) ∧
        (∀ᶠ s in 𝓝[Icc 0 t] t, e s x ≤ η s x) ∧
        HasDerivWithinAt (fun s => e s x) ed (Icc 0 t) t ∧
        κ * scalarGradientSq (g t) (e t) x ≤ G * η t x ∧
        ed - κ * (D t).laplacian (e t) x ≤ L + ε) :
    ∀ t ∈ Icc 0 S, ∀ x ∈ C,
      (a + t) * η t x * Q t x ≤ max I (shiCutoffThreshold c d L G Θ) := by
  let B := max I (shiCutoffThreshold c d L G Θ)
  let f : ℝ → M → ℝ := fun s y => B - (a + s) * η s y * Q s y
  have hB0 : 0 ≤ B := hI.trans (le_max_left _ _)
  have hΘ : 0 ≤ Θ := le_trans (by linarith : 0 ≤ a + S) hcap
  have hinitial : ∀ x ∈ C, 0 ≤ f 0 x := by
    intro x hx
    dsimp [f]
    simpa only [add_zero] using sub_nonneg.mpr ((hinit x hx).trans (le_max_left _ _))
  have hbnd : ∀ t ∈ Icc 0 S, ∀ x ∈ C \ interior C, 0 ≤ f t x := by
    intro t ht x hx
    simpa only [f, hboundary t ht x hx, mul_zero, zero_mul, sub_zero] using hB0
  have hf : ContinuousOn (Function.uncurry f) (Icc 0 S ×ˢ C) :=
    continuousOn_const.sub
      (((continuous_const.add continuous_fst).continuousOn.mul hη).mul hQ)
  have hs : ∀ t ∈ Ioc 0 S, ∀ x ∈ interior C,
      (∀ y ∈ C, f t x ≤ f t y) → f t x < 0 →
      ∀ δ > 0, ∃ ψ : ℝ → ℝ, ∃ v : ℝ,
        ψ t = f t x ∧ (∀ᶠ s in 𝓝[ Icc 0 t ] t, f s x ≤ ψ s) ∧
        HasDerivWithinAt ψ v (Icc 0 t) t ∧ -0 * f t x - δ ≤ v := by
    intro t ht x hx hmin hneg δ hδ
    have htS : t ∈ Icc 0 S := ⟨ht.1.le, ht.2⟩
    have hxC : x ∈ C := interior_subset hx
    have hτ : 0 < a + t := add_pos_of_nonneg_of_pos ha ht.1
    have hτΘ : a + t ≤ Θ := by linarith [ht.2]
    have hq0 := hQ0 t htS x hxC
    have he0 := hη0 t htS x hxC
    have he1 := hη1 t htS x hxC
    have hW : B < (a + t) * η t x * Q t x := by
      change B - (a + t) * η t x * Q t x < 0 at hneg
      linarith
    have hepos : 0 < η t x := by
      by_contra hnot
      have hez : η t x = 0 := le_antisymm (le_of_not_gt hnot) he0
      rw [hez, mul_zero, zero_mul] at hW
      exact (not_lt_of_ge hB0) hW
    let ε := δ / (1 + (a + t) * Q t x)
    have hden : 0 < 1 + (a + t) * Q t x := by positivity
    have hε : 0 < ε := div_pos hδ hden
    obtain ⟨e, ed, U, hU, hxU, he, heq, heSpace, heTime, hed, heGrad, heHeat⟩ :=
      hsupport t ht x hx hepos ε hε
    obtain ⟨qd, hqd, hHeat⟩ := hheat t ht x hx
    have hmax : IsLocalMax (fun y => e t y * Q t y) x := by
      filter_upwards [heSpace, isOpen_interior.mem_nhds hx] with y hey hy
      have hyC : y ∈ C := interior_subset hy
      have hprod : η t y * Q t y ≤ η t x * Q t x := by
        apply le_of_mul_le_mul_left (a := a + t) _ hτ
        have hmy := hmin y hyC
        dsimp [f] at hmy
        nlinarith only [hmy]
      calc
        e t y * Q t y ≤ η t y * Q t y :=
          mul_le_mul_of_nonneg_right hey (hQ0 t htS y hyC)
        _ ≤ η t x * Q t x := hprod
        _ = e t x * Q t x := by rw [heq]
    have hedif := (he.contMDiffAt (hU.mem_nhds hxU)).mdifferentiableAt (by simp)
    have hqdif := (hspace t ht x).mdifferentiableAt (by simp)
    have hbalance := scalarGradientPairing_at_product_max (g := g t) hedif hqdif hmax
    rw [heq] at hbalance
    have hLap := laplacian_nonpos_of_isLocalMax (D t)
      ((he.contMDiffAt (hU.mem_nhds hxU)).mul (hspace t ht x)) hmax
    change (D t).laplacian (fun y => e t y * Q t y) x ≤ 0 at hLap
    have htwo : (2 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) := by
      exact WithTop.coe_le_coe.mpr le_top
    rw [laplacian_mul_on (D t) hU (he.of_le htwo)
      ((hspace t ht).contMDiffOn.of_le htwo) hxU, heq] at hLap
    have hV := cutoff_contact_velocity_lt hκ hc hd hL hG hΘ hτ hτΘ hepos he1 hq0
      hHeat heHeat heGrad hbalance hLap ((le_max_right _ _).trans_lt hW)
    let V := η t x * Q t x + (a + t) * (ed * Q t x + η t x * qd)
    have hVδ : V ≤ δ := by
      have heps : (a + t) * Q t x * ε ≤ δ := by
        have heqδ : (1 + (a + t) * Q t x) * ε = δ := by
          dsimp [ε]
          exact mul_div_cancel₀ δ (ne_of_gt hden)
        nlinarith only [heqδ, hε]
      exact hV.le.trans heps
    let ψ : ℝ → ℝ := fun s => B - (a + s) * e s x * Q s x
    refine ⟨ψ, -V, ?_, ?_, ?_, ?_⟩
    · dsimp [ψ, f]
      rw [heq]
    · filter_upwards [heTime, self_mem_nhdsWithin] with s hes hs
      have hsS : s ∈ Icc 0 S := ⟨hs.1, hs.2.trans ht.2⟩
      exact sub_le_sub_left
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hes (add_nonneg ha hs.1))
          (hQ0 s hsS x hxC)) B
    · have hweight : HasDerivWithinAt (fun s : ℝ => a + s) 1 (Icc 0 t) t :=
        ((hasDerivAt_id t).const_add a).hasDerivWithinAt
      have hprod := (hweight.mul hed).mul hqd
      have hvalue : (1 * e t x + (a + t) * ed) * Q t x +
          ((a + t) * e t x) * qd = V := by
        dsimp only [V]
        rw [heq]
        ring
      have hd := hprod.congr_deriv hvalue
      convert! hd.const_sub B using 1
    · simpa only [neg_zero, zero_mul, zero_sub] using neg_le_neg hVδ
  have hresult := compact_subset_min_velocity_nonnegative_of_upper_support
    hC hS f hinitial hbnd hf hs
  intro t ht x hx
  exact sub_nonneg.mp (hresult t ht x hx)

end PoincareConjecture.M04
