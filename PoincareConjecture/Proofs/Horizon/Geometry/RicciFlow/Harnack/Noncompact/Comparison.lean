import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.Barriers
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.Exhaustion.Proper
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.NoncompactMaximum
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Linearity
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Extrema

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.RicciFlow

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] {J : Set ℝ}
  {F : RicciFlow n M J} {O : M}

theorem SmoothExhaustion.nonpos_of_heat_le_mul
    (S : SmoothExhaustion F O)
    (hproper : ∀ r : ℝ, IsCompact {x | S.toFun x ≤ r})
    {u du : M → ℝ → ℝ} {C B T : ℝ}
    (hC : 0 ≤ C) (hT : Icc 0 T ⊆ J)
    (hu : ContinuousOn (Function.uncurry u) (univ ×ˢ Icc 0 T))
    (hsmooth : ∀ t ∈ Icc 0 T,
      ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun x => u x t))
    (hderiv : ∀ x t, t ∈ Ioc 0 T →
      HasDerivWithinAt (u x) (du x t) (Icc 0 T) t)
    (hbound : ∀ x t, t ∈ Icc 0 T → u x t ≤ B)
    (hheat : ∀ x t, t ∈ Ioc 0 T →
      du x t - (F.connection t).laplacian (fun y => u y t) x ≤ C * u x t)
    (hinit : ∀ x, u x 0 ≤ 0) :
    ∀ x t, t ∈ Icc 0 T → u x t ≤ 0 := by
  intro x t ht
  by_contra hnot
  have hpos : 0 < u x t := lt_of_not_ge hnot
  let A := C + (n : ℝ) * S.bound + 1
  have hL : 0 ≤ (n : ℝ) * S.bound := mul_nonneg (Nat.cast_nonneg _) S.bound_nonneg
  have hA : 0 < A := by dsimp [A]; linarith
  have hrate : C + (n : ℝ) * S.bound < A := by dsimp [A]; linarith
  obtain ⟨ε, hε, hsmall⟩ := S.exists_small_exp_mul
    (isCompact_singleton : IsCompact {x}) (half_pos hpos) A T hA.le
  let φ : M → ℝ → ℝ := fun y s => ε * Real.exp (A * s) * S.toFun y
  let v : M → ℝ → ℝ := fun y s => u y s - φ y s
  let dv : M → ℝ → ℝ := fun y s => du y s - A * φ y s
  have hφsmooth (s : ℝ) : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y => φ y s) :=
    contMDiff_const.mul S.smooth
  have hφcontinuous : Continuous (Function.uncurry φ) :=
    (continuous_const.mul (Real.continuous_exp.comp
      (continuous_const.mul continuous_snd))).mul
      (S.smooth.continuous.comp continuous_fst)
  have hv : ContinuousOn (Function.uncurry v) (univ ×ˢ Icc 0 T) :=
    hu.sub hφcontinuous.continuousOn
  have hdv : ∀ y s, s ∈ Ioc 0 T →
      HasDerivWithinAt (v y) (dv y s) (Icc 0 T) s := by
    intro y s hs
    exact (hderiv y s hs).sub (S.hasDerivAt_exp_mul ε A s y).hasDerivWithinAt
  have hlocalization : ∃ K : Set M, IsCompact K ∧
      ∀ y ∉ K, ∀ s ∈ Icc 0 T, v y s ≤ 0 := by
    have hlower (y : M) (s : Icc 0 T) : ε * S.toFun y ≤ φ y s := by
      have he : 1 ≤ Real.exp (A * (s : ℝ)) :=
        Real.one_le_exp (mul_nonneg hA.le s.property.1)
      have hh : 0 ≤ S.toFun y := by linarith [S.one_le y]
      dsimp [φ]
      exact mul_le_mul_of_nonneg_right (by nlinarith) hh
    obtain ⟨K, hK, hout⟩ := Poincare.Parabolic.exists_compact_nonpos_outside_of_barrier
      (I := Icc 0 T) hproper hε (u := fun y s => u y s) (φ := fun y s => φ y s)
      (fun y s => hbound y s s.property) hlower
    exact ⟨K, hK, fun y hy s hs => hout y hy ⟨s, hs⟩⟩
  obtain ⟨K, hK, hout⟩ := hlocalization
  have hvinit (y) : v y 0 ≤ 0 := by
    have hp := S.le_exp_mul hε.le hA.le (le_refl (0 : ℝ)) y
    dsimp [v, φ]
    linarith [hinit y]
  have hvmax : ∀ y s, s ∈ Ioc 0 T → 0 < v y s →
      (∀ z, v z s ≤ v y s) → dv y s ≤ C * v y s := by
    intro y s hs _ hmax
    have hs' : s ∈ Icc 0 T := ⟨hs.1.le, hs.2⟩
    have hvs : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun z => v z s) :=
      (hsmooth s hs').sub (hφsmooth s)
    have hlap := (F.connection s).laplacian_nonpos_of_isLocalMax hvs
      (Filter.Eventually.of_forall hmax)
    have hφheat := S.exp_mul_heat_gt hε hrate (hT hs') y
    rw [(S.hasDerivAt_exp_mul ε A s y).deriv] at hφheat
    have hsub := (F.connection s).laplacian_sub (hsmooth s hs') (hφsmooth s) y
    change (F.connection s).laplacian (fun z => v z s) y =
      (F.connection s).laplacian (fun z => u z s) y -
        (F.connection s).laplacian (fun z => φ z s) y at hsub
    rw [hsub] at hlap
    change C * φ y s < A * φ y s -
      (F.connection s).laplacian (fun z => φ z s) y at hφheat
    dsimp only [dv, v]
    nlinarith [hheat y s hs]
  have hvnonpos := Poincare.Parabolic.nonpos_of_deriv_le_mul_at_max_of_nonpos_outside_compact
    hK hv hdv hvmax hvinit hout x t ht
  have hsmall' := hsmall t ht x rfl
  change u x t - ε * Real.exp (A * t) * S.toFun x ≤ 0 at hvnonpos
  linarith

theorem SmoothExhaustion.nonpos_of_heat_le_mul_of_metricComplete
    [T3Space M] [PreconnectedSpace M] (S : SmoothExhaustion F O)
    {t₀ : ℝ} (ht₀ : t₀ ∈ J) (hcomplete : MetricComplete (F.metric t₀))
    {u du : M → ℝ → ℝ} {C B T : ℝ}
    (hC : 0 ≤ C) (hT : Icc 0 T ⊆ J)
    (hu : ContinuousOn (Function.uncurry u) (univ ×ˢ Icc 0 T))
    (hsmooth : ∀ t ∈ Icc 0 T,
      ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun x => u x t))
    (hderiv : ∀ x t, t ∈ Ioc 0 T →
      HasDerivWithinAt (u x) (du x t) (Icc 0 T) t)
    (hbound : ∀ x t, t ∈ Icc 0 T → u x t ≤ B)
    (hheat : ∀ x t, t ∈ Ioc 0 T →
      du x t - (F.connection t).laplacian (fun y => u y t) x ≤ C * u x t)
    (hinit : ∀ x, u x 0 ≤ 0) :
    ∀ x t, t ∈ Icc 0 T → u x t ≤ 0 :=
  S.nonpos_of_heat_le_mul (S.isCompact_sublevel_of_metricComplete ht₀ hcomplete)
    hC hT hu hsmooth hderiv hbound hheat hinit

end PoincareConjecture.RicciFlow
