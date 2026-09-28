import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Convexity.NormalizedGradient
import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

open PoincareConjecture Filter Set
open scoped ContDiff Topology Manifold Bundle

namespace Poincare.Geometry.Riemannian.Convexity

theorem exists_local_normalizedNegGradient_integralCurve
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    {f : M → ℝ} {x : M} (hf : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f x)
    (hregular : g.inner x (D.gradient f x) (D.gradient f x) ≠ 0) :
    ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurveAt γ (normalizedNegGradient D f) 0 := by
  apply exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless (I := 𝓡 n) 0
  exact (contMDiffAt_normalizedNegGradient D hf hregular).of_le (by simp)

variable {n : ℕ} {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}

theorem hasDerivAt_comp_normalizedNegGradient
    (D : LeviCivitaData g) {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {γ : ℝ → EuclideanSpace ℝ (Fin n)} {t : ℝ}
    (hf : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f (γ t))
    (hregular : g.inner (γ t) (D.gradient f (γ t)) (D.gradient f (γ t)) ≠ 0)
    (hγ : HasDerivAt γ (normalizedNegGradient D f (γ t)) t) :
    HasDerivAt (f ∘ γ) (-1) t := by
  have hd := ((contMDiffAt_iff_contDiffAt.mp hf).differentiableAt (by simp)).hasFDerivAt
  have h := hd.comp_hasDerivAt t hγ
  have he : fderiv ℝ f (γ t) (normalizedNegGradient D f (γ t)) = -1 := by
    have he := mvfderiv_normalizedNegGradient D f (γ t) hregular
    simp [mvfderiv, mfderiv_eq_fderiv, NormedSpace.fromTangentSpace] at he
    convert! he using 1
  exact h.congr_deriv he

theorem comp_normalizedNegGradient_eq_sub
    (D : LeviCivitaData g) {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {γ : ℝ → EuclideanSpace ℝ (Fin n)} {a b : ℝ}
    (hf : ∀ t ∈ Icc a b, ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f (γ t))
    (hregular : ∀ t ∈ Icc a b,
      g.inner (γ t) (D.gradient f (γ t)) (D.gradient f (γ t)) ≠ 0)
    (hγ : ∀ t ∈ Icc a b, HasDerivAt γ (normalizedNegGradient D f (γ t)) t) :
    ∀ t ∈ Icc a b, f (γ t) = f (γ a) - (t - a) := by
  have hd (t : ℝ) (ht : t ∈ Icc a b) : HasDerivAt (f ∘ γ) (-1) t :=
    hasDerivAt_comp_normalizedNegGradient D (hf t ht) (hregular t ht) (hγ t ht)
  have hl (t : ℝ) : HasDerivAt (fun s => f (γ a) - (s - a)) (-1) t := by
    simpa using ((hasDerivAt_id t).sub_const a).const_sub (f (γ a))
  exact eq_of_has_deriv_right_eq
    (fun t ht => (hd t ⟨ht.1, ht.2.le⟩).hasDerivWithinAt)
    (fun t _ => (hl t).hasDerivWithinAt)
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t _ => (hl t).continuousAt.continuousWithinAt) (by simp)

theorem normalized_flow_preserves_level_differential
    (D : LeviCivitaData g) {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {q : ℝ × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {a b : ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hq : ∀ t ∈ Icc a b, ContDiffAt ℝ ∞ q (t, x))
    (hf : ∀ᶠ y in 𝓝 x, ∀ t ∈ Icc a b,
      ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f (q (t, y)))
    (hregular : ∀ᶠ y in 𝓝 x, ∀ t ∈ Icc a b,
      g.inner (q (t, y)) (D.gradient f (q (t, y))) (D.gradient f (q (t, y))) ≠ 0)
    (htime : ∀ᶠ y in 𝓝 x, ∀ t ∈ Icc a b,
      HasDerivAt (fun s => q (s, y)) (normalizedNegGradient D f (q (t, y))) t)
    (v : EuclideanSpace ℝ (Fin n)) (t : ℝ) (ht : t ∈ Icc a b) :
    mvfderiv (𝓡 n) f (q (t, x)) (fderiv ℝ (fun y => q (t, y)) x v) =
      mvfderiv (𝓡 n) f (q (a, x)) (fderiv ℝ (fun y => q (a, y)) x v) := by
  have ha : a ∈ Icc a b := ⟨le_rfl, ht.1.trans ht.2⟩
  have he : (fun y => f (q (t, y))) =ᶠ[𝓝 x]
      fun y => f (q (a, y)) - (t - a) := by
    filter_upwards [hf, hregular, htime] with y hy hr hytime
    exact comp_normalizedNegGradient_eq_sub D hy hr hytime t ht
  have hqd (s : ℝ) (hs : s ∈ Icc a b) :
      DifferentiableAt ℝ (fun y => q (s, y)) x :=
    ((hq s hs).differentiableAt (by simp)).comp x
      (differentiableAt_const s |>.prodMk differentiableAt_id)
  have hfd (s : ℝ) (hs : s ∈ Icc a b) : DifferentiableAt ℝ f (q (s, x)) :=
    (contMDiffAt_iff_contDiffAt.mp (hf.self_of_nhds s hs)).differentiableAt (by simp)
  have hleft := (hfd t ht).hasFDerivAt.comp x (hqd t ht).hasFDerivAt
  have hright := ((hfd a ha).hasFDerivAt.comp x (hqd a ha).hasFDerivAt).sub_const (t - a)
  have hd := congrArg (fun A => A v) (hleft.unique (hright.congr_of_eventuallyEq he))
  simp [mvfderiv, mfderiv_eq_fderiv, NormedSpace.fromTangentSpace]
  convert! hd using 1

end Poincare.Geometry.Riemannian.Convexity
