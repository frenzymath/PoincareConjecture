import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Convexity.NormalizedFlow
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Hypersurface.Connection
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Exponential.Gauss.Variation

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

open PoincareConjecture Filter Set
open Poincare.Geometry.Curvature.Hypersurface
open scoped ContDiff Topology Manifold Bundle

namespace Poincare.Geometry.Riemannian.Convexity

variable {n : ℕ} {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}

theorem differentiableAt_normalizedNegGradient (D : LeviCivitaData g)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hf : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f x)
    (hregular : g.inner x (D.gradient f x) (D.gradient f x) ≠ 0) :
    DifferentiableAt ℝ (normalizedNegGradient D f) x := by
  have hs := (contMDiffAt_normalizedNegGradient D hf hregular).mdifferentiableAt
    (by simp)
  rw [mdifferentiableAt_totalSpace] at hs
  exact mdifferentiableAt_iff_differentiableAt.mp (by simpa using hs.2)

theorem hasDerivAt_flow_squared_length
    (D : LeviCivitaData g)
    {q : ℝ × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {X : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {t : ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hq : ContDiffAt ℝ ∞ q (t, x))
    (hX : DifferentiableAt ℝ X (q (t, x)))
    (htime : ∀ᶠ y in 𝓝 x, HasDerivAt (fun s => q (s, y)) (X (q (t, y))) t)
    (v : EuclideanSpace ℝ (Fin n)) :
    let w := fderiv ℝ (fun y => q (t, y)) x v
    HasDerivAt (fun s => g.inner (q (s, x))
      (fderiv ℝ (fun y => q (s, y)) x v)
      (fderiv ℝ (fun y => q (s, y)) x v))
      (2 * g.inner (q (t, x)) (D.connection X (q (t, x)) w) w) t := by
  dsimp only
  let w := fderiv ℝ (fun y => q (t, y)) x v
  have hqx : DifferentiableAt ℝ (fun y => q (t, y)) x :=
    (hq.differentiableAt (by simp)).comp x
      ((differentiableAt_const t).prodMk differentiableAt_id)
  have hcomp := (hX.hasFDerivAt.comp x hqx.hasFDerivAt).fderiv
  simp only [Function.comp_def] at hcomp
  have hv := CoordinateExponential.hasDerivAt_variation hq htime v
  rw [hcomp] at hv
  have hB := (g.contDiffAt_euclideanCoefficients (q (t, x))).differentiableAt
    (by simp : (∞ : WithTop ℕ∞) ≠ 0)
  have hBq := hB.hasFDerivAt.comp_hasDerivAt t htime.self_of_nhds
  have hm := (hBq.clm_apply hv).clm_apply hv
  apply hm.congr_deriv
  simp only [add_apply, ContinuousLinearMap.comp_apply, Function.comp_apply]
  change fderiv ℝ g.euclideanCoefficients (q (t, x)) (X (q (t, x))) w w +
    g.inner (q (t, x)) (fderiv ℝ X (q (t, x)) w) w +
      g.inner (q (t, x)) w (fderiv ℝ X (q (t, x)) w) =
        2 * g.inner (q (t, x)) (D.connection X (q (t, x)) w) w
  rw [D.connectionCoefficient_metricCompatible]
  rw [D.connection_eq_fderiv_add hX]
  have hs := connectionCoefficient_symm D (q (t, x)) (X (q (t, x))) w
  change D.connection (fun _ => w) (q (t, x)) (X (q (t, x))) =
    D.euclideanConnection w (X (q (t, x))) (q (t, x)) at hs
  rw [hs]
  simp only [map_add, add_apply]
  rw [g.symm (q (t, x)) w (fderiv ℝ X (q (t, x)) w),
    g.symm (q (t, x)) w (D.euclideanConnection w (X (q (t, x))) (q (t, x)))]
  ring

theorem normalized_flow_squared_length_le
    (D : LeviCivitaData g)
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {q : ℝ × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {a b η B : ℝ} {x : EuclideanSpace ℝ (Fin n)} (hη : 0 ≤ η)
    (hq : ∀ t ∈ Icc a b, ContDiffAt ℝ ∞ q (t, x))
    (hf : ∀ᶠ y in 𝓝 x, ∀ t ∈ Icc a b,
      ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f (q (t, y)))
    (hregular : ∀ᶠ y in 𝓝 x, ∀ t ∈ Icc a b,
      0 < g.inner (q (t, y)) (D.gradient f (q (t, y))) (D.gradient f (q (t, y))))
    (hupper : ∀ t ∈ Icc a b,
      g.inner (q (t, x)) (D.gradient f (q (t, x))) (D.gradient f (q (t, x))) ≤ B)
    (htime : ∀ᶠ y in 𝓝 x, ∀ t ∈ Icc a b,
      HasDerivAt (fun s => q (s, y)) (normalizedNegGradient D f (q (t, y))) t)
    (v : EuclideanSpace ℝ (Fin n))
    (hinitial : mvfderiv (𝓡 n) f (q (a, x))
      (fderiv ℝ (fun y => q (a, y)) x v) = 0)
    (hhess : ∀ t ∈ Icc a b,
      let w := fderiv ℝ (fun y => q (t, y)) x v
      η * g.inner (q (t, x)) w w ≤ D.hessian f (q (t, x)) w w) :
    ∀ t ∈ Icc a b,
      g.inner (q (t, x)) (fderiv ℝ (fun y => q (t, y)) x v)
        (fderiv ℝ (fun y => q (t, y)) x v) ≤
      g.inner (q (a, x)) (fderiv ℝ (fun y => q (a, y)) x v)
        (fderiv ℝ (fun y => q (a, y)) x v) * Real.exp (-2 * (η / B) * (t - a)) := by
  have htangent (t : ℝ) (ht : t ∈ Icc a b) :
      mvfderiv (𝓡 n) f (q (t, x)) (fderiv ℝ (fun y => q (t, y)) x v) = 0 := by
    rw [normalized_flow_preserves_level_differential D hq hf
      (hregular.mono (fun _ hy s hs => (hy s hs).ne')) htime v t ht]
    exact hinitial
  have hf := hf.self_of_nhds
  have hregular := hregular.self_of_nhds
  have htime (t : ℝ) (ht : t ∈ Icc a b) := htime.mono (fun _ hy => hy t ht)
  let w : ℝ → EuclideanSpace ℝ (Fin n) := fun t => fderiv ℝ (fun y => q (t, y)) x v
  let l : ℝ → ℝ := fun t => g.inner (q (t, x)) (w t) (w t)
  let l' : ℝ → ℝ := fun t => 2 * g.inner (q (t, x))
    (D.connection (normalizedNegGradient D f) (q (t, x)) (w t)) (w t)
  have hd (t : ℝ) (ht : t ∈ Icc a b) : HasDerivAt l (l' t) t :=
    hasDerivAt_flow_squared_length D (hq t ht)
      (differentiableAt_normalizedNegGradient D (hf t ht) (hregular t ht).ne')
      (htime t ht) v
  apply squared_length_le_exp_of_derivative_bound
    (q := l) (q' := l') (c := η / B)
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => hd t ⟨ht.1, ht.2.le⟩)
  intro t ht
  have hc := inner_connection_normalized_neg_gradient_le D
    (hf t ⟨ht.1, ht.2.le⟩) (hregular t ⟨ht.1, ht.2.le⟩) hη
    (hupper t ⟨ht.1, ht.2.le⟩) (w t)
    (htangent t ⟨ht.1, ht.2.le⟩) (hhess t ⟨ht.1, ht.2.le⟩)
  dsimp only [l, l']
  change 2 * g.inner (q (t, x)) (D.connection
    (fun y => -(g.inner y (D.gradient f y) (D.gradient f y))⁻¹ • D.gradient f y)
    (q (t, x)) (w t)) (w t) ≤ _
  linarith

end Poincare.Geometry.Riemannian.Convexity
