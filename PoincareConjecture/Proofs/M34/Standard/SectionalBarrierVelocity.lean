import PoincareConjecture.Proofs.M34.Standard.VariableSectionalDiffusion
import PoincareConjecture.Proofs.M04.SectionalNullReaction










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M34

open M04

section General

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}



noncomputable def sectionalRayleighVelocity (D : LeviCivitaData g) (x : M)
    (u v : TangentSpace (𝓡 n) x) : ℝ :=
  (D.tensorLaplacian D.riemannEvaluation x ![u, v, u, v] +
      D.curvatureReaction x u v u v) / metricGram g x u v -
    D.curvatureTensor x u v u v *
      (-2 * D.ricci x u u * g.inner x v v - 2 * g.inner x u u * D.ricci x v v +
        4 * D.ricci x u v * g.inner x u v) / (metricGram g x u v) ^ 2



theorem hasDerivWithinAt_sectionalRayleighVelocity {J : Set ℝ}
    (F : RicciFlow n M J) (t : ℝ) (ht : t ∈ J) (x : M)
    (u v : TangentSpace (𝓡 n) x) (hgram : 0 < metricGram (F.metric t) x u v) :
    HasDerivWithinAt (fun s => (F.connection s).curvatureTensor x u v u v /
      metricGram (F.metric s) x u v)
      (sectionalRayleighVelocity (F.connection t) x u v) J t :=
  hasDerivWithinAt_sectionalRayleigh F t ht x u v hgram

end General

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}




theorem sectionalRayleighVelocity_ge_barrier
    (D : LeviCivitaData g) {h : M → ℝ} (hh : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ h)
    {U : Set M} (hU : IsOpen U) {x : M} (hx : x ∈ U)
    (hmin : ∀ y ∈ U, ∀ a b : TangentSpace (𝓡 3) y,
      h y * metricGram g y a b ≤ D.curvatureTensor y a b a b)
    (u v : TangentSpace (𝓡 3) x) (hgram : 0 < metricGram g x u v)
    (hnull : D.curvatureTensor x u v u v = h x * metricGram g x u v) :
    D.laplacian h x + h x * (D.scalarCurvature x - 2 * h x) ≤
      sectionalRayleighVelocity D x u v := by
  have hdiff := curvature_tensorLaplacian_ge_variable_sectional_barrier D hh hU hx
    hmin u v hnull
  have hreact := curvatureReaction_lower_bound_of_shiftedSectional_null D x (-h x)
    (fun a b => by
      have hlow := hmin x hx a b
      change 0 ≤ D.curvatureTensor x a b a b + (-h x) * metricGram g x a b
      linarith) u v (by
        change D.curvatureTensor x u v u v + (-h x) * metricGram g x u v = 0
        rw [hnull]
        ring)
  let V := -2 * D.ricci x u u * g.inner x v v - 2 * g.inner x u u * D.ricci x v v +
    4 * D.ricci x u v * g.inner x u v
  have hr : h x * (D.scalarCurvature x - 2 * h x) * metricGram g x u v ≤
      D.curvatureReaction x u v u v - h x * V := by
    simpa only [neg_neg, mul_neg, neg_mul, ← sub_eq_add_neg, metricGram, V] using hreact
  have hnum : (D.laplacian h x + h x * (D.scalarCurvature x - 2 * h x)) *
      metricGram g x u v ≤ D.tensorLaplacian D.riemannEvaluation x ![u, v, u, v] +
        D.curvatureReaction x u v u v - h x * V := by
    nlinarith only [hdiff, hr]
  calc
    _ ≤ (D.tensorLaplacian D.riemannEvaluation x ![u, v, u, v] +
        D.curvatureReaction x u v u v - h x * V) / metricGram g x u v :=
      (le_div_iff₀ hgram).mpr hnum
    _ = _ := by
      unfold sectionalRayleighVelocity
      rw [hnull]
      dsimp only [V]
      field_simp

end PoincareConjecture.M34
