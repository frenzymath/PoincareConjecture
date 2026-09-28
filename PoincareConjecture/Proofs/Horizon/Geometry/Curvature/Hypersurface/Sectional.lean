import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Hypersurface.Gauss
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Hypersurface.ShapeOperator

noncomputable section
set_option autoImplicit false
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency false

open PoincareConjecture Filter
open scoped ContDiff Topology Manifold Bundle InnerProductSpace

namespace Poincare.Geometry.Curvature.Hypersurface

private abbrev E (k : ℕ) := EuclideanSpace ℝ (Fin k)

theorem metric_inner_normals_eq_mul {m : ℕ}
    (g : RiemannianMetric (m + 1) (E (m + 1))) (p : E (m + 1))
    (L : E m →ₗ[ℝ] E (m + 1)) (hL : Function.Injective L)
    (N : E (m + 1)) (hN : g.inner p N N = 1)
    (hNT : ∀ a, g.inner p N (L a) = 0)
    (v w : E (m + 1)) (hw : ∀ a, g.inner p w (L a) = 0) :
    g.inner p v w = g.inner p v N * g.inner p w N := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 (m + 1)) : E (m + 1) → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : NormedAddCommGroup (TangentSpace (𝓡 (m + 1)) p) := inferInstance
  let : InnerProductSpace ℝ (TangentSpace (𝓡 (m + 1)) p) := inferInstance
  let : FiniteDimensional ℝ (TangentSpace (𝓡 (m + 1)) p) :=
    inferInstanceAs (FiniteDimensional ℝ (E (m + 1)))
  let T : Submodule ℝ (TangentSpace (𝓡 (m + 1)) p) := L.range
  have hdim : Module.finrank ℝ T + 1 =
      Module.finrank ℝ (TangentSpace (𝓡 (m + 1)) p) := by
    change Module.finrank ℝ L.range + 1 = Module.finrank ℝ (E (m + 1))
    rw [LinearMap.finrank_range_of_inj hL]
    simp [E]
  have hNT' : N ∈ Tᗮ := by
    apply (Submodule.mem_orthogonal' (E := TangentSpace (𝓡 (m + 1)) p) T N).2
    rintro _ ⟨a, rfl⟩
    exact hNT a
  have hw' : w ∈ Tᗮ := by
    apply (Submodule.mem_orthogonal' (E := TangentSpace (𝓡 (m + 1)) p) T w).2
    rintro _ ⟨a, rfl⟩
    exact hw a
  exact inner_normals_eq_mul T hdim N hN hNT' v w hw'

theorem fderiv_injective_of_pullback_metric {m n : ℕ}
    {g : RiemannianMetric n (E n)} {h : RiemannianMetric m (E m)}
    {F : E m → E n} {x : E m}
    (hmetric : ∀ a b, h.inner x a b =
      g.inner (F x) (fderiv ℝ F x a) (fderiv ℝ F x b)) :
    Function.Injective (fderiv ℝ F x) := by
  intro a b hab
  have hz : fderiv ℝ F x (a - b) = 0 := by rw [map_sub, hab, sub_self]
  have hab' : a - b = 0 := by
    by_contra hne
    have hp := h.pos x (a - b) hne
    rw [hmetric, hz] at hp
    simp at hp
  exact sub_eq_zero.mp hab'

theorem gauss_sectionalCurvature_of_eventually {m : ℕ}
    {g : RiemannianMetric (m + 1) (E (m + 1))} {h : RiemannianMetric m (E m)}
    (D : LeviCivitaData g) (D' : LeviCivitaData h)
    {F : E m → E (m + 1)} {x : E m} (hF : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ ∞ F y)
    (hmetric : ∀ᶠ y in 𝓝 x, ∀ a b, h.inner y a b =
      g.inner (F y) (fderiv ℝ F y a) (fderiv ℝ F y b))
    (N : E (m + 1)) (hN : g.inner (F x) N N = 1)
    (hNT : ∀ a, g.inner (F x) N (fderiv ℝ F x a) = 0)
    (u v : E m) (hu : h.inner x u u = 1) (hv : h.inner x v v = 1)
    (huv : h.inner x u v = 0) :
    D'.sectionalCurvature x u v =
      D.sectionalCurvature (F x) (fderiv ℝ F x u) (fderiv ℝ F x v) +
      h.inner x (shapeOperator D D' F x N u) u *
        h.inner x (shapeOperator D D' F x N v) v -
      h.inner x (shapeOperator D D' F x N u) v ^ 2 := by
  have hL := fderiv_injective_of_pullback_metric hmetric.self_of_nhds
  have hpair (a b c d : E m) :
      g.inner (F x) (secondFundamentalForm D D' F x a b)
        (secondFundamentalForm D D' F x c d) =
      h.inner x (shapeOperator D D' F x N a) b *
        h.inner x (shapeOperator D D' F x N c) d := by
    rw [metric_inner_normals_eq_mul g (F x) (fderiv ℝ F x).toLinearMap hL N hN hNT
      _ _ (secondFundamentalForm_normal D D' hF.self_of_nhds hmetric c d)]
    rw [g.symm (F x) (secondFundamentalForm D D' F x a b),
      g.symm (F x) (secondFundamentalForm D D' F x c d),
      inner_shapeOperator, inner_shapeOperator]
  have hGauss := gauss_curvatureTensor_of_eventually D D' hF hmetric u v u v
  rw [hpair, secondFundamentalForm_symm D D' hF.self_of_nhds v u, hpair] at hGauss
  simpa only [LeviCivitaData.sectionalCurvature, ← hmetric.self_of_nhds,
    hu, hv, huv, zero_pow (by decide : 2 ≠ 0), mul_one, sub_zero, div_one, pow_two]
    using hGauss

theorem gauss_sectionalCurvature {m : ℕ}
    {g : RiemannianMetric (m + 1) (E (m + 1))} {h : RiemannianMetric m (E m)}
    (D : LeviCivitaData g) (D' : LeviCivitaData h)
    {F : E m → E (m + 1)} {x : E m} (hF : ContDiff ℝ ∞ F)
    (hmetric : ∀ᶠ y in 𝓝 x, ∀ a b, h.inner y a b =
      g.inner (F y) (fderiv ℝ F y a) (fderiv ℝ F y b))
    (N : E (m + 1)) (hN : g.inner (F x) N N = 1)
    (hNT : ∀ a, g.inner (F x) N (fderiv ℝ F x a) = 0)
    (u v : E m) (hu : h.inner x u u = 1) (hv : h.inner x v v = 1)
    (huv : h.inner x u v = 0) :
    D'.sectionalCurvature x u v =
      D.sectionalCurvature (F x) (fderiv ℝ F x u) (fderiv ℝ F x v) +
      h.inner x (shapeOperator D D' F x N u) u *
        h.inner x (shapeOperator D D' F x N v) v -
      h.inner x (shapeOperator D D' F x N u) v ^ 2 :=
  gauss_sectionalCurvature_of_eventually D D'
    (Filter.Eventually.of_forall fun _ => hF.contDiffAt) hmetric N hN hNT u v hu hv huv

theorem metric_symmetric_operator_extrinsic_determinant_lower_bound {m : ℕ}
    (h : RiemannianMetric (m + 1) (E (m + 1))) (x : E (m + 1))
    (A : E (m + 1) →ₗ[ℝ] E (m + 1))
    (hA : ∀ u v, h.inner x (A u) v = h.inner x u (A v)) (β : ℝ)
    (hupper : ∀ κ, Module.End.HasEigenvalue A κ → κ ≤ β) (hβ : 0 ≤ β)
    (u v : E (m + 1)) (hu : h.inner x u u = 1) (hv : h.inner x v v = 1)
    (huv : h.inner x u v = 0) :
    -(negativePart (A.trace ℝ (E (m + 1))) + (m : ℝ) * β) * β ≤
      h.inner x (A u) u * h.inner x (A v) v - h.inner x (A u) v ^ 2 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 (m + 1)) : E (m + 1) → Type _) :=
    ⟨h.toRiemannianMetric⟩
  let : NormedAddCommGroup (TangentSpace (𝓡 (m + 1)) x) := inferInstance
  let : InnerProductSpace ℝ (TangentSpace (𝓡 (m + 1)) x) := inferInstance
  let : FiniteDimensional ℝ (TangentSpace (𝓡 (m + 1)) x) :=
    inferInstanceAs (FiniteDimensional ℝ (E (m + 1)))
  let A' : TangentSpace (𝓡 (m + 1)) x →ₗ[ℝ] TangentSpace (𝓡 (m + 1)) x := A
  have hA' : A'.IsSymmetric := hA
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 (m + 1)) x) = m + 1 := by
    change Module.finrank ℝ (E (m + 1)) = m + 1
    simp [E]
  exact symmetric_operator_extrinsic_determinant_lower_bound hdim A' hA' β
    (fun i => hupper _ (hA'.hasEigenvalue_eigenvalues hdim i)) hβ u v hu hv huv

theorem sectionalCurvature_lower_bound_of_eventually {m : ℕ}
    {g : RiemannianMetric (m + 2) (E (m + 2))}
    {h : RiemannianMetric (m + 1) (E (m + 1))}
    (D : LeviCivitaData g) (D' : LeviCivitaData h)
    {F : E (m + 1) → E (m + 2)} {x : E (m + 1)}
    (hF : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ ∞ F y)
    (hmetric : ∀ᶠ y in 𝓝 x, ∀ a b, h.inner y a b =
      g.inner (F y) (fderiv ℝ F y a) (fderiv ℝ F y b))
    (N : E (m + 2)) (hN : g.inner (F x) N N = 1)
    (hNT : ∀ a, g.inner (F x) N (fderiv ℝ F x a) = 0)
    (K β : ℝ) (hβ : 0 ≤ β)
    (hambient : ∀ a b, g.inner (F x) a a = 1 → g.inner (F x) b b = 1 →
      g.inner (F x) a b = 0 → -K ≤ D.sectionalCurvature (F x) a b)
    (hupper : ∀ κ, Module.End.HasEigenvalue (shapeOperator D D' F x N) κ → κ ≤ β)
    (u v : E (m + 1)) (hu : h.inner x u u = 1) (hv : h.inner x v v = 1)
    (huv : h.inner x u v = 0) :
    -K - (negativePart ((shapeOperator D D' F x N).trace ℝ (E (m + 1))) +
      ((m + 1 : ℕ) : ℝ) * β) * β ≤ D'.sectionalCurvature x u v := by
  have hdet := metric_symmetric_operator_extrinsic_determinant_lower_bound h x
    (shapeOperator D D' F x N) (shapeOperator_selfAdjoint D D' hF.self_of_nhds N)
    β hupper hβ u v hu hv huv
  have hcurv := hambient (fderiv ℝ F x u) (fderiv ℝ F x v)
    ((hmetric.self_of_nhds u u).symm.trans hu)
    ((hmetric.self_of_nhds v v).symm.trans hv)
    ((hmetric.self_of_nhds u v).symm.trans huv)
  rw [gauss_sectionalCurvature_of_eventually D D' hF hmetric N hN hNT u v hu hv huv]
  push_cast
  nlinarith [sq_nonneg β]

theorem sectionalCurvature_lower_bound {m : ℕ}
    {g : RiemannianMetric (m + 2) (E (m + 2))}
    {h : RiemannianMetric (m + 1) (E (m + 1))}
    (D : LeviCivitaData g) (D' : LeviCivitaData h)
    {F : E (m + 1) → E (m + 2)} {x : E (m + 1)} (hF : ContDiff ℝ ∞ F)
    (hmetric : ∀ᶠ y in 𝓝 x, ∀ a b, h.inner y a b =
      g.inner (F y) (fderiv ℝ F y a) (fderiv ℝ F y b))
    (N : E (m + 2)) (hN : g.inner (F x) N N = 1)
    (hNT : ∀ a, g.inner (F x) N (fderiv ℝ F x a) = 0)
    (K β : ℝ) (hβ : 0 ≤ β)
    (hambient : ∀ a b, g.inner (F x) a a = 1 → g.inner (F x) b b = 1 →
      g.inner (F x) a b = 0 → -K ≤ D.sectionalCurvature (F x) a b)
    (hupper : ∀ κ, Module.End.HasEigenvalue (shapeOperator D D' F x N) κ → κ ≤ β)
    (u v : E (m + 1)) (hu : h.inner x u u = 1) (hv : h.inner x v v = 1)
    (huv : h.inner x u v = 0) :
    -K - (negativePart ((shapeOperator D D' F x N).trace ℝ (E (m + 1))) +
      ((m + 1 : ℕ) : ℝ) * β) * β ≤ D'.sectionalCurvature x u v :=
  sectionalCurvature_lower_bound_of_eventually D D'
    (Filter.Eventually.of_forall fun _ => hF.contDiffAt) hmetric N hN hNT K β hβ
    hambient hupper u v hu hv huv

end Poincare.Geometry.Curvature.Hypersurface
