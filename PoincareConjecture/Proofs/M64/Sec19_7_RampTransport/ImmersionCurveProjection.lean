import PoincareConjecture.Proofs.M64.Sec19_7_RampTransport.ImmersionConnectionBound
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.C1ChartPullback
import PoincareConjecture.Proofs.M63.Sec19_4_Approximation.GeodesicConnection
import Mathlib.Analysis.Calculus.Deriv.Mul






noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold Bundle

namespace PoincareConjecture

open Poincare.Geometry.Curvature.Hypersurface Proofs.M09

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {m n : ℕ} {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}
  {h : RiemannianMetric m (EuclideanSpace ℝ (Fin m))}





theorem m64_induced_curve_connection_decomposition
    (D : LeviCivitaData g) (Dh : LeviCivitaData h)
    {j : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
    {c W : ℝ → EuclideanSpace ℝ (Fin m)} {x : ℝ}
    (hj : ContDiffAt ℝ ∞ j (c x)) (hc : DifferentiableAt ℝ c x)
    (hW : DifferentiableAt ℝ W x) :
    deriv (fun y => fderiv ℝ j (c y) (W y)) x +
        D.connectionCoefficient (j (c x)) (deriv (j ∘ c) x)
          (fderiv ℝ j (c x) (W x)) =
      secondFundamentalForm D Dh j (c x) (deriv c x) (W x) +
        fderiv ℝ j (c x)
          (deriv W x + Dh.connectionCoefficient (c x) (deriv c x) (W x)) := by
  have hdj : DifferentiableAt ℝ (fderiv ℝ j) (c x) :=
    (hj.fderiv_right (show (∞ : ℕ∞ω) + 1 ≤ ∞ by simp)).differentiableAt (by simp)
  have hw := ((hdj.hasFDerivAt.comp_hasDerivAt x hc.hasDerivAt).clm_apply
    hW.hasDerivAt).deriv
  simp only [Function.comp_apply] at hw
  have hv := ((hj.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt x
    hc.hasDerivAt).deriv
  rw [hw, hv]
  simp only [secondFundamentalForm, covariantHessianMap, map_add]
  abel





theorem m64_induced_curve_connection_norm_le
    (D : LeviCivitaData g) (Dh : LeviCivitaData h)
    {j : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
    {c W : ℝ → EuclideanSpace ℝ (Fin m)} {x : ℝ}
    (hj : ContDiffAt ℝ ∞ j (c x)) (hc : DifferentiableAt ℝ c x)
    (hW : DifferentiableAt ℝ W x)
    (hmetric : ∀ᶠ y in 𝓝 (c x), ∀ a b, h.inner y a b =
      g.inner (j y) (fderiv ℝ j y a) (fderiv ℝ j y b)) :
    h.tangentNorm (c x)
        (deriv W x + Dh.connectionCoefficient (c x) (deriv c x) (W x)) ≤
      g.tangentNorm (j (c x))
        (deriv (fun y => fderiv ℝ j (c y) (W y)) x +
          D.connectionCoefficient (j (c x)) (deriv (j ∘ c) x)
            (fderiv ℝ j (c x) (W x))) := by
  let A := deriv W x + Dh.connectionCoefficient (c x) (deriv c x) (W x)
  let B := secondFundamentalForm D Dh j (c x) (deriv c x) (W x)
  let V := fderiv ℝ j (c x) A
  have horth : g.inner (j (c x)) B V = 0 :=
    secondFundamentalForm_normal D Dh hj hmetric (deriv c x) (W x) A
  have horth' : g.inner (j (c x)) V B = 0 := (g.symm _ V B).trans horth
  have hnonneg : 0 ≤ g.inner (j (c x)) B B := by
    by_cases hB : B = 0
    · simp only [hB, map_zero, le_refl]
    · exact (g.pos _ B hB).le
  rw [m64_induced_curve_connection_decomposition D Dh hj hc hW]
  change h.tangentNorm (c x) A ≤ g.tangentNorm (j (c x)) (B + V)
  unfold RiemannianMetric.tangentNorm
  apply Real.sqrt_le_sqrt
  simp only [map_add, add_apply, horth, horth', zero_add, add_zero]
  rw [hmetric.self_of_nhds]
  exact le_add_of_nonneg_left hnonneg

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]





theorem m64_pullback_chart_expression {g : RiemannianMetric n M}
    (D : LeviCivitaData g) (p : M) {c : ℝ → M} {x : ℝ}
    (hc : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n) c x)
    (hsource : c x ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source)
    {Y : (s : ℝ) → TangentSpace (𝓡 n) (c s)}
    {v : ℝ → EuclideanSpace ℝ (Fin n)} (hv : ContDiffAt ℝ 1 v x)
    (hfield : ∀ᶠ s in 𝓝 x, Y s = chartVectorField p (v s) (c s)) :
    rampHorizontalCovariantDerivative D c Y x =
      chartVectorField p
        (deriv v x + coordinateChristoffel
          (g.pullbackCoefficients (chartAt (EuclideanSpace ℝ (Fin n)) p).symm)
          ((chartAt (EuclideanSpace ℝ (Fin n)) p) (c x))
          (deriv ((chartAt (EuclideanSpace ℝ (Fin n)) p) ∘ c) x) (v x)) (c x) := by
  obtain ⟨V, hV, hvV⟩ := hv.contDiffOn le_rfl (by simp)
  obtain ⟨U, hUV, hU, hxU⟩ := mem_nhds_iff.mp hV
  have hvel : chartVectorField p
      (deriv ((chartAt (EuclideanSpace ℝ (Fin n)) p) ∘ c) x) (c x) =
      curveVelocity c x := by
    have hd := hasDerivAt_chart_curve p c x hsource hc
    exact chartVectorField_coordinate_velocity p c x _ hsource hc
      hd.differentiableAt.hasDerivAt
  have hconn := M63.chartVectorField_coordinateChristoffel D p
    ((chartAt (EuclideanSpace ℝ (Fin n)) p) (c x))
    ((chartAt (EuclideanSpace ℝ (Fin n)) p).map_source hsource)
    (deriv ((chartAt (EuclideanSpace ℝ (Fin n)) p) ∘ c) x) (v x)
  rw [(chartAt (EuclideanSpace ℝ (Fin n)) p).left_inv hsource, hvel] at hconn
  rw [M62.pullback_congr D hfield,
    M63.pullback_chart_field_of_contDiff_one D p hc hsource hU hxU v (hvV.mono hUV),
    ← hconn]
  simp only [chartVectorField, VectorField.mpullback, map_add]





theorem m64_model_pullback_expression
    (D : LeviCivitaData g) {c W : ℝ → EuclideanSpace ℝ (Fin n)} {x : ℝ}
    (hc : DifferentiableAt ℝ c x) (hW : ContDiffAt ℝ 1 W x) :
    rampHorizontalCovariantDerivative D c W x =
      deriv W x + D.connectionCoefficient (c x) (deriv c x) (W x) := by
  have hfield (v : EuclideanSpace ℝ (Fin n)) :
      chartVectorField 0 v = (fun _ : EuclideanSpace ℝ (Fin n) => v) := by
    simp only [chartVectorField, chartAt_self_eq]
    change VectorField.mpullback (𝓡 n) (𝓡 n) id (fun _ => v) = (fun _ => v)
    exact VectorField.mpullback_id
  have heq := m64_pullback_chart_expression D 0 hc.mdifferentiableAt (by simp) hW
    (Filter.Eventually.of_forall fun s => by rw [hfield])
  have hcoeff : g.pullbackCoefficients id = g.euclideanCoefficients := by
    ext q a b
    simp only [RiemannianMetric.pullbackCoefficients, mfderiv_id,
      RiemannianMetric.euclideanCoefficients]
    rfl
  simpa only [hfield, chartAt_self_eq, OpenPartialHomeomorph.refl_apply,
    OpenPartialHomeomorph.refl_symm, Function.id_comp, id_eq, hcoeff,
    D.connectionCoefficient_eq_coordinateChristoffel] using heq

end PoincareConjecture
