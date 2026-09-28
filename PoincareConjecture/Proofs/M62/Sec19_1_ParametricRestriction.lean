import PoincareConjecture.Proofs.M62.Sec19_1_PullbackRestriction
import PoincareConjecture.Definitions.M62Geometry
import PoincareConjecture.Proofs.M09.ParametricCurveDerivative

set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M62

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem hasDerivAt_fixedPointTimeDerivative
    (W : ℝ → (p : M) → TangentSpace (𝓡 n) p) (p : M) (x : ℝ)
    (hW : MDifferentiableAt ((𝓘(ℝ, ℝ)).prod (𝓡 n)) ((𝓡 n).prod (𝓡 n))
      (fun z : ℝ × M ↦ (⟨z.2, W z.1 z.2⟩ : TangentBundle (𝓡 n) M)) (x, p)) :
    HasDerivAt (fun r ↦ W r p) (fixedPointTimeDerivative W p x) x := by
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) p
  have hp : p ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' p
  let C : ℝ × M → EuclideanSpace ℝ (Fin n) := fun z ↦ (e ⟨z.2, W z.1 z.2⟩).2
  have hC : MDifferentiableAt ((𝓘(ℝ, ℝ)).prod (𝓡 n)) (𝓡 n) C (x, p) :=
    ((e.mdifferentiableAt_totalSpace_iff (𝓡 n) _ (e.mem_source.mpr hp)).mp hW).2
  have hc : DifferentiableAt ℝ (fun r ↦ C (r, p)) x :=
    (hC.comp x (mdifferentiableAt_id.prodMk mdifferentiableAt_const)).differentiableAt
  have hlin : HasDerivAt (fun r ↦ e.symmL ℝ p (C (r, p)))
      (e.symmL ℝ p (deriv (fun r ↦ C (r, p)) x)) x := by
    rw [hasDerivAt_iff_hasFDerivAt, hasFDerivAt_iff_isLittleOTVS]
    simpa only [Function.comp_def, map_sub, map_smul,
      ContinuousLinearMap.toSpanSingleton_apply] using
      (e.symmL ℝ p).isBigOTVS_comp.trans_isLittleOTVS hc.hasDerivAt.hasFDerivAt.isLittleOTVS
  have hrep : (fun r ↦ e.symmL ℝ p (C (r, p))) = (fun r ↦ W r p) := by
    funext r
    change e.symmL ℝ p (e ⟨p, W r p⟩).2 = W r p
    rw [← e.continuousLinearMapAt_apply_of_mem ℝ hp]
    exact e.symmL_continuousLinearMapAt hp _
  rw [hrep] at hlin
  exact hlin

theorem pullback_parametric_field {g : RiemannianMetric n M}
    (D : LeviCivitaData g) {γ : ℝ → M} {x : ℝ}
    (hγ : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) γ x)
    (W : ℝ → (p : M) → TangentSpace (𝓡 n) p)
    (hW : MDifferentiableAt ((𝓘(ℝ, ℝ)).prod (𝓡 n)) ((𝓡 n).prod (𝓡 n))
      (fun z : ℝ × M ↦ (⟨z.2, W z.1 z.2⟩ : TangentBundle (𝓡 n) M)) (x, γ x)) :
    rampHorizontalCovariantDerivative D γ (fun r ↦ W r (γ r)) x =
      fixedPointTimeDerivative W (γ x) x +
        D.connection (W x) (γ x) (curveVelocity γ x) := by
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) (γ x)
  have hp : γ x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' (γ x)
  let C : ℝ × M → EuclideanSpace ℝ (Fin n) := fun z ↦ (e ⟨z.2, W z.1 z.2⟩).2
  have hC : MDifferentiableAt ((𝓘(ℝ, ℝ)).prod (𝓡 n)) (𝓡 n) C (x, γ x) :=
    ((e.mdifferentiableAt_totalSpace_iff (𝓡 n) _ (e.mem_source.mpr hp)).mp hW).2
  have hsplit := PoincareConjecture.Proofs.M09.hasDerivAt_parametric_curve C γ x hC hγ
  have hCs : MDifferentiableAt (𝓡 n) (𝓡 n) (fun p ↦ C (x, p)) (γ x) :=
    hC.comp (γ x) (mdifferentiableAt_const.prodMk mdifferentiableAt_id)
  have hspatial : HasDerivAt (fun r ↦ C (x, γ r))
      (mvfderiv (𝓡 n) (fun p ↦ C (x, p)) (γ x) (curveVelocity γ x)) x :=
    (hCs.hasMFDerivAt.comp x hγ.hasMFDerivAt).hasFDerivAt.hasDerivAt
  have hWs : MDifferentiableAt (𝓡 n) ((𝓡 n).prod (𝓡 n))
      (fun p ↦ (⟨p, W x p⟩ : TangentBundle (𝓡 n) M)) (γ x) :=
    hW.comp (γ x) (mdifferentiableAt_const.prodMk mdifferentiableAt_id)
  rw [← pullback_ambient_field D hγ (W x) hWs]
  change e.symmL ℝ (γ x) (deriv (fun r ↦ C (r, γ r)) x) +
      D.connection (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (W x (γ x)))
        (γ x) (curveVelocity γ x) =
    e.symmL ℝ (γ x) (deriv (fun r ↦ C (r, γ x)) x) +
      (e.symmL ℝ (γ x) (deriv (fun r ↦ C (x, γ r)) x) +
        D.connection (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (W x (γ x)))
          (γ x) (curveVelocity γ x))
  rw [hsplit.deriv, hspatial.deriv, map_add, add_assoc]

end PoincareConjecture.M62
