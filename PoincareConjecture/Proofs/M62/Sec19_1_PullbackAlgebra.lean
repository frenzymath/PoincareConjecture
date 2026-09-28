import PoincareConjecture.Proofs.M62.Sec19_1_PullbackConnection
import Mathlib.Analysis.Calculus.Deriv.Mul










set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology
open Filter

universe u

namespace PoincareConjecture.M62

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



theorem pullback_congr {g : RiemannianMetric n M}
    (D : LeviCivitaData g) {γ : ℝ → M}
    {Y Z : (r : ℝ) → TangentSpace (𝓡 n) (γ r)} {x : ℝ}
    (h : ∀ᶠ r in 𝓝 x, Y r = Z r) :
    rampHorizontalCovariantDerivative D γ Y x =
      rampHorizontalCovariantDerivative D γ Z x := by
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) (γ x)
  have hx : Y x = Z x := h.self_of_nhds
  have heq : (fun r ↦ (e ⟨γ r, Y r⟩).2) =ᶠ[𝓝 x]
      (fun r ↦ (e ⟨γ r, Z r⟩).2) := by
    filter_upwards [h] with r hr
    rw [hr]
  change e.symmL ℝ (γ x) (deriv (fun r ↦ (e ⟨γ r, Y r⟩).2) x) +
      D.connection (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (Y x))
        (γ x) (curveVelocity γ x) = _
  rw [heq.deriv_eq, hx]
  rfl



theorem pullback_smul {g : RiemannianMetric n M}
    (D : LeviCivitaData g) {γ : ℝ → M}
    {Y : (r : ℝ) → TangentSpace (𝓡 n) (γ r)} {f : ℝ → ℝ}
    {x f' : ℝ} (hf : HasDerivAt f f' x)
    (hY : MDifferentiableAt (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n))
      (fun r ↦ (⟨γ r, Y r⟩ : TangentBundle (𝓡 n) M)) x) :
    rampHorizontalCovariantDerivative D γ (fun r ↦ f r • Y r) x =
      f' • Y x + f x • rampHorizontalCovariantDerivative D γ Y x := by
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) (γ x)
  have hp : γ x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' (γ x)
  let y : ℝ → EuclideanSpace ℝ (Fin n) := fun r ↦ (e ⟨γ r, Y r⟩).2
  rw [mdifferentiableAt_totalSpace] at hY
  have hy : DifferentiableAt ℝ y x := hY.2.differentiableAt
  have hnear : ∀ᶠ r in 𝓝 x, γ r ∈ e.baseSet :=
    hY.1.continuousAt (e.open_baseSet.mem_nhds hp)
  have heq : (fun r ↦ (e ⟨γ r, f r • Y r⟩).2) =ᶠ[𝓝 x]
      (fun r ↦ f r • y r) := by
    filter_upwards [hnear] with r hr
    change (e ⟨γ r, f r • Y r⟩).2 = f r • (e ⟨γ r, Y r⟩).2
    rw [← e.continuousLinearMapAt_apply_of_mem ℝ hr,
      ← e.continuousLinearMapAt_apply_of_mem ℝ hr, map_smul]
  have hd : deriv (fun r ↦ (e ⟨γ r, f r • Y r⟩).2) x =
      f' • y x + f x • deriv y x := by
    rw [heq.deriv_eq, deriv_fun_smul hf.differentiableAt hy, hf.deriv, add_comm]
  have hrep : e.symmL ℝ (γ x) (y x) = Y x := by
    change e.symmL ℝ (γ x) (e ⟨γ x, Y x⟩).2 = Y x
    rw [← e.continuousLinearMapAt_apply_of_mem ℝ hp]
    exact e.symmL_continuousLinearMapAt hp _
  let A := PoincareConjecture.Proofs.M09.frozenConnectionEndomorphism D (γ x) (curveVelocity γ x)
  change e.symmL ℝ (γ x) (deriv (fun r ↦ (e ⟨γ r, f r • Y r⟩).2) x) +
      A (f x • Y x) =
    f' • Y x + f x • (e.symmL ℝ (γ x) (deriv y x) + A (Y x))
  rw [hd, map_add, map_smul, map_smul, map_smul, hrep, smul_add, add_assoc]

end PoincareConjecture.M62
