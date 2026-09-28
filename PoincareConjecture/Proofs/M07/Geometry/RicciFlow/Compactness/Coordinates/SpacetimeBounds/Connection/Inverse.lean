import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.AffineComposition
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Coefficients.InverseBounds

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 800000

open Set Filter
open scoped ContDiff Topology BigOperators

namespace PoincareConjecture.SpacetimeBounds

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_uniform_inverse_metric_jet_bound
    (q : ℕ) {a : ℝ} (ha : 0 < a) (b D : ℝ) (hD : 1 ≤ D) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (B : E → E →L[ℝ] E →L[ℝ] ℝ) (x : E), ContDiffAt ℝ ∞ B x →
        ‖B x‖ ≤ b → (∀ v, a * ‖v‖ ^ 2 ≤ B x v v) →
        (∀ j, 1 ≤ j → j ≤ q → ‖iteratedFDeriv ℝ j B x‖ ≤ D ^ j) →
        ∀ j ≤ q, ‖iteratedFDeriv ℝ j (fun y => (B y).inverse) x‖ ≤ C := by
  classical
  choose A hA using fun j : Fin (q + 1) =>
    CoordinateTransition.hasUniformJetBoundsOn_inverse_elliptic (E := E) ha b q
      j.val (by omega)
  let K : ℝ := ∑ j : Fin (q + 1), max (A j) 0
  have hK : 0 ≤ K := Finset.sum_nonneg (fun j _ => le_max_right (A j) 0)
  let C : ℝ := ∑ j : Fin (q + 1), j.val.factorial * K * D ^ j.val
  have hC : 0 ≤ C := Finset.sum_nonneg (fun j _ => by positivity)
  refine ⟨C, hC, ?_⟩
  intro B x hB hnorm hell hjets j hj
  have houter : ∀ l ≤ j,
      ‖iteratedFDeriv ℝ l (ContinuousLinearMap.inverse :
        (E →L[ℝ] E →L[ℝ] ℝ) → ((E →L[ℝ] ℝ) →L[ℝ] E)) (B x)‖ ≤ K := by
    intro l hl
    let i : Fin (q + 1) := ⟨l, by omega⟩
    exact (hA i () (B x) ⟨hnorm, hell⟩).trans ((le_max_left _ _).trans
      (Finset.single_le_sum (fun i _ => le_max_right (A i) 0) (Finset.mem_univ i)))
  have h := Poincare.Analysis.Calculus.norm_iteratedFDeriv_comp_le_of_contDiffAt hB
    (CoordinateTransition.isInvertible_of_uniformEllipticity ha hell).contDiffAt_map_inverse j
    houter (fun l hl hlj => hjets l hl (hlj.trans hj))
  apply h.trans
  exact Finset.single_le_sum (f := fun i : Fin (q + 1) => (i.val.factorial : ℝ) * K * D ^ i.val)
    (fun i _ => by positivity)
    (Finset.mem_univ (⟨j, by omega⟩ : Fin (q + 1)))

theorem exists_affine_inverse_metric_jet_bound
    (q : ℕ) {a : ℝ} (ha : 0 < a) (b D : ℝ) (hD : 1 ≤ D) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (B : E → E →L[ℝ] E →L[ℝ] ℝ) (x : E), ContDiffAt ℝ ∞ B x →
        ‖B x‖ ≤ b → (∀ v, a * ‖v‖ ^ 2 ≤ B x v v) →
        (∀ j, 1 ≤ j → j ≤ q → ‖iteratedFDeriv ℝ j B x‖ ≤ D ^ j) →
        ‖iteratedFDeriv ℝ (q + 1) (fun y => (B y).inverse) x‖ ≤
          C * (1 + ‖iteratedFDeriv ℝ (q + 1) B x‖) := by
  classical
  choose A hA using fun j : Fin (q + 2) =>
    CoordinateTransition.hasUniformJetBoundsOn_inverse_elliptic (E := E) ha b (q + 1)
      j.val (by omega)
  let K : ℝ := ∑ j : Fin (q + 2), max (A j) 0
  have hK : 0 ≤ K := Finset.sum_nonneg (fun j _ => le_max_right (A j) 0)
  have hD0 : 0 ≤ D := le_trans zero_le_one hD
  let Q : ℝ := ∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ) * (i.factorial * K * D ^ i)
  have hQ : 0 ≤ Q := Finset.sum_nonneg (fun i _ => by positivity)
  refine ⟨Q * D ^ (q + 1), by positivity, ?_⟩
  intro B x hB hnorm hell hjets
  have houter : ∀ j ≤ q + 1,
      ‖iteratedFDeriv ℝ j (ContinuousLinearMap.inverse :
        (E →L[ℝ] E →L[ℝ] ℝ) → ((E →L[ℝ] ℝ) →L[ℝ] E)) (B x)‖ ≤ K := by
    intro j hj
    let k : Fin (q + 2) := ⟨j, by omega⟩
    exact (hA k () (B x) ⟨hnorm, hell⟩).trans ((le_max_left _ _).trans
      (Finset.single_le_sum (fun i _ => le_max_right (A i) 0) (Finset.mem_univ k)))
  have h := norm_iteratedFDeriv_comp_le_affine_highest hB
    (CoordinateTransition.isInvertible_of_uniformEllipticity ha hell).contDiffAt_map_inverse
    q hK hD houter hjets
  change ‖iteratedFDeriv ℝ (q + 1) (fun y => (B y).inverse) x‖ ≤
    Q * (‖iteratedFDeriv ℝ (q + 1) B x‖ + D ^ (q + 1)) at h
  apply h.trans
  have hp : 1 ≤ D ^ (q + 1) := one_le_pow₀ hD
  have htop := norm_nonneg (iteratedFDeriv ℝ (q + 1) B x)
  calc
    _ ≤ Q * (D ^ (q + 1) * (1 + ‖iteratedFDeriv ℝ (q + 1) B x‖)) :=
      mul_le_mul_of_nonneg_left (by nlinarith) hQ
    _ = _ := by ring

end PoincareConjecture.SpacetimeBounds
