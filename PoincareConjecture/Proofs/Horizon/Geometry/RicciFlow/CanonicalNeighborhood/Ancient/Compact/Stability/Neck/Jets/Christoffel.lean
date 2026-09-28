import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Coefficients.InverseBounds
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Exponential.Jacobi.Coefficients
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Metric.Comparison.Jets.ComparisonCoordinateJets














noncomputable section

set_option autoImplicit false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

open Set
open scoped ContDiff Topology

namespace PoincareConjecture.CoordinateTransition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

private def christoffelOfCoefficientPair
    (p : (E →L[ℝ] E →L[ℝ] ℝ) × (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)) :
    E →L[ℝ] E →L[ℝ] E :=
  let flipL := (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).toLinearIsometry.toContinuousLinearMap
  (ContinuousLinearMap.compL ℝ E (E →L[ℝ] ℝ) E p.1.inverse).comp
    ((2⁻¹ : ℝ) • (p.2 + (flipL.comp p.2).flip - flipL.comp p.2.flip))

private theorem contDiffAt_christoffelOfCoefficientPair
    {p : (E →L[ℝ] E →L[ℝ] ℝ) × (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)}
    (hp : p.1.IsInvertible) :
    ContDiffAt ℝ ∞ christoffelOfCoefficientPair p := by
  have hi : ContDiffAt ℝ ∞
      (fun q : (E →L[ℝ] E →L[ℝ] ℝ) × (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) =>
        q.1.inverse) p := hp.contDiffAt_map_inverse.comp p contDiffAt_fst
  have hf : ContDiff ℝ ∞ (fun A : E →L[ℝ] E →L[ℝ] ℝ => A.flip) :=
    (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).contDiff
  have hf' : ContDiff ℝ ∞ (fun A : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ => A.flip) :=
    (ContinuousLinearMap.flipₗᵢ ℝ E E (E →L[ℝ] ℝ)).contDiff
  unfold christoffelOfCoefficientPair
  fun_prop



theorem exists_finite_christoffel_jet_bound_at
    {ι : Type*} {A : ι → E → E →L[ℝ] E →L[ℝ] ℝ} (x : ι → E)
    (hA : ∀ i, ContDiffAt ℝ ∞ (A i) (x i)) (m : ℕ)
    (hjets : ∃ C : ℝ, ∀ i j, j ≤ m + 1 →
      ‖iteratedFDeriv ℝ j (A i) (x i)‖ ≤ C)
    {a : ℝ} (ha : 0 < a)
    (hell : ∀ i v, a * ‖v‖ ^ 2 ≤ A i (x i) v v) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ i j, j ≤ m →
      ‖iteratedFDeriv ℝ j (CoordinateExponential.christoffelBilinear (A i)) (x i)‖ ≤ C := by
  obtain ⟨CA, hCA⟩ := hjets
  let B := max CA 1
  have hB : 1 ≤ B := le_max_right _ _
  let p := fun i y => (A i y, fderiv ℝ (A i) y)
  have hD (i : ι) : ContDiffAt ℝ ∞ (fderiv ℝ (A i)) (x i) :=
    (hA i).fderiv_right (m := ∞) (by simp)
  have hps (i : ι) : ContDiffAt ℝ ∞ (p i) (x i) := (hA i).prodMk (hD i)
  have hpj (i : ι) (j : ℕ) (hj : j ≤ m) :
      ‖iteratedFDeriv ℝ j (p i) (x i)‖ ≤ B := by
    dsimp only [p]
    erw [iteratedFDeriv_prodMk (hA i) (hD i) (by exact_mod_cast le_top),
      ContinuousMultilinearMap.opNorm_prod]
    apply max_le
    · exact (hCA i j (by omega)).trans (le_max_left _ _)
    · rw [norm_iteratedFDeriv_fderiv]
      exact (hCA i (j + 1) (by omega)).trans (le_max_left _ _)
  let H := (E →L[ℝ] E →L[ℝ] ℝ) × (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
  let K : Set H :=
    {Q : E →L[ℝ] E →L[ℝ] ℝ | ‖Q‖ ≤ B ∧ ∀ v, a * ‖v‖ ^ 2 ≤ Q v v} ×ˢ
      Metric.closedBall (0 : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) B
  let : ProperSpace (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
    FiniteDimensional.proper ℝ _
  have hK : IsCompact K := (isCompact_bounded_uniformlyElliptic (E := E) a B).prod
    (isCompact_closedBall _ _)
  obtain ⟨L, hL, hLj⟩ := MetricSurgery.exists_compact_local_jet_bound hK
    (fun q hq => contDiffAt_christoffelOfCoefficientPair
      (isInvertible_of_uniformEllipticity ha hq.1.2)) m
  have hpK (i : ι) : p i (x i) ∈ K := by
    refine ⟨⟨?_, hell i⟩, ?_⟩
    · simpa only [norm_iteratedFDeriv_zero] using
        (hCA i 0 (Nat.zero_le _)).trans (le_max_left CA 1)
    · simpa only [Metric.mem_closedBall, dist_zero_right, p, norm_iteratedFDeriv_one] using
        (hCA i 1 (by omega)).trans (le_max_left CA 1)
  refine ⟨max 1 (m.factorial * L * B ^ m), le_max_left _ _, ?_⟩
  intro i j hj
  have heq : CoordinateExponential.christoffelBilinear (A i) =
      christoffelOfCoefficientPair ∘ p i := rfl
  rw [heq]
  apply le_trans (MetricSurgery.norm_iteratedFDeriv_comp_uniform_at (hps i)
    (contDiffAt_christoffelOfCoefficientPair (isInvertible_of_uniformEllipticity ha (hell i)))
    j hB (fun l hl => hLj l (hl.trans hj) (p i (x i)) (hpK i))
    (fun l _ hl => hpj i l (hl.trans hj)))
  apply le_trans _ (le_max_right _ _)
  gcongr

end PoincareConjecture.CoordinateTransition
