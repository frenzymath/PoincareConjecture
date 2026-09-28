import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma16_8_CovariantComponentBounds
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma16_8_CurvatureCoordinateJets
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma11_2_UniformCoordinateJets
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Metric.LocalExtension
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.JetBounds.CurvatureNaturality










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology BigOperators

namespace PoincareConjecture.M44

local notation "E" => EuclideanSpace ℝ (Fin 3)

noncomputable local instance initialCoefficientNormedGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance initialCoefficientNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace




theorem exists_uniform_curvature_derivative_bound (m : ℕ) {a : ℝ}
    (ha : 0 < a) (Z : ℝ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (g : RiemannianMetric 3 E) (D : LeviCivitaData g) (x : E),
      (∀ v : E, a * ‖v‖ ^ 2 ≤ g.inner x v v) →
      (∀ j ≤ m + 2, ‖iteratedFDeriv ℝ j g.euclideanCoefficients x‖ ≤ Z) →
      ∀ j ≤ m, D.curvatureDerivativeNorm j x ≤ C := by
  classical
  obtain ⟨G, hG, hchrist⟩ := exists_uniform_comparisonChristoffel_bound m ha Z
  obtain ⟨R, hR, hcurv⟩ := exists_curvature_component_jet_bound m ha Z
  choose C hC hbound using fun i : Fin (m + 1) =>
    exists_uniform_covariant_norm_bound 4 i.val ha hG
  let B := 1 + ∑ i : Fin (m + 1), C i * R
  have hsum : 0 ≤ ∑ i : Fin (m + 1), C i * R :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hC i).le hR)
  refine ⟨B, by dsimp [B]; linarith only [hsum], ?_⟩
  intro g D x hell hjets j hj
  let i : Fin (m + 1) := ⟨j, Nat.lt_succ_of_le hj⟩
  have h := hbound i g D D.riemannEvaluation D.riemannEvaluation_isSmooth_model
    x R hR hell
    (fun l hl b c d => hchrist g x hell (fun q hq => hjets q (by omega))
      l (hl.trans hj) b c d)
    (fun l hl b => hcurv g D x hell hjets l (hl.trans hj) b)
  change D.curvatureDerivativeNorm j x ≤ C i * R at h
  exact h.trans ((Finset.single_le_sum
    (fun k _ => mul_nonneg (hC k).le hR) (Finset.mem_univ i)).trans
      (le_add_of_nonneg_left zero_le_one))




theorem exists_uniform_pullback_curvature_bound (m : ℕ) {a : ℝ}
    (ha : 0 < a) (Z : ℝ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {M : Type*} [TopologicalSpace M]
      [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M],
      ∀ (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
        {f : E → M} {U : Set E}, IsOpen U →
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U →
      (∀ y ∈ U, (mfderiv (𝓡 3) (𝓡 3) f y).IsInvertible) →
      ∀ x ∈ U,
      (∀ v : E, a * ‖v‖ ^ 2 ≤ g.pullbackCoefficients f x v v) →
      (∀ j ≤ m + 2, ‖iteratedFDeriv ℝ j (g.pullbackCoefficients f) x‖ ≤ Z) →
      ∀ j ≤ m, D.curvatureDerivativeNorm j (f x) ≤ C := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_curvature_derivative_bound m ha Z
  refine ⟨C, hC, ?_⟩
  intro M _ _ _ g D f U hU hf hinv x hx hell hjets j hj
  obtain ⟨gE, DE, V, hV, hxV, hVU, hmetric⟩ :=
    RiemannianMetric.exists_local_realization hU hx (g.pullbackCoefficients f)
      (fun y hy => (g.contDiffAt_pullbackCoefficients
        (hf.contMDiffAt (hU.mem_nhds hy))).contDiffWithinAt)
      (fun y _ v w => g.symm (f y) _ _)
      (fun y hy v hv => by
        apply g.pos (f y)
        intro hz
        apply hv
        apply (hinv y hy).injective
        rw [map_zero]
        exact hz)
  have heq : gE.euclideanCoefficients =ᶠ[𝓝 x] g.pullbackCoefficients f :=
    eventually_of_mem (hV.mem_nhds hxV) hmetric
  have hellE : ∀ v : E, a * ‖v‖ ^ 2 ≤ gE.inner x v v := by
    intro v
    change a * ‖v‖ ^ 2 ≤ gE.euclideanCoefficients x v v
    rw [heq.eq_of_nhds]
    exact hell v
  have hjetsE : ∀ l ≤ m + 2, ‖iteratedFDeriv ℝ l gE.euclideanCoefficients x‖ ≤ Z := by
    intro l hl
    rw [(heq.iteratedFDeriv ℝ l).eq_of_nhds]
    exact hjets l hl
  have hnorm := DE.curvatureDerivativeNorm_eq_pullback D hV (hf.mono hVU)
    (fun y hy => hinv y (hVU hy))
    (fun y hy v w => congrArg (fun B => B v w) (hmetric y hy)) j hxV
  rw [← hnorm]
  exact hbound gE DE x hellE hjetsE j hj

end PoincareConjecture.M44
