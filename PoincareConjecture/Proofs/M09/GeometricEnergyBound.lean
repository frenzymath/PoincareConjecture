import PoincareConjecture.Proofs.M09.ScalarDifferentialBound
import PoincareConjecture.Proofs.M09.BufferedDerivatives
import PoincareConjecture.Proofs.M09.CurvatureWindow
import PoincareConjecture.Proofs.M09.EnergyBound
import PoincareConjecture.Proofs.M09.CoordinateEnergy

set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [ConnectedSpace M] [T3Space M] [SecondCountableTopology M]

theorem exists_uniform_geometricEnergy_bound {J : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T τmax : ℝ) (hτmax : 0 < τmax)
    (hwindow : Set.Icc (T - τmax) T ⊆ J)
    (hcurvature : CompleteBoundedCurvatureOn F (Set.Icc (T - τmax) T))
    (b : ℝ) (hb : 0 ≤ b) (hbmax : b < τmax) :
    ∃ A : ℝ, 0 < A ∧ ∀ s ∈ Set.Icc 0 (Real.sqrt b), ∀ (x : M)
      (V : TangentSpace (𝓡 n) x),
      |4 * s ^ 2 * mvfderiv (𝓡 n) (F.connection (T - s ^ 2)).scalarCurvature x V -
        4 * s * (F.connection (T - s ^ 2)).ricci x V V| ≤
        A * ((F.metric (T - s ^ 2)).inner x V V + 1) := by
  obtain ⟨C1, hC1, hderiv⟩ :=
    exists_uniform_curvatureDerivative_bound F hM04 T τmax hτmax hwindow hcurvature
      1 b hb hbmax
  obtain ⟨K, hK, hbound⟩ := hcurvature.2
  let B : ℝ := (n : ℝ) * K
  let C : ℝ := (n : ℝ) ^ 2 * C1
  let H : ℝ := Real.sqrt b
  let A0 : ℝ := 2 * H ^ 2 * C + 4 * H * B
  have hB : 0 ≤ B := mul_nonneg (Nat.cast_nonneg n) hK
  have hC : 0 ≤ C := mul_nonneg (sq_nonneg _) hC1.le
  have hA0 : 0 ≤ A0 := by dsimp [A0, H]; positivity
  refine ⟨A0 + 1, by linarith, ?_⟩
  intro s hs x V
  have hs2 : s ^ 2 ∈ Set.Icc 0 b := by
    refine ⟨sq_nonneg s, ?_⟩
    nlinarith [Real.sq_sqrt hb, hs.1, hs.2, Real.sqrt_nonneg b]
  have ht : T - s ^ 2 ∈ Set.Icc (T - τmax) T := by
    constructor <;> linarith [hs2.1, hs2.2]
  let g := F.metric (T - s ^ 2)
  let D := F.connection (T - s ^ 2)
  let e : ℝ := g.inner x V V
  have he : 0 ≤ e := by
    rcases eq_or_ne V 0 with rfl | hV
    · simp [e]
    · exact (g.pos x V hV).le
  have hdR : |mvfderiv (𝓡 n) D.scalarCurvature x V| ≤ C * Real.sqrt e := by
    apply (scalarCurvature_mvfderiv_abs_le hM04 g D x V).trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hderiv (s ^ 2) hs2 x) (sq_nonneg _))
      (Real.sqrt_nonneg _)
  have hric : |D.ricci x V V| ≤ B * e :=
    ricci_quadratic_abs_le_of_curvature_bound hM04 g D x V K
      ((le_abs_self _).trans (hbound (T - s ^ 2) ht x))
  have h := regularizedEnergy_abs_bound s H B C e _ _ hs.1 hs.2 hB hC he hdR hric
  exact h.trans (mul_le_mul_of_nonneg_right (by dsimp [A0]; linarith) (by linarith))

theorem exists_uniform_squareChartEnergy_exp_bound {J : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T τmax : ℝ) (hτmax : 0 < τmax)
    (hwindow : Set.Icc (T - τmax) T ⊆ J)
    (hcurvature : CompleteBoundedCurvatureOn F (Set.Icc (T - τmax) T))
    (b : ℝ) (hb : 0 < b) (hbmax : b < τmax) :
    ∃ A : ℝ, 0 < A ∧ ∀ (p : M) (a v : ℝ → EuclideanSpace ℝ (Fin n))
      (h : ℝ), 0 ≤ h → h < Real.sqrt b →
      (∀ s ∈ Set.Icc 0 h, a s ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).target) →
      (∀ s ∈ Set.Icc 0 h, HasDerivAt a (v s) s) →
      (∀ s ∈ Set.Icc 0 h, HasDerivAt v
        (regularizedCoordinatePhase (squareChartMetric F T p) (squareChartScalar F T p)
          (s, (a s, v s))).2 s) →
      ∀ s ∈ Set.Icc 0 h,
        squareChartMetric F T p (s, a s) (v s) (v s) + 1 ≤
          (squareChartMetric F T p (0, a 0) (v 0) (v 0) + 1) * Real.exp (A * s) := by
  obtain ⟨A, hA, hbound⟩ :=
    exists_uniform_geometricEnergy_bound F hM04 T τmax hτmax hwindow hcurvature b hb.le hbmax
  refine ⟨A, hA, ?_⟩
  intro p a v h hh hhb hy ha hv
  have hw : Set.Icc (T - b) T ⊆ J := by
    intro t ht
    exact hwindow ⟨by linarith [ht.1], ht.2⟩
  let e : ℝ → ℝ := fun s ↦ squareChartMetric F T p (s, a s) (v s) (v s)
  let x : ℝ → M := fun s ↦ (chartAt (EuclideanSpace ℝ (Fin n)) p).symm (a s)
  let V := fun s ↦ mfderiv (𝓡 n) (𝓡 n)
    (chartAt (EuclideanSpace ℝ (Fin n)) p).symm (a s) (v s)
  let e' : ℝ → ℝ := fun s ↦
    4 * s ^ 2 * mvfderiv (𝓡 n) (F.connection (T - s ^ 2)).scalarCurvature (x s) (V s) -
      4 * s * (F.connection (T - s ^ 2)).ricci (x s) (V s) (V s)
  have hd : ∀ s ∈ Set.Icc 0 h, HasDerivAt e (e' s) s := by
    intro s hs
    apply squareChartEnergy_hasDerivAt F hM04 T b hb hw p a v s
    · exact ⟨lt_of_lt_of_le (neg_lt_zero.mpr (Real.sqrt_pos.mpr hb)) hs.1,
        hs.2.trans_lt hhb⟩
    · exact hy s hs
    · exact ha s hs
    · exact hv s hs
  apply nonnegativeEnergy_exp_bound e e' h A hh hA.le
  · exact fun s hs ↦ (hd s hs).continuousAt.continuousWithinAt
  · intro s hs
    rcases eq_or_ne (v s) 0 with hv0 | hv0
    · simp [e, hv0]
    · exact (squareChartMetric_pos F T p (s, a s) (hy s hs) (v s) hv0).le
  · exact fun s hs ↦ hd s ⟨hs.1, hs.2.le⟩
  · intro s hs
    exact hbound s ⟨hs.1, hs.2.le.trans hhb.le⟩ (x s) (V s)

end PoincareConjecture.Proofs.M09
