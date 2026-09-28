import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Cor6_67_SurvivalSlice
import PoincareConjecture.Proofs.M14.Sec6_5_LocalLipschitzConfinedEnergy











set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Proofs.M46

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T tau : ℝ} {x y : G.Point}

private theorem transported_inner {a b : G.Point} (h : a = b) (v : G.Horizontal a) :
    G.spacetime.horizontalMetric.inner b (h ▸ v) (h ▸ v) =
      G.spacetime.horizontalMetric.inner a v v := by
  cases h
  rfl



theorem initialValue_energy_zero {Z : G.Horizontal x}
    (Q : M14SquareRootInitialValuePath G T tau x y Z) :
    G.spacetime.horizontalMetric.inner (Q.square_path.curve 0)
      (Q.square_path.horizontal_velocity 0) (Q.square_path.horizontal_velocity 0) =
        4 * G.spacetime.horizontalMetric.inner x Z Z := by
  obtain ⟨hzero, hvelocity⟩ := Q.initial_velocity
  rw [← transported_inner hzero, hvelocity]
  simp only [map_smul, smul_apply, smul_eq_mul]
  ring





theorem confined_minimizers_initial_bound
    (LG : GeneralizedLGeometryConclusion G)
    (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (E : M14ExponentialFamily G T x)
    {F0 : Set G.Point} {delta H D CR Cgrad : ℝ}
    (hdelta : 0 < delta) (hD : 0 ≤ D) (hCR : 0 ≤ CR) (hCgrad : 0 ≤ Cgrad)
    (hRic : ∀ q ∈ F0, ∀ v w : G.Horizontal q, |horizontalRicci G.leafwise q v w| ≤
      CR * Real.sqrt (G.spacetime.horizontalMetric.inner q v v) *
        Real.sqrt (G.spacetime.horizontalMetric.inner q w w))
    (hgrad : ∀ q ∈ F0, ∀ v : G.Horizontal q,
      |M14HorizontalScalarDifferential G q v.val| ≤
        Cgrad * Real.sqrt (G.spacetime.horizontalMetric.inner q v v)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ tau : ℝ,
      delta ≤ Real.sqrt tau → Real.sqrt tau ≤ H → ∀ y : G.Point,
      ∀ p : M14BackwardPath G T 0 tau x y, M14IsMinimizing p →
      M14BackwardLAction G p ≤ D → MapsTo p.curve (Icc 0 tau) F0 →
      ∃ Z : G.Horizontal x, (Z, Real.sqrt tau) ∈ E.domain ∧
        EqOn p.curve (fun s => E.gamma Z (Real.sqrt s)) (Icc 0 tau) ∧
        E.gamma Z (Real.sqrt tau) = y ∧
        G.spacetime.horizontalMetric.inner x Z Z ≤ C := by
  let A := 2 * H ^ 2 * Cgrad + 4 * H * CR
  let B := Real.exp (A * H) * (2 * D + 4 * ((n : ℝ) * CR) * H ^ 3 + H)
  let C := (Real.sqrt (B / delta + 4 * H ^ 2)) ^ 2
  refine ⟨C, sq_nonneg _, ?_⟩
  intro tau htimeLow htimeHigh y p hp haction hconf
  obtain ⟨Z, Q, hQ⟩ := minimizing_initialValuePath LG p hp
  have hconfR (s : ℝ) (hs : s ∈ M14SqrtParameterInterval 0 tau) :
      Q.square_path.curve s ∈ F0 := by
    rw [Q.square_path.agrees s hs, hQ]
    apply hconf
    have hs0 : 0 ≤ s := by simpa only [Real.sqrt_zero] using hs.1
    exact ⟨sq_nonneg s, (sq_le_sq₀ hs0 (Real.sqrt_nonneg _) |>.mpr hs.2).trans
      (Real.sq_sqrt p.tau_lt.le).le⟩
  have hzero : (0 : ℝ) ∈ M14SqrtParameterInterval 0 tau := by
    exact ⟨by simp, Real.sqrt_nonneg tau⟩
  have henergy := M14.squareRoot_energy_uniform_bound hM12 Q.square_path Q.extension
    Q.euler hdelta htimeLow htimeHigh hCR hCgrad hD
    (by simpa only [hQ] using haction)
    (fun s hs => hRic _ (hconfR s hs))
    (fun s hs => hgrad _ (hconfR s hs)) hzero
  change G.spacetime.horizontalMetric.inner (Q.square_path.curve 0)
    (Q.square_path.horizontal_velocity 0) (Q.square_path.horizontal_velocity 0) +
      4 * (0 : ℝ) ^ 2 ≤ C at henergy
  rw [initialValue_energy_zero Q] at henergy
  obtain ⟨hsurvive, htrace, hend⟩ := initialValue_exponential_branch E Q
  rw [hQ] at htrace
  refine ⟨Z, hsurvive, htrace, hend, ?_⟩
  have hC : 0 ≤ C := sq_nonneg _
  nlinarith

end PoincareConjecture.Proofs.M46
