import PoincareConjecture.Proofs.M09.ActionCoercivity
import PoincareConjecture.Proofs.M09.GeometricEnergyBound
import PoincareConjecture.Proofs.M09.ExponentialAction
import PoincareConjecture.Proofs.M09.FamilySquareRegularization








set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [ConnectedSpace M] [T3Space M] [SecondCountableTopology M]

set_option backward.isDefEq.respectTransparency false in
theorem exists_uniform_lExponentialFamily_action_coercive {J : Set ℝ}
    (F : RicciFlow n M J) (hM04 : RicciFlowCurvatureTheory.{u})
    (T τmax : ℝ) (hτmax : 0 < τmax) (hwindow : Set.Icc (T - τmax) T ⊆ J)
    (hcurvature : CompleteBoundedCurvatureOn F (Set.Icc (T - τmax) T))
    (b : ℝ) (hb : 0 < b) (hbmax : b < τmax) :
    ∃ B C : ℝ, 0 < B ∧ 0 ≤ C ∧ ∀ (p : M) (A : LExponentialFamily F T τmax p)
      (Z : TangentSpace (𝓡 n) p) (τ : ℝ), 0 < τ → τ ≤ b →
      Real.sqrt τ * (4 * (F.metric T).inner p Z Z + 1) ≤
        Real.exp (B * Real.sqrt τ) *
          (2 * A.action Z τ + 4 * C * (Real.sqrt τ) ^ 3 + Real.sqrt τ) := by
  obtain ⟨B, hB, hbound⟩ := exists_uniform_geometricEnergy_bound F hM04 T τmax hτmax
    hwindow hcurvature b hb.le hbmax
  obtain ⟨C0, hC0, hcurv⟩ := hcurvature.2
  let C : ℝ := (n : ℝ) ^ 2 * C0
  have hC : 0 ≤ C := mul_nonneg (sq_nonneg _) hC0
  refine ⟨B, C, hB, hC, ?_⟩
  intro p A Z τ hτ hτb
  have hmax : τ < τmax := hτb.trans_lt hbmax
  let R := lExponentialFamily_squareRegularization hM04 hτmax hwindow A Z τ hτ hmax
  let I : Set ℝ := Set.Icc 0 (Real.sqrt τ)
  have hIeq : I = sqrtParameterInterval 0 τ := by
    simp only [I, sqrtParameterInterval, Real.sqrt_zero]
  have hId : UniqueDiffOn ℝ I := uniqueDiffOn_Icc (Real.sqrt_pos.mpr hτ)
  have hIU : I ⊆ R.path.domain := by rw [hIeq]; exact R.path.interval_subset
  have htime (s : ℝ) (hs : s ∈ I) :
      s ∈ Set.Ioo (-Real.sqrt τmax) (Real.sqrt τmax) :=
    ⟨(neg_lt_zero.mpr (Real.sqrt_pos.mpr hτmax)).trans_le hs.1,
      hs.2.trans_lt (Real.sqrt_lt_sqrt hτ.le hmax)⟩
  let e := regularizedCurveEnergy F T R.path.curve
  let e' : ℝ → ℝ := fun s ↦
    4 * s ^ 2 * mvfderiv (𝓡 n) (F.connection (T - s ^ 2)).scalarCurvature
      (R.path.curve s) (curveVelocity R.path.curve s) -
      4 * s * (F.connection (T - s ^ 2)).ricci (R.path.curve s)
        (curveVelocity R.path.curve s) (curveVelocity R.path.curve s)
  have hd : ∀ s ∈ I, HasDerivAt e (e' s) s := by
    intro s hs
    have hs' : s ∈ sqrtParameterInterval 0 τ := hIeq ▸ hs
    exact regularizedCurveEnergy_hasDerivAt F hM04 T τmax hτmax hwindow
      R.path.curve R.path.domain (sqrtParameterInterval 0 τ) R.path.open_domain
      R.path.interval_subset (hIeq ▸ hId) R.path.smooth R.velocity_extension s hs'
      (htime s hs) (R.equation s hs')
  have he : ∀ s ∈ I, 0 ≤ e s := by
    intro s _
    rcases eq_or_ne (curveVelocity (n := n) R.path.curve s) 0 with hzero | hne
    · simp [e, regularizedCurveEnergy, hzero]
    · exact ((F.metric (T - s ^ 2)).pos _ _ hne).le
  have hbe : ∀ s ∈ I, |e' s| ≤ B * (e s + 1) := by
    intro s hs
    exact hbound s ⟨hs.1, hs.2.trans (Real.sqrt_le_sqrt hτb)⟩
      (R.path.curve s) (curveVelocity R.path.curve s)
  let S : ℝ → ℝ := fun s ↦ (F.connection (T - s ^ 2)).scalarCurvature (R.path.curve s)
  have hSc : ContinuousOn S I := by
    have hg : ContMDiffOn (𝓘(ℝ, ℝ)) ((𝓘(ℝ, ℝ)).prod (𝓡 n)) ∞
        (fun s ↦ (s, R.path.curve s)) I :=
      contMDiffOn_id.prodMk (R.path.smooth.mono hIU)
    exact ((squareTime_scalar_smooth F hM04 T τmax hτmax hwindow).comp hg
      (fun s hs ↦ ⟨htime s hs, Set.mem_univ _⟩)).continuousOn
  have hSbound : ∀ s ∈ I, |S s| ≤ C := by
    intro s hs
    exact scalar_abs_le_of_curvature_bound hM04 (F.metric (T - s ^ 2))
      (F.connection (T - s ^ 2)) (R.path.curve s) C0
      ((le_abs_self _).trans (hcurv (T - s ^ 2)
        (squareTime_mem_window T hτmax (htime s hs)) (R.path.curve s)))
  have hcoercive := nonnegativeEnergy_action_reverse_bound e e' S (Real.sqrt τ) B C
    (Real.sqrt_nonneg τ) hB.le hC (fun s hs ↦ (hd s hs).continuousAt.continuousWithinAt)
    he hd hbe hSc hSbound
  have henergy0 : e 0 = 4 * (F.metric T).inner p Z Z := by
    have hinit := A.initial_derivative Z
    have hcast (x y : M) (h : x = y) (v : TangentSpace (𝓡 n) x) :
        (h ▸ v : TangentSpace (𝓡 n) y) = (show TangentSpace (𝓡 n) y from v) := by
      cases h
      rfl
    simp only [hcast] at hinit
    change (F.metric (T - (0 : ℝ) ^ 2)).inner (A.squareFamily Z 0)
      (curveVelocity (A.squareFamily Z) 0) (curveVelocity (A.squareFamily Z) 0) = _
    rw [hinit]
    rw [A.square_at_zero]
    simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), sub_zero,
      map_smul, smul_apply, smul_eq_mul]
    ring
  have haction : (∫ s in (0 : ℝ)..Real.sqrt τ, 2 * s ^ 2 * S s + (1 / 2 : ℝ) * e s) =
      A.action Z τ := by
    rw [lExponentialFamily_action_square_eq A Z τ hτ hmax]
    rfl
  rw [henergy0, haction] at hcoercive
  exact hcoercive

end PoincareConjecture.Proofs.M09
