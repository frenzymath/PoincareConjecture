import PoincareConjecture.Proofs.M10.TerminalGradient
import PoincareConjecture.Proofs.M10.RegularGerms
import Mathlib.Analysis.SpecialFunctions.Sqrt










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology BigOperators

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}


theorem normalized_action_hasDerivAt (G : LExponentialGeometry F T τmax p)
    (Z : TangentSpace (𝓡 n) p) {τ : ℝ} (hτ : 0 < τ) (hmax : τ < τmax) :
    HasDerivAt (fun s ↦ G.toLExponentialFamily.action Z s / (2 * Real.sqrt s))
      (((F.connection (T - τ)).scalarCurvature (G.gamma Z τ) +
          (F.metric (T - τ)).inner (G.gamma Z τ) (curveVelocity (G.gamma Z) τ)
            (curveVelocity (G.gamma Z) τ)) / 2 -
        (G.toLExponentialFamily.action Z τ / (2 * Real.sqrt τ)) / (2 * τ)) τ := by
  have hs : Real.sqrt τ ≠ 0 := (Real.sqrt_pos.2 hτ).ne'
  have h := (G.action_time_derivative Z τ hτ hmax).div
    ((Real.hasDerivAt_sqrt hτ.ne').const_mul 2) (mul_ne_zero (by norm_num) hs)
  apply h.congr_deriv
  dsimp only [backwardLIntegrand]
  field_simp
  rw [show Real.sqrt τ ^ 3 = τ * Real.sqrt τ by
    rw [pow_succ, Real.sq_sqrt hτ.le], Real.sq_sqrt hτ.le]
  ring

variable [ConnectedSpace M]


theorem reducedLength_time_gradient_identity
    (hDifferential : ReducedLengthDifferentialTheory F T τmax) {q : M} {τ : ℝ}
    (r : ReducedLengthRegularPoint F T τmax p q τ) :
    2 * deriv (fun s ↦ reducedLength F T p q s) τ =
      (F.connection (T - τ)).scalarCurvature q -
        reducedLengthGradientNormSq F T (fun z ↦ reducedLength F T p z.1 z.2) τ q -
        reducedLength F T p q τ / τ := by
  obtain ⟨hd, hg, _⟩ := hDifferential.regular_point_formulas p q τ r
  rw [(regular_time_eventuallyEq r).deriv_eq,
    r.representative_eq (q, τ) r.center_mem] at hd
  rw [regular_gradientNormSq_eq r,
    r.representative_eq (q, τ) r.center_mem] at hg
  rw [hd, hg]
  ring

set_option backward.isDefEq.respectTransparency false in

theorem reducedLength_gradientNormSq_eq_terminal_speed
    (hL : LGeodesicTheory F T τmax) (G : LExponentialGeometry F T τmax p)
    (Z : TangentSpace (𝓡 n) p) {τ : ℝ}
    (hreg : (Z, τ) ∈ G.toLExponentialFamily.regularDomain) :
    reducedLengthGradientNormSq F T (fun z ↦ reducedLength F T p z.1 z.2)
      τ (G.gamma Z τ) =
      (F.metric (T - τ)).inner (G.gamma Z τ) (curveVelocity (G.gamma Z) τ)
        (curveVelocity (G.gamma Z) τ) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric (T - τ)).toRiemannianMetric⟩
  obtain ⟨hτ, hmax, hmin, _⟩ := hreg.1
  have hsrc : (Z, τ) ∈ G.regular_chart.source := G.regular_source.symm ▸ hreg
  have htgt : (G.gamma Z τ, τ) ∈ G.regularImage := by
    change (G.gamma Z τ, τ) ∈ G.regular_chart.target
    simpa only [G.regular_forward] using G.regular_chart.map_source hsrc
  have hr := G.regular_point (G.gamma Z τ, τ) htgt
  have hpair := reducedLength_differential_eq_terminal_pairing hL G Z hτ hmax hmin
    ((reducedLength_space_contMDiffAt hr).mdifferentiableAt (by simp)) hreg.2.2
  unfold reducedLengthGradientNormSq
  simp_rw [hpair]
  exact (((F.metric (T - τ)).orthonormalBasis (G.gamma Z τ)).sum_sq_inner_left _).trans
    (real_inner_self_eq_norm_sq _).symm


theorem normalized_action_regular_hasDerivAt
    (hL : LGeodesicTheory F T τmax)
    (hDifferential : ReducedLengthDifferentialTheory F T τmax)
    (G : LExponentialGeometry F T τmax p) (Z : TangentSpace (𝓡 n) p) {τ : ℝ}
    (hreg : (Z, τ) ∈ G.toLExponentialFamily.regularDomain) :
    HasDerivAt (fun s ↦ G.toLExponentialFamily.action Z s / (2 * Real.sqrt s))
      (deriv (fun s ↦ reducedLength F T p (G.gamma Z τ) s) τ +
        reducedLengthGradientNormSq F T (fun z ↦ reducedLength F T p z.1 z.2)
          τ (G.gamma Z τ)) τ := by
  obtain ⟨hτ, hmax, hmin, _⟩ := hreg.1
  have hsrc : (Z, τ) ∈ G.regular_chart.source := G.regular_source.symm ▸ hreg
  have htgt : (G.gamma Z τ, τ) ∈ G.regularImage := by
    change (G.gamma Z τ, τ) ∈ G.regular_chart.target
    simpa only [G.regular_forward] using G.regular_chart.map_source hsrc
  have hid := reducedLength_time_gradient_identity hDifferential
    (G.regular_point (G.gamma Z τ, τ) htgt)
  have ha := reducedLength_eq_normalized_action_of_minimizing hL G Z hτ hmax hmin
  have hg := reducedLength_gradientNormSq_eq_terminal_speed hL G Z hreg
  apply (normalized_action_hasDerivAt G Z hτ hmax).congr_deriv
  rw [← ha, ← hg]
  field_simp [hτ.ne']
  have hid' : 2 * deriv (fun s ↦ reducedLength F T p (G.gamma Z τ) s) τ =
      (F.connection (T - τ)).scalarCurvature (G.gamma Z τ) -
        reducedLengthGradientNormSq F T (fun z ↦ reducedLength F T p z.1 z.2)
          τ (G.gamma Z τ) - reducedLength F T p (G.gamma Z τ) τ / τ := by
    simpa only [Prod.fst, Prod.snd] using hid
  have hidmul := congrArg (fun x : ℝ ↦ x * τ) hid'
  field_simp [hτ.ne'] at hidmul
  nlinarith [hidmul]

end PoincareConjecture.M10
