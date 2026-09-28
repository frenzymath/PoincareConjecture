import PoincareConjecture.Proofs.M30.Thm11_8.RadiusDependentLeftCylinders
import PoincareConjecture.Proofs.M30.Thm11_8.FiniteLeftLocalExtension










set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M30

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold



theorem exists_raw_finite_closed_left_extension_threshold
    (P : M30ControlledBlowupPredecessors.{u}) :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 400 ∧
      ∀ (S : GeneralizedBlowupSequence.{u}) (epsilon C kappa r0 mu : ℝ),
        epsilon ≤ epsilon0 → ∀ T0 : ℝ≥0∞,
      ∀ _H : M30LongBlowupControls S epsilon C kappa r0 mu T0,
      ∀ T : ℝ, 0 < T → ENNReal.ofReal T < T0 →
      ∀ G : GeneralizedBlowupConvergence S (Ioc (-T) 0),
        ∃ Fbar : RicciFlow 3 G.limit.carrier.carrier (Icc (-T) 0),
          (∀ t ∈ Ioc (-T) 0, Fbar.metric t = G.limit.flow.metric t) ∧
          (∀ t ∈ Icc (-T) 0, G.limit.carrier.metricComplete (Fbar.metric t)) ∧
          (∀ t ∈ Icc (-T) 0, ∀ x : G.limit.carrier.carrier,
            (Fbar.connection t).NonnegativeCurvatureOperator x) ∧
          ∀ A : ℝ, 0 < A →
          ∀ U : TopologicalSpace.Opens G.limit.carrier.carrier,
            (U : Set G.limit.carrier.carrier) =
              (G.limit.flow.metric 0).ball G.limit.base A →
            ∃ delta : ℝ, 0 < delta ∧
              ∃ F : RicciFlow 3 U (Icc (-(T + delta)) 0),
                (∀ t ∈ Icc (-T) 0, ∀ (x : U) (v w : TangentSpace (𝓡 3) x),
                  (F.metric t).inner x v w = (Fbar.metric t).inner x.val
                    (mfderiv (𝓡 3) (𝓡 3)
                      (Subtype.val : U → G.limit.carrier.carrier) x v)
                    (mfderiv (𝓡 3) (𝓡 3)
                      (Subtype.val : U → G.limit.carrier.carrier) x w)) ∧
                ∀ t ∈ Icc (-(T + delta)) 0, ∀ x : U,
                  (F.connection t).NonnegativeCurvatureOperator x := by
  obtain ⟨epsilon0, hepsilon0, hepsilonMax, hleft⟩ :=
    exists_radius_dependent_left_cylinders_threshold P
  refine ⟨epsilon0, hepsilon0, hepsilonMax, ?_⟩
  intro S epsilon C kappa r0 mu hepsilon T0 H T hT hTT0 G
  obtain ⟨Tplus, _, hTTplus, hTplusT0⟩ := ENNReal.lt_iff_exists_real_btwn.mp hTT0
  have hTplus : 0 < Tplus := ENNReal.ofReal_pos.mp (lt_of_le_of_lt
    (by positivity : (0 : ℝ≥0∞) ≤ ENNReal.ofReal T) hTTplus)
  have hTTplus' : T < Tplus := (ENNReal.ofReal_lt_ofReal_iff hTplus).mp hTTplus
  have hcyl (A : ℝ) (hA : 0 < A) :
      ∃ delta : ℝ, 0 < delta ∧ ∃ B : ℝ, 0 ≤ B ∧
        ∀ᶠ k : ℕ in atTop,
          Nonempty (ControlledBlowupCylinder S (G.subsequence k) A (T + delta) B 1) := by
    obtain ⟨delta, hdelta, _, B, hB, hfamily⟩ := hleft S epsilon C kappa r0 mu
      hepsilon H.toM30CommonBlowupControls T Tplus hT hTTplus' G
        (H.slabs Tplus hTplus hTplusT0) A hA
    refine ⟨delta, hdelta, B, hB, (hfamily 1 (by norm_num)).mono ?_⟩
    intro k hk
    exact hk.map NoncollapsedControlledBlowupCylinder.toControlledBlowupCylinder
  obtain ⟨Fbar, hmetric, hcomplete, hsign, _, hlocal⟩ :=
    exists_complete_closed_left_extension_of_radius_dependent_cylinders
      P.m04.local_derivative_estimates hT G H.branch
      (fun A hA => G.subsequence_strictMono.tendsto_atTop.eventually (H.balls_compact A hA))
      hcyl
  exact ⟨Fbar, hmetric, hcomplete, hsign, hlocal⟩

end PoincareConjecture.M30
