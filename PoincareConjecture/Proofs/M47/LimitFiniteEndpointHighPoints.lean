import PoincareConjecture.Proofs.M47.TerminalCurvatureEarlierCapture
import PoincareConjecture.Proofs.M47.TerminalCurvatureEarlierCanonical
import PoincareConjecture.Proofs.M47.TerminalCurvatureSurgeryCases
import PoincareConjecture.Proofs.M47.TerminalCurvatureFiniteGermsBound
import PoincareConjecture.Definitions.M45ControlledSchedules










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped ENNReal Manifold ContDiff Topology

universe u v

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)



theorem limitFinite_endpoint_high_points
    {ι : Type*} (sched : RepairedControlledSchedulesData.{u})
    (F : ℕ → SurgeryFlowData.{u}) (base t Q r : ℕ → ℝ)
    (hQ : ∀ k, 0 < Q k) (hfloor : ∀ k, (r k)⁻¹ ^ 2 ≤ Q k)
    (hEpsilon : ∀ k, (F k).parameters.epsilon = sched.setup.epsilon)
    (hC : ∀ k, (F k).parameters.C = sched.setup.C)
    (hPast : ∀ k, SurgeryCanonicalOn (F k) (Ico 0 (base k)) (r k))
    (htPast : ∀ k, t k ∈ Ico 0 (base k))
    (htDomain : ∀ k, t k ∈ (F k).time_domain)
    {X : Type v} [TopologicalSpace X] [ChartedSpace E X]
    [IsManifold (𝓡 3) ∞ X] [T2Space X] [T3Space X] [ConnectedSpace X]
    (g : RiemannianMetric 3 X) (D : LeviCivitaData g) (hcomplete : MetricComplete g)
    (U : ℕ → Set X) (hU : ∀ k, IsOpen (U k)) (hmono : Monotone U)
    (hcover : (⋃ k, U k) = univ) (hcompact : ∀ k, IsCompact (closure (U k)))
    (p : X) (hp : ∀ k, p ∈ U k)
    (psi : ∀ k, PartialDiffeomorph (𝓡 3) (𝓡 3) X ((F k).slice (t k)).carrier ∞)
    (hsource : ∀ k, (psi k).source = U k)
    (c : ι → PartialDiffeomorph (𝓡 3) (𝓡 3) X E ∞)
    (hcoverC : ∀ x, ∃ i, x ∈ (c i).source)
    (hjet : ∀ i m K, IsCompact K → K ⊆ (c i).target → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m
        ((rescaledMetric ((F k).metric (t k)) (Q k) (hQ k)).pullbackCoefficients
          (psi k ∘ (c i).symm)))
      (iteratedFDeriv ℝ m (g.pullbackCoefficients (c i).symm)) atTop K) :
    ∀ x, 2 ≤ D.scalarCurvature x →
      (∃ N : EpsilonNeck g, N.connection = D ∧ N.epsilon = 2 * sched.setup.epsilon ∧
        D.scalarCurvature x ≤ (4 * max 1 sched.setup.C) * D.scalarCurvature N.center) ∨
          IsCompact (univ : Set X) := by
  have hsmall : 2 * sched.setup.epsilon < 1 / 2 :=
    (sched.calibration.two_epsilon_le_bounded_distance.trans
      sched.calibration.epsilon₁₀_le).trans_lt (by norm_num)
  have hround : sched.setup.epsilon ≤ 1 / 200 :=
    sched.calibration.epsilon_source_le.trans (min_le_left _ _)
  intro x hx
  have hxone : 1 < D.scalarCurvature x := lt_of_lt_of_le (by norm_num) hx
  have hxpos : 0 < D.scalarCurvature x := lt_trans zero_lt_one hxone
  have hcanonical := terminalCurvature_eventually_earlier_canonical
    F base t Q r hQ hfloor g D U hU hmono hcover psi hsource c hcoverC hjet x hxone
      hEpsilon hC hPast htPast htDomain
  have hballs (R : ℝ) (hR : 0 < R) : ∃ j, ∀ᶠ k in atTop,
      (rescaledMetric ((F k).metric (t k)) (Q k) (hQ k)).ball (psi k x) R ⊆
        psi k '' U j :=
    terminalCurvature_source_balls_of_original_jets
      (fun k => rescaledMetric ((F k).metric (t k)) (Q k) (hQ k))
      g hcomplete U hU hmono hcover psi hsource c hcoverC (fun i => hjet i 0) x hR
  exact terminalCurvature_readout_of_surgery_source_canonical F t Q hQ g D
    U hU hmono hcover hcompact p hp psi hsource c hcoverC hjet x hxpos hballs
    sched.setup.epsilon_pos hsmall hround sched.setup.C_pos
    (hcanonical.mono fun _ hk => hk.2)



theorem limitFinite_endpoint_global_bound
    {ι : Type*} (sched : RepairedControlledSchedulesData.{u})
    (F : ℕ → SurgeryFlowData.{u}) (base t Q r : ℕ → ℝ)
    (hQ : ∀ k, 0 < Q k) (hfloor : ∀ k, (r k)⁻¹ ^ 2 ≤ Q k)
    (hEpsilon : ∀ k, (F k).parameters.epsilon = sched.setup.epsilon)
    (hC : ∀ k, (F k).parameters.C = sched.setup.C)
    (hPast : ∀ k, SurgeryCanonicalOn (F k) (Ico 0 (base k)) (r k))
    (htPast : ∀ k, t k ∈ Ico 0 (base k))
    (htDomain : ∀ k, t k ∈ (F k).time_domain)
    {X : Type u} [TopologicalSpace X] [ChartedSpace E X] [IsManifold (𝓡 3) ∞ X]
    [MeasurableSpace X] [BorelSpace X] [T2Space X] [T3Space X]
    [SecondCountableTopology X] [ConnectedSpace X]
    (g : RiemannianMetric 3 X) (D : LeviCivitaData g)
    (h04 : RicciFlowCurvatureTheory.{u}) (hcomplete : MetricComplete g)
    (hoperator : ∀ x, D.NonnegativeCurvatureOperator x)
    (U : ℕ → Set X) (hU : ∀ k, IsOpen (U k)) (hmono : Monotone U)
    (hcover : (⋃ k, U k) = univ) (hcompact : ∀ k, IsCompact (closure (U k)))
    (p : X) (hp : ∀ k, p ∈ U k)
    (psi : ∀ k, PartialDiffeomorph (𝓡 3) (𝓡 3) X ((F k).slice (t k)).carrier ∞)
    (hsource : ∀ k, (psi k).source = U k)
    (c : ι → PartialDiffeomorph (𝓡 3) (𝓡 3) X E ∞)
    (hcoverC : ∀ x, ∃ i, x ∈ (c i).source)
    (hjet : ∀ i m K, IsCompact K → K ⊆ (c i).target → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m
        ((rescaledMetric ((F k).metric (t k)) (Q k) (hQ k)).pullbackCoefficients
          (psi k ∘ (c i).symm)))
      (iteratedFDeriv ℝ m (g.pullbackCoefficients (c i).symm)) atTop K)
    {κ : Type*} (V : κ → TopologicalSpace.Opens X) [∀ i, ConnectedSpace (V i)]
    (tau : κ → ℝ) (htau : ∀ i, 0 < tau i)
    (L : ∀ i, RicciFlow 3 (V i) (Icc (-tau i) 0))
    (hmetric : ∀ i (x : V i) (v w : TangentSpace (𝓡 3) x),
      ((L i).metric 0).inner x v w = g.inner x.val v w)
    (hlocalOperator : ∀ i t, t ∈ Icc (-tau i) 0 → ∀ x,
      ((L i).connection t).NonnegativeCurvatureOperator x)
    (htriple : ∀ x y z : X, ∃ i, x ∈ V i ∧ y ∈ V i ∧ z ∈ V i) :
    ∃ B : ℝ, 0 < B ∧ ∀ x, D.curvatureTensorNorm x ≤ B := by
  classical
  by_cases hzero : ∀ x, D.scalarCurvature x = 0
  · refine ⟨1, zero_lt_one, fun x => ?_⟩
    have hbound := D.curvatureTensorNorm_le_scalarCurvature_sharp
      (h04.tensor_calculus 3 X g D) x (hoperator x)
    rw [hzero x] at hbound
    exact hbound.trans zero_le_one
  · push Not at hzero
    obtain ⟨q, hq⟩ := hzero
    have hreadout := limitFinite_endpoint_high_points sched F base t Q r hQ hfloor
      hEpsilon hC hPast htPast htDomain g D hcomplete U hU hmono hcover hcompact p hp
      psi hsource c hcoverC hjet
    have hhalf : sched.setup.epsilon ≤ sched.calibration.epsilon₁ / 2 :=
      sched.calibration.epsilon_source_le.trans
        ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
    have hsmall : 2 * sched.setup.epsilon ≤ sched.calibration.epsilon₁ := by linarith
    have hcalibrated : 2 * sched.setup.epsilon ≤ 1 / 200 :=
      sched.calibration.two_epsilon_le_bounded_distance.trans sched.calibration.epsilon₁₀_le
    have hA : 0 < 4 * max 1 sched.setup.C := by positivity
    exact terminalCurvature_bound_of_finite_germs (H := 2)
      sched.calibration.small_neck_scale_bound
      (mul_pos (by norm_num) sched.setup.epsilon_pos) hsmall hcalibrated hA
      D h04 hcomplete hoperator q hq V tau htau L hmetric hlocalOperator htriple hreadout

end PoincareConjecture.M47
