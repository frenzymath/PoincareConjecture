import PoincareConjecture.Proofs.M47.TerminalCurvatureEarlierSequence
import PoincareConjecture.Proofs.M47.TerminalCurvatureEarlierCanonical
import PoincareConjecture.Proofs.M47.TerminalCurvatureEarlierCapture
import PoincareConjecture.Proofs.M47.TerminalCurvatureSurgeryCases











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u v

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)




theorem terminalCurvature_high_point_readout_of_source_cylinders
    (sched : RepairedControlledSchedulesData.{u})
    (S : ℕ → SurgeryFlowData.{u}) (C : ℕ → GeneralizedSliceCarrier.{u})
    (b Q tau r : ℕ → ℝ) (htau : ∀ k, 0 < tau k)
    (V : ∀ k, TopologicalSpace.Opens (C k).carrier) (q : ∀ k, V k)
    (e : ∀ k, SurgeryFlowCylinder (S k) (C k) (b k) (Q k) (Icc (-tau k) 0) (V k))
    (F : ∀ k, RicciFlow 3 (V k) (Icc (-tau k) 0))
    (hmetric : ∀ k (s : ℝ) (hs : s ∈ Icc (-tau k) 0) (y : V k)
      (v w : TangentSpace (𝓡 3) y),
      ((F k).metric s).inner y v w = (e k).pullbackInner s hs y.val
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : V k → (C k).carrier) y v)
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : V k → (C k).carrier) y w))
    {X : Type v} [TopologicalSpace X] [ChartedSpace E X]
    [IsManifold (𝓡 3) ∞ X] [T2Space X] [T3Space X] [ConnectedSpace X]
    (g : RiemannianMetric 3 X) (D : LeviCivitaData g) (hcomplete : MetricComplete g)
    (U : ℕ → Set X) (hU : ∀ k, IsOpen (U k)) (hmono : Monotone U)
    (hcover : (⋃ k, U k) = univ) (hcompact : ∀ j, IsCompact (closure (U j)))
    (p : X) (hp : ∀ j, p ∈ U j)
    (phi : ∀ k, PartialDiffeomorph (𝓡 3) (𝓡 3) X (V k) ∞)
    (hsource : ∀ k, (phi k).source = U k)
    (c : ℕ → PartialDiffeomorph (𝓡 3) (𝓡 3) X E ∞)
    (hcoverC : ∀ x : X, ∃ i, x ∈ (c i).source)
    (hjet : ∀ i m K, IsCompact K → K ⊆ (c i).target → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m
        (((F k).metric 0).pullbackCoefficients (phi k ∘ (c i).symm)))
      (iteratedFDeriv ℝ m (g.pullbackCoefficients (c i).symm)) atTop K)
    (hfloor : ∀ k, (r k)⁻¹ ^ 2 ≤ Q k)
    (hEpsilon : ∀ k, (S k).parameters.epsilon = sched.setup.epsilon)
    (hC : ∀ k, (S k).parameters.C = sched.setup.C)
    (hPast : ∀ k, SurgeryCanonicalOn (S k) (Ico 0 (b k)) (r k)) :
    ∀ x : X, 2 ≤ D.scalarCurvature x →
      (∃ N : EpsilonNeck g, N.connection = D ∧ N.epsilon = 2 * sched.setup.epsilon ∧
        D.scalarCurvature x ≤ (4 * max 1 sched.setup.C) * D.scalarCurvature N.center) ∨
        IsCompact (univ : Set X) := by
  obtain ⟨s, hs, _hs0, htime, psi, hpsi_source, _hpsi_map, hjets⟩ :=
    terminalCurvature_exists_earlier_physical_sequence S C b Q tau htau V q e F hmetric
      g U hU hmono hcover phi hsource c hjet
  let t : ℕ → ℝ := fun k => b k + s k / Q k
  have hsmall : 2 * sched.setup.epsilon < 1 / 2 :=
    (sched.calibration.two_epsilon_le_bounded_distance.trans
      sched.calibration.epsilon₁₀_le).trans_lt (by norm_num)
  have hround : sched.setup.epsilon ≤ 1 / 200 :=
    sched.calibration.epsilon_source_le.trans (min_le_left _ _)
  intro x hx
  have hcanonical := terminalCurvature_eventually_earlier_canonical
    S b t Q r (fun k => (e k).scale_pos) hfloor g D U hU hmono hcover
    psi hpsi_source c hcoverC hjets x (by linarith) hEpsilon hC hPast
    (fun k => (htime k).1) (fun k => (htime k).2)
  have hballs (R : ℝ) (hR : 0 < R) : ∃ j, ∀ᶠ k in atTop,
      (rescaledMetric ((S k).metric (t k)) (Q k) (e k).scale_pos).ball (psi k x) R ⊆
        psi k '' U j :=
    terminalCurvature_source_balls_of_original_jets
      (fun k => rescaledMetric ((S k).metric (t k)) (Q k) (e k).scale_pos)
      g hcomplete U hU hmono hcover psi hpsi_source c hcoverC
      (fun i => hjets i 0) x hR
  exact terminalCurvature_readout_of_surgery_source_canonical
    S t Q (fun k => (e k).scale_pos) g D U hU hmono hcover hcompact p hp
    psi hpsi_source c hcoverC hjets x (by linarith) hballs
    sched.setup.epsilon_pos hsmall hround sched.setup.C_pos
    (hcanonical.mono (fun _ hk => hk.2))

end PoincareConjecture.M47
