import PoincareConjecture.Proofs.M47.TerminalCurvatureEarlierReadout
import PoincareConjecture.Proofs.M47.TerminalCurvatureCountableFiniteGerms










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)

private noncomputable local instance selectedBridgeDualNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private noncomputable local instance selectedBridgeDualNormedSpace :
    NormedSpace ℝ (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

private noncomputable local instance selectedBridgeBilinearNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private noncomputable local instance selectedBridgeBilinearNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace



theorem terminalCurvature_bound_of_selected_source_finite_germs
    (sched : RepairedControlledSchedulesData.{u})
    (S : ℕ → SurgeryFlowData.{u}) (C : ℕ → GeneralizedSliceCarrier.{u})
    (b Q tau r : ℕ → ℝ) (htau : ∀ k, 0 < tau k)
    (V : ∀ k, Opens (C k).carrier) (q : ∀ k, V k)
    (e : ∀ k, SurgeryFlowCylinder (S k) (C k) (b k) (Q k)
      (Icc (-tau k) 0) (V k))
    (F : ∀ k, RicciFlow 3 (V k) (Icc (-tau k) 0))
    (hmetric : ∀ k (s : ℝ) (hs : s ∈ Icc (-tau k) 0) (y : V k)
      (v w : TangentSpace (𝓡 3) y),
      ((F k).metric s).inner y v w = (e k).pullbackInner s hs y.val
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : V k → (C k).carrier) y v)
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : V k → (C k).carrier) y w))
    {X : Type u} [TopologicalSpace X] [ChartedSpace E X]
    [IsManifold (𝓡 3) ∞ X] [T2Space X] [T3Space X]
    [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X]
    (g : RiemannianMetric 3 X) (D : LeviCivitaData g)
    (hC : RicciFlowCurvatureTheory.{u}) (hcomplete : MetricComplete g)
    (p : X) (hscalar : D.scalarCurvature p ≠ 0)
    (U : ℕ → Set X) (hU : ∀ k, IsOpen (U k)) (hmono : Monotone U)
    (hcover : (⋃ k, U k) = univ)
    (hcompact : ∀ j, IsCompact (closure (U j))) (hp : ∀ j, p ∈ U j)
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
    (hCsetup : ∀ k, (S k).parameters.C = sched.setup.C)
    (hPast : ∀ k, SurgeryCanonicalOn (S k) (Ico 0 (b k)) (r k))
    {P : ℕ → Type u} [∀ n, TopologicalSpace (P n)]
    [∀ n, ChartedSpace E (P n)] [∀ n, IsManifold (𝓡 3) ∞ (P n)]
    (tauG : ℕ → ℝ) (GG : ∀ n, RicciFlow 3 (P n) (Icc (-tauG n) 0))
    (qG : ∀ n, P n → X) (K : ℕ → Set X) (hK : ∀ m, IsOpen (K m))
    (hconnected : ∀ m, IsConnected (K m))
    (hfinite : TerminalSourceCountableFiniteGermsResult tauG GG qG g K hK) :
    ∃ K0 : ℝ, 1 ≤ K0 ∧ ∀ x, D.curvatureTensorNorm x ≤ K0 := by
  have hepsilon : 0 < 2 * sched.setup.epsilon :=
    mul_pos (by norm_num) sched.setup.epsilon_pos
  have hhalf : sched.setup.epsilon ≤ sched.calibration.epsilon₁ / 2 :=
    sched.calibration.epsilon_source_le.trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hsmall : 2 * sched.setup.epsilon ≤ sched.calibration.epsilon₁ := by
    linarith
  have hcalibrated : 2 * sched.setup.epsilon ≤ 1 / 200 :=
    sched.calibration.two_epsilon_le_bounded_distance.trans sched.calibration.epsilon₁₀_le
  have hA : 0 < 4 * max 1 sched.setup.C := by positivity
  have hreadout := terminalCurvature_high_point_readout_of_source_cylinders
    sched S C b Q tau r htau V q e F hmetric g D hcomplete U hU hmono hcover hcompact p hp
    phi hsource c hcoverC hjet hfloor hEpsilon hCsetup hPast
  exact terminalCurvature_bound_of_countable_finite_germs
    (epsilon1 := sched.calibration.epsilon₁)
    (epsilon := 2 * sched.setup.epsilon) (A := 4 * max 1 sched.setup.C) (H := 2)
    sched.calibration.small_neck_scale_bound hepsilon hsmall hcalibrated hA
    tauG GG qG g K hK hconnected hfinite D hC hcomplete p hscalar hreadout

end PoincareConjecture.M47
