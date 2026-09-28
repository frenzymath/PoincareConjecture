import PoincareConjecture.Proofs.M47.TerminalRegularGrowingSource
import PoincareConjecture.Proofs.M47.TerminalRegularCapturedJets
import PoincareConjecture.Proofs.M47.TerminalRegularScalarAnchor
import PoincareConjecture.Proofs.M47.TerminalRegularLiftedGerms
import PoincareConjecture.Proofs.M47.TerminalRegularLiftedJets
import PoincareConjecture.Proofs.M47.TerminalSourceCountableFiniteGerms
import PoincareConjecture.Proofs.M47.TerminalCurvatureEarlierReadout
import PoincareConjecture.Proofs.M47.TerminalCurvatureFiniteGermsFloor










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)

section Family

variable (S : RepairedControlledSchedulesData.{u})
  (B : M47ComponentAnalyticBounds.{u} S.setup.C) (p : SurgeryParameterPrefix S.constants)
  (F : ℕ → SurgeryFlowData.{u}) (O : ∀ k, SurgeryObservation (F k))
  (W : ∀ k, M33RegularHistoryWindow (F k)) (H : ∀ k, M33RegularHistoryData (W k))
  (base Q r A tau0 tau K L R rho : ℕ → ℝ) (N : ℕ → ℕ)
  (center : ∀ k, ((F k).slice (base k)).carrier)
  (data : ∀ k j, j ≤ k → TerminalRegularStageData S B p (O k) (H k)
    (base k) (Q k) (r k) (A j) (tau0 j) (tau j) (K j) (L j)
    ((j : ℝ) + 1) (R j) (rho j) (N j) (center k))

local notation "M" => (fun k : ℕ => Poincare.connectedComponentOpens E (center k))
local notation "gPhysical" => (fun k : ℕ =>
  M13.scaleSmoothMetric (SurgeryFlowData.metric (F k) (base k)) (Q k)
    (SurgeryFlowCylinder.scale_pos (TerminalRegularStageData.original (data k 0 (Nat.zero_le k)))))
local notation "gSource" => (fun k : ℕ =>
  RiemannianMetric.connectedComponentMetric (gPhysical k) (center k))
local notation "point" => (fun k : ℕ => (Subtype.mk (center k) mem_connectedComponent : M k))



theorem terminalSource_regular_terminal_curvature_bound
    (P : M46Predecessors.{u})
    {X : Type} [TopologicalSpace X] [ChartedSpace E X]
    [IsManifold (𝓡 3) ∞ X] [T3Space X] [ConnectedSpace X] [SecondCountableTopology X]
    (g : RiemannianMetric 3 X) (D : LeviCivitaData g) (hg : MetricComplete g)
    (nu : ℕ → ℕ) (hnu : StrictMono nu) (htau : ∀ j, 0 < tau j)
    (hA : ∀ s : ℝ, 0 < s → ∃ j, s ≤ A j)
    (V : ℕ → Set X) (hV : ∀ k, IsOpen (V k)) (hmono : Monotone V)
    (hconnected : ∀ k, IsConnected (V k)) (hcover : (⋃ k, V k) = univ)
    (hcompact : ∀ j, IsCompact (closure (V j))) (pX : X) (hpX : ∀ j, pX ∈ V j)
    (f : ∀ k : ℕ, X → Poincare.connectedComponentOpens E (center (nu k)))
    (hgeometry : ∀ k, Topology.IsOpenEmbedding (fun x : V k => f k x) ∧
      IsLocalDiffeomorphOn (𝓡 3) (𝓡 3) ∞ (f k) (V k))
    (hbase : ∀ k, f k pX = point (nu k))
    (c : ℕ → PartialDiffeomorph (𝓡 3) (𝓡 3) X E ∞)
    (hcoverC : ∀ x : X, ∃ i, x ∈ (c i).source)
    (e : ∀ k, ℕ → E → M (nu k)) (bound : ℕ → ℝ)
    (hbound : letI : ∀ k, MetricSpace (M k) :=
        fun k => terminalSourceComponentMetricSpace (gPhysical k) (center k)
      ∀ k i z, z ∈ (c i).target → dist (point (nu k)) (e k i z) ≤ bound i)
    (happrox : letI : ∀ k, MetricSpace (M k) :=
        fun k => terminalSourceComponentMetricSpace (gPhysical k) (center k)
      ∀ i C, IsCompact C → C ⊆ (c i).target → TendstoUniformlyOn
        (fun k z => dist (f k ((c i).symm z)) (e k i z)) (fun _ => 0) atTop C)
    (hjets : ∀ i m C, IsCompact C → C ⊆ (c i).target → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m
        ((gSource (nu k)).pullbackCoefficients (f k ∘ (c i).symm)))
      (iteratedFDeriv ℝ m (g.pullbackCoefficients (c i).symm)) atTop C)
    (hfloor : ∀ k, (r k)⁻¹ ^ 2 ≤ Q k)
    (hEpsilon : ∀ k, (F k).parameters.epsilon = S.setup.epsilon)
    (hC : ∀ k, (F k).parameters.C = S.setup.C)
    (hPast : ∀ k, SurgeryCanonicalOn (F k) (Ico 0 (base k)) (r k))
    {Z : ℕ → Type} [∀ n, TopologicalSpace (Z n)] [∀ n, ChartedSpace E (Z n)]
    [∀ n, IsManifold (𝓡 3) ∞ (Z n)]
    (tauG : ℕ → ℝ) (GG : ∀ n, RicciFlow 3 (Z n) (Icc (-tauG n) 0))
    (qG : ∀ n, Z n → X)
    (hfinite : TerminalSourceCountableFiniteGermsResult tauG GG qG g V hV) :
    ∃ K0 : ℝ, 1 ≤ K0 ∧ ∀ x, D.curvatureTensorNorm x ≤ K0 := by
  classical
  obtain ⟨J, lambda, hlambda, available, j, hj, _htarget, _hprojection, _hpoint,
    hmetric, phi, _hphi, hsource, hfactor, hbased⟩ :=
    terminalSource_regular_growing_sources S B p F O W H base Q r A tau0 tau K L R rho N
      center data nu V pX f hnu htau hA hV hmono hcompact hpX hgeometry hbase c hcoverC
      e bound hbound happrox
  let raw := fun k => nu (lambda k)
  let selected := fun k => data (raw k) (J k) (available k)
  let source := fun k => terminalRegularStageSource
    (F (raw k)) (base (raw k)) (Q (raw k)) (A (J k)) (center (raw k))
  let flow := fun k => (selected k).flow
  have hsourceJets := terminalSource_regular_captured_jets g (fun k => (flow k).metric 0)
    (fun k => gSource (raw k)) V hV hmono hcover j hj hmetric phi hsource
    (fun k => f (lambda k)) hfactor c
    (fun i m C hC hCi => (hjets i m C hC hCi).seq_tendstoUniformlyOn
      lambda hlambda.tendsto_atTop)
  have hscalar : D.scalarCurvature pX = 1 :=
    terminalSource_regular_scalar_one S B p (fun k => F (raw k)) (fun k => O (raw k))
      (fun k => W (raw k)) (fun k => H (raw k)) (base ∘ raw) (Q ∘ raw) (r ∘ raw)
      (A ∘ J) (tau0 ∘ J) (tau ∘ J) (K ∘ J) (L ∘ J) (fun k => (J k : ℝ) + 1)
      (R ∘ J) (rho ∘ J) (N ∘ J) (fun k => center (raw k)) selected
      g D V pX hpX phi hsource hbased c hcoverC hsourceJets
  let physical := fun k => terminalSourceNormal_historyCylinder (H (raw k)) (source k)
    (selected k).time (selected k).cylinder
  have hphysicalMetric := fun k => terminalSource_regular_included_metric (selected k)
  let domains : ℕ → Opens X := fun k => ⟨V k, hV k⟩
  let : ∀ k, ConnectedSpace (domains k) :=
    fun k => isConnected_iff_connectedSpace.mp (hconnected k)
  obtain ⟨s, delta, _hs, _hcover, hdelta, _htime, flows, hm, _hcharts,
    _hcompat, htriple, hop, _hambient⟩ := hfinite
  let : ChartedSpace E (ULift.{u} X) := Poincare.Manifold.uliftChartedSpace E X
  let : IsManifold (𝓡 3) ∞ (ULift.{u} X) := Poincare.Manifold.uliftIsManifold (𝓡 3) X
  let d := Poincare.Manifold.uliftDiffeomorph (𝓡 3) X
  let : ConnectedSpace (ULift.{u} X) := d.toHomeomorph.connectedSpace_iff.mpr inferInstance
  let : SecondCountableTopology (ULift.{u} X) := d.toHomeomorph.isEmbedding.secondCountableTopology
  let : MeasurableSpace (ULift.{u} X) := borel _
  let : BorelSpace (ULift.{u} X) := ⟨rfl⟩
  let gL := g.pullbackOfLocalDiffeomorph d d.isLocalDiffeomorph
  let DL : LeviCivitaData gL := gL.leviCivitaData
  let UL := fun k => terminalGermsOpenChartSource d d.isLocalDiffeomorph (domains k)
  obtain ⟨hgL, hULconnected, FL, hmL, hopL, htripleL, hambientL⟩ :=
    terminalSource_regular_lifted_germs.{u} g hg domains delta hdelta flows hm hop htriple
  let : ∀ k, ConnectedSpace (UL k) := hULconnected
  let VL : ℕ → Set (ULift.{u} X) := fun k => ULift.down ⁻¹' V k
  obtain ⟨hVL, hVLmono, hVLcompact, hVLcover, hpL⟩ :=
    terminalSource_regular_lifted_exhaustion.{u} V hV hmono hcompact hcover pX hpX
  let phiL := fun k => d.toPartialDiffeomorph.trans (phi k)
  let cL := fun i => d.toPartialDiffeomorph.trans (c i)
  obtain ⟨hsourceL, _hmapsL, hjetsL⟩ :=
    terminalSource_regular_lifted_source_jets.{u} g
      (fun k => (flow k).metric 0) phi c hsourceJets
  have hsourceL' (k : ℕ) : (phiL k).source = VL k := by
    rw [hsourceL, hsource k]
  have hcoverCL (x : ULift.{u} X) : ∃ i, x ∈ (cL i).source := by
    obtain ⟨i, hi⟩ := hcoverC x.down
    refine ⟨i, ?_⟩
    rw [(terminalSource_regular_lifted_chart_jets.{u} g (c i)).1]
    exact hi
  have hreadout := terminalCurvature_high_point_readout_of_source_cylinders S
    (fun k => F (raw k)) (fun k => (F (raw k)).slice (base (raw k)))
    (base ∘ raw) (Q ∘ raw) (tau ∘ J) (r ∘ raw) (fun k => htau (J k))
    source (fun k => (selected k).point) physical flow hphysicalMetric gL DL hgL
    VL hVL hVLmono hVLcover hVLcompact (ULift.up pX) hpL phiL hsourceL' cL hcoverCL hjetsL
    (fun k => hfloor (raw k)) (fun k => hEpsilon (raw k))
    (fun k => hC (raw k)) (fun k => hPast (raw k))
  have hepsilon : 0 < 2 * S.setup.epsilon := mul_pos (by norm_num) S.setup.epsilon_pos
  have hhalf : S.setup.epsilon ≤ S.calibration.epsilon₁ / 2 :=
    S.calibration.epsilon_source_le.trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hsmall : 2 * S.setup.epsilon ≤ S.calibration.epsilon₁ := by linarith
  have hcalibrated : 2 * S.setup.epsilon ≤ 1 / 200 :=
    S.calibration.two_epsilon_le_bounded_distance.trans S.calibration.epsilon₁₀_le
  have hscalarL : DL.scalarCurvature (ULift.up pX) ≠ 0 := by
    rw [(terminalSource_regular_lifted_curvature.{u} D DL (ULift.up pX)).1, hscalar]
    exact one_ne_zero
  obtain ⟨K0, hK0, hboundL⟩ := terminalCurvature_bound_of_finite_germs_floor
    (epsilon1 := S.calibration.epsilon₁) (epsilon := 2 * S.setup.epsilon)
    (A := 4 * max 1 S.setup.C) (H := 2) S.calibration.small_neck_scale_bound
    hepsilon hsmall hcalibrated (by positivity) DL P.m04 hgL (hambientL DL)
    (ULift.up pX) hscalarL UL delta hdelta FL hmL hopL htripleL hreadout
  refine ⟨K0, hK0, fun x => ?_⟩
  rw [← (terminalSource_regular_lifted_curvature.{u} D DL (ULift.up x)).2]
  exact hboundL (ULift.up x)

end Family

end PoincareConjecture.M47
