import PoincareConjecture.Proofs.M47.TerminalGermsPinchedOperator
import PoincareConjecture.Proofs.M47.TerminalCurvatureOriginalChartBound

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Poincare.Gluing TopologicalSpace
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)

private noncomputable local instance pinchedChartBoundDualAdd : NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private noncomputable local instance pinchedChartBoundDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

private noncomputable local instance pinchedChartBoundBilinAdd :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private noncomputable local instance pinchedChartBoundBilinSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

section OriginalCharts

variable {ι : Type*} (U : ι → Opens E) [∀ i, Nonempty (U i)]

noncomputable local instance originalChartSpace (i : ι) : ChartedSpace E (U i) :=
  (U i).isOpen.isOpenEmbedding_subtypeVal.singletonChartedSpace

noncomputable local instance originalChartManifold (i : ι) :
    IsManifold (𝓡 3) ∞ (U i) :=
  (U i).isOpen.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 3) (n := ∞)

variable (S : RepairedControlledSchedulesData.{u})
  (B : M47ComponentAnalyticBounds.{u} S.setup.C)
  (p : SurgeryParameterPrefix S.constants) (P : M46Predecessors.{u})
  (tau : ι → ℝ) (htau : ∀ i, 0 < tau i)
  (G : ∀ i, RicciFlow 3 (U i) (Icc (-tau i) 0))
  (coeff : ι → ℝ × E → E →L[ℝ] E →L[ℝ] ℝ)
  (hcoeff : ∀ i t, t ∈ Icc (-tau i) 0 → ∀ (x : U i) v w,
    ((G i).metric t).inner x v w = coeff i (t, x) v w)
  (F₀ : ι → ℕ → SurgeryFlowData.{u})
  (O : ∀ i k, SurgeryObservation (F₀ i k))
  (W : ∀ i k, M33RegularHistoryWindow (F₀ i k))
  (H : ∀ i k, M33RegularHistoryData (W i k))
  (C₀ : ι → ℕ → GeneralizedSliceCarrier.{u})
  (base Q rNext : ι → ℕ → ℝ)
  (V : ∀ i k, Opens (C₀ i k).carrier)
  (e : ∀ i k, GeneralizedFlowCylinder (H i k).generalized (C₀ i k)
    (base i k) (Q i k) (Icc (-tau i) 0) (V i k))
  (Fseq : ∀ i k, RicciFlow 3 (V i k) (Icc (-tau i) 0))
  (R L eta0 : ι → ℝ)
  (C : ∀ i k, TerminalSourceChart ((Fseq i k).metric 0) (R i))
  (hGood : ∀ i, ∀ᶠ k in atTop, TerminalSourceJetsG4Good S B p (O i k) (H i k)
    (V i k) (e i k) (Fseq i k) (L := L i) (eta := eta0 i) (rNext := rNext i k) (C i k))
  (hmetric : ∀ i k (s : ℝ) (hs : s ∈ Icc (-tau i) 0) (x : V i k),
    ∀ v w : TangentSpace (𝓡 3) x,
      ((Fseq i k).metric s).inner x v w = (e i k).pullbackInner s hs x.val
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : V i k → (C₀ i k).carrier) x v)
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : V i k → (C₀ i k).carrier) x w))
  (hQ : ∀ i, Tendsto (Q i) atTop atTop)
  (phi : ∀ i k, U i → V i k)
  (hphi : ∀ i k, IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (phi i k))
  (sigma : ℕ → ℕ) (hsigma : StrictMono sigma)
  (hjet : ∀ i m K, IsCompact K → K ⊆ Ioo (-tau i) 0 ×ˢ U i → TendstoUniformlyOn
    (fun k => iteratedFDeriv ℝ m (fun z : ℝ × E =>
      ((Fseq i (sigma k)).metric z.1).pullbackCoefficients
        (ChartDistance.chartParametrization (fun j => (U j : Set E))
          (fun j => (U j).isOpen) (phi i (sigma k))) z.2))
    (iteratedFDeriv ℝ m (coeff i)) atTop K)

include htau hcoeff hGood hmetric hQ hphi hsigma hjet P

theorem terminalGerms_original_chart_operator_of_first_failure :
    ∀ i t, t ∈ Icc (-tau i) 0 → ∀ x,
      ((G i).connection t).NonnegativeCurvatureOperator x := by
  intro i
  apply terminalGerms_operator_of_original_chart_jets (fun j => (U j : Set E))
    (fun j => (U j).isOpen) (neg_neg_of_pos (htau i))
    (fun k => Fseq i (sigma k)) i (fun k => phi i (sigma k))
    (fun k => hphi i (sigma k)) (G i) (coeff i) (hcoeff i) (hjet i)
  have hsource := terminalCurvature_eventually_source_sectional atTop S B p P
    (F₀ i) (O i) (W i) (H i) (C₀ i) (base i) (Q i) (rNext i) (V i) (e i)
    (Fseq i) (C i) (hGood i) (hmetric i) (hQ i)
  intro eta heta
  exact hsigma.tendsto_atTop.eventually (hsource eta heta)

theorem terminalCurvature_bound_of_pinched_original_charts
    {epsilon1 epsilon A Hscalar : ℝ} (hM45 : M45SmallNeckScaleBound.{u} epsilon1)
    (hepsilon : 0 < epsilon) (hsmall : epsilon ≤ epsilon1)
    (hcalibrated : epsilon ≤ 1 / 200) (hA : 0 < A)
    {M : Type u} [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]
    [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
    [SecondCountableTopology M] [ConnectedSpace M]
    {g : RiemannianMetric 3 M} (D : LeviCivitaData g) (hcomplete : MetricComplete g)
    (p0 : M) (hscalar : D.scalarCurvature p0 ≠ 0)
    (q : ∀ i, U i → M)
    (hq : ∀ i, IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (q i))
    (hcover : ∀ y, ∃ i x, q i x = y)
    (hinv : ∀ i j t, t ∈ Icc (-tau i) 0 → t ∈ Icc (-tau j) 0 →
      ∀ (x : U i) (y : U j), q i x = q j y →
      ∀ (a b : TangentSpace (𝓡 3) x) (c d : TangentSpace (𝓡 3) y),
        mfderiv (𝓡 3) (𝓡 3) (q i) x a = mfderiv (𝓡 3) (𝓡 3) (q j) y c →
        mfderiv (𝓡 3) (𝓡 3) (q i) x b = mfderiv (𝓡 3) (𝓡 3) (q j) y d →
        ((G i).metric t).inner x a b = ((G j).metric t).inner y c d)
    (hterminal : ∀ i (x : U i) (a b : TangentSpace (𝓡 3) x),
      ((G i).metric 0).inner x a b = g.inner (q i x)
        (mfderiv (𝓡 3) (𝓡 3) (q i) x a) (mfderiv (𝓡 3) (𝓡 3) (q i) x b))
    (exh : ℕ → Set M) (hopen : ∀ j, IsOpen (exh j))
    (hconnected : ∀ j, IsConnected (exh j))
    (hcompact : ∀ j, IsCompact (closure (exh j)))
    (hnested : ∀ j, closure (exh j) ⊆ exh (j + 1))
    (hexhaust : (⋃ j, exh j) = univ)
    (hreadout : ∀ x, Hscalar ≤ D.scalarCurvature x →
      (∃ N : EpsilonNeck g, N.connection = D ∧ N.epsilon = epsilon ∧
        D.scalarCurvature x ≤ A * D.scalarCurvature N.center) ∨ IsCompact (univ : Set M)) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ x, D.curvatureTensorNorm x ≤ B0 := by
  apply terminalCurvature_bound_of_original_chart_flows
    hM45 hepsilon hsmall hcalibrated hA D P.m04 hcomplete p0 hscalar
    tau htau G q hq hcover hinv hterminal ?_ exh hopen hconnected hcompact
    hnested hexhaust hreadout
  exact terminalGerms_original_chart_operator_of_first_failure U S B p P tau htau
    G coeff hcoeff F₀ O W H C₀ base Q rNext V e Fseq R L eta0 C hGood hmetric
    hQ phi hphi sigma hsigma hjet

end OriginalCharts

end PoincareConjecture.M47
