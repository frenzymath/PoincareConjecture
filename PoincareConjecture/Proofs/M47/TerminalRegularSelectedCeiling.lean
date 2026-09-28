import PoincareConjecture.Proofs.M47.TerminalRegularFiniteGerms
import PoincareConjecture.Proofs.M47.TerminalRegularAtlasCharts
import PoincareConjecture.Proofs.M47.TerminalRegularCurvatureApplication
import PoincareConjecture.Proofs.M47.TerminalRegularScalarCeiling










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter TopologicalSpace Poincare.Gluing
open scoped Manifold ContDiff Topology NNReal

universe u

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)

private theorem selected_locallyCompact_t3 (X : Type*) [TopologicalSpace X]
    [T2Space X] [LocallyCompactSpace X] : T3Space X := inferInstance

section Family

variable (S : RepairedControlledSchedulesData.{u})
  (B : M47ComponentAnalyticBounds.{u} S.setup.C) (p : SurgeryParameterPrefix S.constants)
  (F : ℕ → SurgeryFlowData.{u}) (obs : ∀ k, SurgeryObservation (F k))
  (W : ∀ k, M33RegularHistoryWindow (F k)) (H : ∀ k, M33RegularHistoryData (W k))
  (base Q r A tau0 tau K L R rho : ℕ → ℝ) (N : ℕ → ℕ)
  (center : ∀ k, ((F k).slice (base k)).carrier)
  (data : ∀ k j, j ≤ k → TerminalRegularStageData S B p (obs k) (H k)
    (base k) (Q k) (r k) (A j) (tau0 j) (tau j) (K j) (L j)
    ((j : ℝ) + 1) (R j) (rho j) (N j) (center k))
  (hrho : ∀ j, 0 < rho j)

local notation "label" => terminalSourceCountableLabel N
local notation "U" => (fun n => terminalSourceCountableDomain (rho (Sigma.fst (label n))))
local notation "Uset" => (fun n => (U n : Set E))
local notation "hU" => (fun n => TopologicalSpace.Opens.isOpen (U n))
local notation "M" => (fun k : ℕ => Poincare.connectedComponentOpens E (center k))
local notation "gPhysical" => (fun k : ℕ =>
  M13.scaleSmoothMetric (SurgeryFlowData.metric (F k) (base k)) (Q k)
    (SurgeryFlowCylinder.scale_pos (TerminalRegularStageData.original (data k 0 (Nat.zero_le k)))))
local notation "gSource" => (fun k : ℕ =>
  RiemannianMetric.connectedComponentMetric (gPhysical k) (center k))
local notation "e" => (fun (k j : ℕ) (hjk : j ≤ k) => TerminalRegularStageData.maps (data k j hjk))
local notation "total" => (fun k n => terminalSourceCountableMap hrho e k
  (Sigma.fst (label n)) (Sigma.snd (label n)))
local notation "point" => (fun k : ℕ => (Subtype.mk (center k) mem_connectedComponent : M k))

include data hrho




theorem terminalSource_regular_selected_ceiling
    (P : M46Predecessors.{u}) (htau : ∀ j, 0 < tau j)
    (hrhoR : ∀ j, 2 * rho j < R j)
    (hsmall : ∀ j s, |s| ≤ 2 * rho j →
      ((13 * max (4 * L j / 3) 1) * s ^ 2) *
        Real.exp (max 1 ((13 * max (4 * L j / 3) 1) * s ^ 2)) ≤ 3)
    (hQ : Tendsto Q atTop atTop)
    (hA : ∀ a : ℝ, 0 < a → ∃ j, a ≤ A j)
    (hfloor : ∀ k, (r k)⁻¹ ^ 2 ≤ Q k)
    (hEpsilon : ∀ k, (F k).parameters.epsilon = S.setup.epsilon)
    (hC : ∀ k, (F k).parameters.C = S.setup.C)
    (hPast : ∀ k, SurgeryCanonicalOn (F k) (Ico 0 (base k)) (r k)) :
    ∃ nu : ℕ → ℕ, StrictMono nu ∧ ∃ K0 : ℝ, 1 ≤ K0 ∧
      ∀ a : ℝ, 0 < a → ∀ᶠ k in atTop,
        ∀ z ∈ ((F (nu k)).metric (base (nu k))).ball (center (nu k))
            (a / Real.sqrt (Q (nu k))),
          ((F (nu k)).connection (base (nu k))).scalarCurvature z ≤ (2 * K0) * Q (nu k) := by
  classical
  let : ∀ k, MetricSpace (M k) :=
    fun k => terminalSourceComponentMetricSpace (gPhysical k) (center k)
  let : ∀ n, Nonempty (U n) := fun n => ⟨terminalSourceCountableZero (hrho (label n).1)⟩
  let : ∀ n, ChartedSpace E (U n) :=
    fun n => (U n).isOpen.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let : ∀ n, IsManifold (𝓡 3) ∞ (U n) :=
    fun n => (U n).isOpen.isOpenEmbedding_subtypeVal.isManifold_singleton
  let : ∀ n, LocallyCompactSpace (U n) := fun n => (U n).isOpen.locallyCompactSpace
  obtain ⟨sigma, hsigma, _hlate, B0, hB0, hBjets, Bminus, hBminus, hNegative,
    D, hD, he, hc, hlower, ho, hconn, hbase, hatlas⟩ :=
    terminalSource_regular_countable_atlas S B p F obs W H base Q r A tau0 tau K L R rho N
      center data hrho P htau hrhoR hsmall
  let hpoint := fun n n' x y =>
    (hD n n').tendstoLocallyUniformlyOn.tendsto_at (mem_univ (x, y))
  let c := fun n => terminalSourceCountableScaleFactor (rho 0) (rho (label n).1) / 2
  let overlap := ChartDistance.overlapSystem hpoint (fun _ => (3 / 2 : ℝ≥0))
    he c hc hlower ho hconn
  obtain ⟨hT2, hSecond, hO, gLocal, _hcompat, hgLocal, hconnected,
    gQ, hgQ, hgMetric, V, hV, hVc, hVp, hVK, hVnested, hVcover,
    kappa, hkappa, f, hf, happrox, hfjets, _hescape⟩ := hatlas
  let : T2Space (Quotient overlap.setoid) := hT2
  let : SecondCountableTopology (Quotient overlap.setoid) := hSecond
  let : ConnectedSpace (Quotient overlap.setoid) := hconnected
  let := quotientChartedSpace Uset hU overlap
  let := quotient_isManifold Uset hU overlap hO
  let : LocallyCompactSpace (Quotient overlap.setoid) := ChartedSpace.locallyCompactSpace E _
  let : T3Space (Quotient overlap.setoid) := selected_locallyCompact_t3 _
  let DQ : LeviCivitaData gQ := gQ.leviCivitaData
  have hterminal (n : ℕ) (x : U n) (v w : TangentSpace (𝓡 3) x) :
      B0 n x v w = gQ.inner (overlap.include n x)
        (mfderiv (𝓡 3) (𝓡 3) (overlap.include n) x v)
        (mfderiv (𝓡 3) (𝓡 3) (overlap.include n) x w) :=
    (hgLocal n x v w).symm.trans (hgMetric n x v w)
  obtain ⟨G, _hGzero, hGcoeff⟩ := terminalSource_regular_chart_flows
    S B p F obs W H base Q r A tau0 tau K L R rho N center data hrho
    P htau hrhoR hsmall hsigma B0 Bminus hB0 hBminus
    (fun n => hBjets n 0) hNegative gLocal hgLocal
  obtain ⟨_he', _hc', _hlower', _ho', _hconn', germs⟩ := terminalSource_regular_finite_germs
    S B p F obs W H base Q r A tau0 tau K L R rho N center data hrho
    P htau hrhoR hsmall hQ hsigma B0 Bminus hB0 hBminus
    (fun n => hBjets n 0) hNegative G hGcoeff D hD
  have hfinite := germs hO gQ hterminal V hV hVc hVK hVnested hVcover
  obtain ⟨charts, hinverse, _hchartSource, htarget, hchartCover, _hcoeff, hchartJets⟩ :=
    terminalSource_regular_atlas_charts Uset hU overlap hO gQ B0 hterminal
  let nu := sigma ∘ kappa
  have hnu : StrictMono nu := hsigma.comp hkappa
  have hmono : Monotone V := monotone_nat_of_le_succ fun j =>
    subset_closure.trans (hVnested j)
  let bound := fun n => max ((label n).1 + 1 + R (label n).1) (rho 0 / 2)
  have hbaseDist := (terminalSourceCountableMap_base_distances hrho e point
    (fun j => (j : ℝ) + 1 + R j)
    (fun k => (data k 0 (Nat.zero_le k)).zero)
    (fun k j hjk i x y => ((data k j hjk).distances i x y).2)
    (fun k j hjk => (data k j hjk).based_distances)).1
  let coord := fun k n => ChartDistance.chartParametrization Uset hU (total (nu k) n)
  have hbound (k n : ℕ) (z : E) (hz : z ∈ (charts n).target) :
      dist (point (nu k)) (coord k n z) ≤ bound n := by
    have hzU : z ∈ U n := by rwa [htarget] at hz
    let x : U n := ⟨z, hzU⟩
    change dist (point (nu k))
      (ChartDistance.chartParametrization Uset hU (total (nu k) n) x.val) ≤ bound n
    rw [ChartDistance.chartParametrization_apply]
    exact hbaseDist (nu k) (label n).1 (label n).2 x
  have happroxCoord : ∀ n C, IsCompact C → C ⊆ (charts n).target → TendstoUniformlyOn
      (fun k z => dist (f k ((charts n).symm z)) (coord k n z)) (fun _ => 0) atTop C := by
    intro n C hC hCn
    rw [hinverse n]
    exact terminalSource_regular_chart_approximation Uset hU overlap.include
      (fun k => M (nu k)) f (fun k => total (nu k)) happrox n C hC
      (by rwa [htarget] at hCn)
  have hactualJets : ∀ n m C, IsCompact C → C ⊆ (charts n).target → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m ((gSource (nu k)).pullbackCoefficients
        (f k ∘ (charts n).symm)))
      (iteratedFDeriv ℝ m (gQ.pullbackCoefficients (charts n).symm)) atTop C := by
    intro n m C hC hCn
    have hCU : C ⊆ U n := by rwa [htarget] at hCn
    have hlimit := (hfjets n m C hC hCU).congr_right
      (fun z hz => (hchartJets n m z (hCU hz)).symm)
    rw [hinverse n] at hlimit ⊢
    exact hlimit
  obtain ⟨bound0, _hbound0, hglobal⟩ := terminalSource_regular_terminal_curvature_bound
    S B p F obs W H base Q r A tau0 tau K L R rho N center data P
    gQ DQ hgQ nu hnu htau hA V hV hmono hVc hVcover hVK
    (overlap.include 0 (terminalSourceCountableZero (hrho (label 0).1))) hVp f
    (fun k => ⟨(hf k).1, (hf k).2.1⟩)
    (fun k => (hf k).2.2.trans (hbase (kappa k))) charts hchartCover
    coord bound hbound happroxCoord hactualJets hfloor hEpsilon hC hPast
    (fun n => tau (label n).1 / 4) G overlap.include hfinite
  have hstatic := terminalSource_regular_physical_scalar_ceiling
    S B p F obs W H base Q r A tau0 tau K L R rho N center data hrho
    gQ DQ nu hnu (fun n => (charts n).symm) hglobal htarget
    (fun n m C hC hCU => ((hBjets n m C hC hCU).seq_tendstoUniformlyOn
      kappa hkappa.tendsto_atTop).congr_right
        (fun z hz => (hchartJets n m z (hCU hz)).symm))
  exact ⟨nu, hnu, max 1 (3 * bound0), hstatic⟩

end Family

end PoincareConjecture.M47
