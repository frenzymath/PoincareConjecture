import PoincareConjecture.Proofs.M47.TerminalRegularCountableAtlas
import PoincareConjecture.Proofs.M47.TerminalSourceCountableChartFlow










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter TopologicalSpace Poincare.Gluing
open scoped Manifold ContDiff Topology NNReal

universe u

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "Bilin" => E →L[ℝ] E →L[ℝ] ℝ

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
  (hrho : ∀ j, 0 < rho j)

local notation "label" => terminalSourceCountableLabel N
local notation "U" => (fun n => terminalSourceCountableDomain (rho (Sigma.fst (label n))))
local notation "Uset" => (fun n => (U n : Set E))
local notation "hU" => (fun n => TopologicalSpace.Opens.isOpen (U n))
local notation "g" => (fun k : ℕ => RiemannianMetric.connectedComponentMetric
  (M13.scaleSmoothMetric (SurgeryFlowData.metric (F k) (base k)) (Q k)
    (SurgeryFlowCylinder.scale_pos (TerminalRegularStageData.original (data k 0 (Nat.zero_le k)))))
  (center k))
local notation "e" => (fun (k j : ℕ) (hjk : j ≤ k) => TerminalRegularStageData.maps (data k j hjk))
local notation "total" => (fun k n => terminalSourceCountableMap hrho e k
  (Sigma.fst (label n)) (Sigma.snd (label n)))
local notation "f0" => (fun n k => RiemannianMetric.pullbackCoefficients (g k)
  (ChartDistance.chartParametrization Uset hU (total k n)))
local notation "src" => (fun (j : ℕ) (a : {k : ℕ // j ≤ k}) =>
  terminalRegularStageSource (F (Subtype.val a)) (base (Subtype.val a)) (Q (Subtype.val a))
    (A j) (center (Subtype.val a)))
local notation "flow" => (fun (j : ℕ) (a : {k : ℕ // j ≤ k}) =>
  TerminalRegularStageData.flow (data (Subtype.val a) j (Subtype.property a)))
local notation "chart" => (fun (j : ℕ) (a : {k : ℕ // j ≤ k}) =>
  TerminalSourceIndexedChartCover.chart
    (TerminalRegularStageData.cover (data (Subtype.val a) j (Subtype.property a))))



theorem terminalSource_regular_chart_flows
    (P : M46Predecessors.{u}) (htau : ∀ j, 0 < tau j)
    (hrhoR : ∀ j, 2 * rho j < R j)
    (hsmall : ∀ j s, |s| ≤ 2 * rho j →
      ((13 * max (4 * L j / 3) 1) * s ^ 2) *
        Real.exp (max 1 ((13 * max (4 * L j / 3) 1) * s ^ 2)) ≤ 3)
    {sigma : ℕ → ℕ} (hsigma : StrictMono sigma)
    (B0 : ℕ → E → Bilin) (Bminus : ℕ → ℝ × E → Bilin)
    (hB0 : ∀ n, ContDiffOn ℝ ∞ (B0 n) (U n))
    (hminus : ∀ n, ContDiffOn ℝ ∞ (Bminus n)
      (Ioo (-(tau (label n).1 / 2)) 0 ×ˢ (U n : Set E))) :
    letI : ∀ n, Nonempty (U n) := fun n => ⟨terminalSourceCountableZero (hrho (label n).1)⟩
    letI : ∀ n, ChartedSpace E (U n) :=
      fun n => (U n).isOpen.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI : ∀ n, IsManifold (𝓡 3) ∞ (U n) :=
      fun n => (U n).isOpen.isOpenEmbedding_subtypeVal.isManifold_singleton
    ∀
    (_hzero : ∀ n C, IsCompact C → C ⊆ U n → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ 0 (f0 n (sigma k)))
      (iteratedFDeriv ℝ 0 (B0 n)) atTop C)
    (_hnegative : ∀ n m C, IsCompact C →
      C ⊆ Ioo (-(tau (label n).1 / 2)) 0 ×ˢ (U n : Set E) → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m (terminalSourceCountableNegative (label n).1
        (fun a => (src (label n).1 a : Type u)) (flow (label n).1)
        (fun a => chart (label n).1 a (label n).2) (f0 n) (sigma k)))
      (iteratedFDeriv ℝ m (Bminus n)) atTop C)
    (g0 : ∀ n, CanonicalMetric Uset hU n)
    (_hterminal : ∀ n (x : U n) v w, (g0 n).inner x v w = B0 n x v w),
    ∃ G : ∀ n, RicciFlow 3 (U n) (Icc (-(tau (label n).1 / 4)) 0),
      (∀ n, (G n).metric 0 = g0 n) ∧
      ∀ n t, t ∈ Icc (-(tau (label n).1 / 4)) 0 → ∀ (x : U n) v w,
        ((G n).metric t).inner x v w =
          (if t < 0 then Bminus n (t, x) else B0 n x) v w := by
  classical
  let : ∀ n, Nonempty (U n) := fun n => ⟨terminalSourceCountableZero (hrho (label n).1)⟩
  let : ∀ n, ChartedSpace E (U n) :=
    fun n => (U n).isOpen.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let : ∀ n, IsManifold (𝓡 3) ∞ (U n) :=
    fun n => (U n).isOpen.isOpenEmbedding_subtypeVal.isManifold_singleton
  dsimp only
  intro hzero hnegative g0 hterminal
  let cyl := fun (j : ℕ) (a : {k : ℕ // j ≤ k}) => (data a.val j a.property).cylinder
  have hGood (j : ℕ) (i : Fin (N j + 1)) :
      ∀ᶠ a in Filter.comap (Subtype.val : {k : ℕ // j ≤ k} → ℕ) atTop,
        TerminalSourceJetsG4Good S B p (O a.val) (H a.val) (src j a) (cyl j a) (flow j a)
          (rNext := r a.val) (L := L j) (eta := 1) (chart j a i) :=
    Filter.Eventually.of_forall (fun a => (data a.val j a.property).good i)
  have hUR (n : ℕ) : (U n : Set E) ⊆ Metric.ball 0 (R (label n).1) :=
    Metric.ball_subset_ball (by linarith [hrho (label n).1, hrhoR (label n).1])
  have hread (n : ℕ) (a : {k : ℕ // (label n).1 ≤ k}) :
      EqOn (f0 n a.val) (((flow (label n).1 a).metric 0).pullbackCoefficients
        (chart (label n).1 a (label n).2).chart) (U n) := by
    let : ChartedSpace E (U n) := (U n).instChartedSpace
    dsimp only
    rw [terminalSourceCountableMap_good hrho e a.property]
    exact terminalSourceCountable_pullback_readout U (g a.val)
      ((flow (label n).1 a).metric 0)
      ((data a.val (label n).1 a.property).geometry (label n).2).2.contMDiff
      (chart (label n).1 a (label n).2).chart
      ((chart (label n).1 a (label n).2).smooth.mono (hUR n))
      ((data a.val (label n).1 a.property).map_metric (label n).2)
  have hz (n : ℕ) (x : E) (hx : x ∈ U n) :
      Tendsto (fun k => f0 n (sigma k) x) atTop (𝓝 (B0 n x)) := by
    have h := (hzero n {x} isCompact_singleton (singleton_subset_iff.mpr hx)).tendsto_at
      (mem_singleton x)
    have heval := ((ContinuousMultilinearMap.uniformContinuous_eval_const
      (𝕜 := ℝ) (0 : Fin 0 → E)).continuous.tendsto _).comp h
    simpa only [Function.comp_def, iteratedFDeriv_zero_apply] using heval
  have hflow (n : ℕ) : ∃ G : RicciFlow 3 (U n) (Icc (-(tau (label n).1 / 4)) 0),
      G.metric 0 = g0 n ∧ ∀ t ∈ Icc (-(tau (label n).1 / 4)) 0, ∀ (x : U n) v w,
        (G.metric t).inner x v w =
          (if t < 0 then Bminus n (t, x) else B0 n x) v w := by
    let j := (label n).1
    let i := (label n).2
    let coeff := fun z : ℝ × E => if z.1 < 0 then Bminus n z else B0 n z.2
    have hclosed := terminalSourceCountable_g4_closed_limit j S B p P
      (htau j) (hrho j) (hrhoR j) (hsmall j)
      (fun a => F a.val) (fun a => O a.val) (fun a => W a.val) (fun a => H a.val)
      (fun a => (F a.val).slice (base a.val))
      (fun a => base a.val) (fun a => Q a.val) (fun a => r a.val)
      (src j) (cyl j) (flow j) (fun a => chart j a i) (hGood j i)
      (f0 n) (hread n) hsigma (B0 n) (Bminus n) (hB0 n) (hminus n) (hz n) (hnegative n)
    have hbound := (terminalSourceCountable_g4_closed_bounds j S B p P
      (htau j) (hrho j) (hrhoR j) (hsmall j)
      (fun a => F a.val) (fun a => O a.val) (fun a => W a.val) (fun a => H a.val)
      (fun a => (F a.val).slice (base a.val))
      (fun a => base a.val) (fun a => Q a.val) (fun a => r a.val)
      (src j) (cyl j) (flow j) (fun a => chart j a i) (hGood j i)
      (f0 n) (hread n)).1
    apply terminalSourceCountable_chart_flow U n j (fun a => (src j a : Type u))
      (htau j) (hUR n) (flow j) (fun a => chart j a i) (f0 n) hsigma
      coeff hclosed.1 hclosed.2.1 ?_ hclosed.2.2 (g0 n) ?_
    · intro t ht x hx
      refine ⟨terminalSourceLower (13 * max (4 * L j / 3) 1) (tau j),
        terminalSourceLower_pos _ _, ?_⟩
      filter_upwards [hsigma.tendsto_atTop.eventually hbound] with k hk v
      exact hk t ⟨by linarith [htau j, ht.1], ht.2⟩ x hx v
    · intro x v w
      simpa only [coeff, lt_self_iff_false, if_false] using hterminal n x v w
  choose G hG hcoeff using hflow
  exact ⟨G, hG, hcoeff⟩

end Family

end PoincareConjecture.M47
