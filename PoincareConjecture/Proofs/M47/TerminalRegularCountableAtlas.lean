import PoincareConjecture.Proofs.M47.TerminalRegularStageFamily
import PoincareConjecture.Proofs.M47.TerminalSourceCountableAtlas










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

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

local notation "M" => (fun k : ℕ => Poincare.connectedComponentOpens E (center k))
local notation "gPhysical" => (fun k : ℕ =>
  M13.scaleSmoothMetric (SurgeryFlowData.metric (F k) (base k)) (Q k)
    (SurgeryFlowCylinder.scale_pos (TerminalRegularStageData.original (data k 0 (Nat.zero_le k)))))
local notation "g" => (fun k : ℕ =>
  RiemannianMetric.connectedComponentMetric (gPhysical k) (center k))
local notation "e" => (fun (k j : ℕ) (hjk : j ≤ k) => TerminalRegularStageData.maps (data k j hjk))
local notation "point" => (fun k : ℕ => (Subtype.mk (center k) mem_connectedComponent : M k))
local notation "src" => (fun (j : ℕ) (a : {k : ℕ // j ≤ k}) =>
  terminalRegularStageSource (F (Subtype.val a)) (base (Subtype.val a)) (Q (Subtype.val a))
    (A j) (center (Subtype.val a)))
local notation "flow" => (fun (j : ℕ) (a : {k : ℕ // j ≤ k}) =>
  TerminalRegularStageData.flow (data (Subtype.val a) j (Subtype.property a)))
local notation "chart" => (fun (j : ℕ) (a : {k : ℕ // j ≤ k}) =>
  TerminalSourceIndexedChartCover.chart
    (TerminalRegularStageData.cover (data (Subtype.val a) j (Subtype.property a))))

private def RegularCountableAtlasOutput : Prop :=
  letI : ∀ k, MetricSpace (M k) :=
    fun k => terminalSourceComponentMetricSpace (gPhysical k) (center k)
  let label := terminalSourceCountableLabel N
  let U := fun n => terminalSourceCountableDomain (rho (label n).1)
  letI : ∀ n, Nonempty (U n) := fun n => ⟨terminalSourceCountableZero (hrho (label n).1)⟩
  let total := fun k n => terminalSourceCountableMap hrho e k (label n).1 (label n).2
  let f0 := fun n k => (g k).pullbackCoefficients
    (ChartDistance.chartParametrization (fun n => (U n : Set E)) (fun n => (U n).isOpen)
      (total k n))
  let fminus := fun n => terminalSourceCountableNegative (label n).1
    (fun a => (src (label n).1 a : Type u)) (flow (label n).1)
    (fun a => chart (label n).1 a (label n).2) (f0 n)
  ∃ sigma : ℕ → ℕ, StrictMono sigma ∧
    (∀ n, ∀ᶠ k in atTop, ∃ hjk : (label n).1 ≤ sigma k,
      total (sigma k) n = e (sigma k) (label n).1 hjk (label n).2 ∧
      fminus n (sigma k) = fun z : ℝ × E =>
        ((flow (label n).1 ⟨sigma k, hjk⟩).metric z.1).pullbackCoefficients
          (chart (label n).1 ⟨sigma k, hjk⟩ (label n).2).chart z.2) ∧
    ∃ B0 : ℕ → E → Bilin,
      (∀ n, ContDiffOn ℝ ∞ (B0 n) (U n)) ∧
      (∀ n m C, IsCompact C → C ⊆ U n → TendstoUniformlyOn
        (fun k => iteratedFDeriv ℝ m (f0 n (sigma k)))
        (iteratedFDeriv ℝ m (B0 n)) atTop C) ∧
      ∃ Bminus : ℕ → ℝ × E → Bilin,
        (∀ n, ContDiffOn ℝ ∞ (Bminus n)
          (Ioo (-(tau (label n).1 / 2)) 0 ×ˢ (U n : Set E))) ∧
        (∀ n m C, IsCompact C →
          C ⊆ Ioo (-(tau (label n).1 / 2)) 0 ×ˢ (U n : Set E) → TendstoUniformlyOn
          (fun k => iteratedFDeriv ℝ m (fminus n (sigma k)))
          (iteratedFDeriv ℝ m (Bminus n)) atTop C) ∧
        ∃ D : ∀ n n', C(U n × U n', ℝ),
        ∃ hD : ∀ n n', TendstoLocallyUniformly
          (fun k z => dist (total (sigma k) n z.1) (total (sigma k) n' z.2)) (D n n') atTop,
        let selected := fun k n => total (sigma k) n
        let c := fun n => terminalSourceCountableScaleFactor (rho 0) (rho (label n).1) / 2
        ∃ he : ∀ k n, LipschitzWith (3 / 2 : ℝ≥0) (selected k n),
        ∃ hc : ∀ n, 0 < c n,
        ∃ hlower : ∀ k n x y, c n * dist x y ≤ dist (selected k n x) (selected k n y),
        ∃ ho : ∀ k n, Topology.IsOpenEmbedding (selected k n),
        ∃ hconn : ∀ k (x : M (sigma k)) s, IsPreconnected (Metric.ball x s),
          (∀ k, selected k 0 (terminalSourceCountableZero (hrho (label 0).1)) = point (sigma k)) ∧
          TerminalSourceCountableAtlasResult (fun n => (U n : Set E)) (fun n => (U n).isOpen)
            (fun k => g (sigma k)) selected D hD (fun _ => (3 / 2 : ℝ≥0))
            he c hc hlower ho hconn B0 (terminalSourceCountableZero (hrho (label 0).1))



theorem terminalSource_regular_countable_atlas
    (P : M46Predecessors.{u}) (htau : ∀ j, 0 < tau j)
    (hrhoR : ∀ j, 2 * rho j < R j)
    (hsmall : ∀ j s, |s| ≤ 2 * rho j →
      ((13 * max (4 * L j / 3) 1) * s ^ 2) *
        Real.exp (max 1 ((13 * max (4 * L j / 3) 1) * s ^ 2)) ≤ 3) :
    RegularCountableAtlasOutput S B p F O W H base Q r A tau0 tau K L R rho N center data hrho := by
  classical
  let : ∀ k, MetricSpace (M k) :=
    fun k => terminalSourceComponentMetricSpace (gPhysical k) (center k)
  let cyl := fun (j : ℕ) (a : {k : ℕ // j ≤ k}) => (data a.val j a.property).cylinder
  have hGood (j : ℕ) (i : Fin (N j + 1)) :
      ∀ᶠ a in Filter.comap (Subtype.val : {k : ℕ // j ≤ k} → ℕ) atTop,
        TerminalSourceJetsG4Good S B p (O a.val) (H a.val) (src j a) (cyl j a) (flow j a)
          (rNext := r a.val) (L := L j) (eta := 1) (chart j a i) :=
    Filter.Eventually.of_forall (fun a => (data a.val j a.property).good i)
  have hopen := fun k j hjk i => ((data k j hjk).geometry i).1
  have hsmooth := fun k j hjk i => ((data k j hjk).geometry i).2
  have hdist := fun k j hjk => (data k j hjk).distances
  have hzero (k : ℕ) : e k 0 (Nat.zero_le k) 0 (terminalSourceCountableZero (hrho 0)) = point k :=
    (data k 0 (Nat.zero_le k)).zero
  have hbase := fun k j hjk => (data k j hjk).based_distances
  have hmetric := fun k j hjk => (data k j hjk).map_metric
  obtain ⟨sigma, hsigma, hlate, B0, hB0, hBjets, Bminus, hBminus, hNegative, D, hD⟩ :=
    terminalSourceCountable_extract_actual_charts S B p P g rho tau R L (fun _ => 1) N
      hrho htau hrhoR hsmall
      (fun _ a => F a.val) (fun _ a => O a.val) (fun _ a => W a.val) (fun _ a => H a.val)
      (fun _ a => (F a.val).slice (base a.val))
      (fun _ a => base a.val) (fun _ a => Q a.val) (fun _ a => r a.val)
      src cyl flow chart hGood e hopen hsmooth hdist point (fun j => (j : ℝ) + 1 + R j)
      hzero hbase hmetric
  have hactual (k : ℕ) (x y : M k) : edist x y = (g k).edist x y := rfl
  have hconn (k : ℕ) (x : M k) (s : ℝ) : IsPreconnected (Metric.ball x s) :=
    (terminalSourceComponent_balls (gPhysical k) (center k) x s).2.2
  have hcofinal (s : ℝ) (_hs : 0 < s) : ∃ j : ℕ, s ≤ (j : ℝ) + 1 := by
    obtain ⟨j, hj⟩ := exists_nat_gt s
    exact ⟨j, by linarith⟩
  have hcover (k j : ℕ) (hjk : j ≤ k) :
      Metric.ball (point k) ((j : ℝ) + 1) ⊆
        ⋃ i, e k j hjk i '' terminalSourceCountableCore (rho j) := by
    obtain ⟨core, _hcore, hcoreEq, hcover⟩ := (data k j hjk).cores
    have hcore : core = terminalSourceCountableCore (rho j) := Set.ext hcoreEq
    rwa [hcore] at hcover
  obtain ⟨he, hc, hlower, ho, hpoint, hatlas⟩ :=
    terminalSourceCountable_complete_atlas S B p P g hactual hconn rho tau R L (fun _ => 1) N
      hrho htau hrhoR hsmall
      (fun _ a => F a.val) (fun _ a => O a.val) (fun _ a => W a.val) (fun _ a => H a.val)
      (fun _ a => (F a.val).slice (base a.val))
      (fun _ a => base a.val) (fun _ a => Q a.val) (fun _ a => r a.val)
      src cyl flow chart hGood e hopen hsmooth hdist point hzero
      (fun j => (j : ℝ) + 1) hcofinal hcover hmetric hsigma B0 hB0 hBjets D hD
  exact ⟨sigma, hsigma, hlate, B0, hB0, hBjets, Bminus, hBminus, hNegative, D, hD,
    he, hc, hlower, ho, (fun k => hconn (sigma k)), hpoint, hatlas⟩

end Family

end PoincareConjecture.M47
