import PoincareConjecture.Proofs.M47.TerminalRegularChartFlows
import PoincareConjecture.Proofs.M47.TerminalRegularTerminalProjection
import PoincareConjecture.Proofs.M47.TerminalSourceCountableFiniteGerms

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter Metric TopologicalSpace Poincare.Gluing
open scoped Manifold ContDiff Topology NNReal

universe u

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "Bilin" => E →L[ℝ] E →L[ℝ] ℝ

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
local notation "g" => (fun k : ℕ =>
  RiemannianMetric.connectedComponentMetric (gPhysical k) (center k))
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

set_option maxHeartbeats 800000 in

theorem terminalSource_regular_finite_germs
    (P : M46Predecessors.{u}) (htau : ∀ j, 0 < tau j)
    (hrhoR : ∀ j, 2 * rho j < R j)
    (hsmall : ∀ j s, |s| ≤ 2 * rho j →
      ((13 * max (4 * L j / 3) 1) * s ^ 2) *
        Real.exp (max 1 ((13 * max (4 * L j / 3) 1) * s ^ 2)) ≤ 3)
    (hQ : Tendsto Q atTop atTop)
    {sigma : ℕ → ℕ} (hsigma : StrictMono sigma)
    (B0 : ℕ → E → Bilin) (Bminus : ℕ → ℝ × E → Bilin)
    (hB0 : ∀ n, ContDiffOn ℝ ∞ (B0 n) (U n))
    (hminus : ∀ n, ContDiffOn ℝ ∞ (Bminus n)
      (Ioo (-(tau (label n).1 / 2)) 0 ×ˢ (U n : Set E))) :
    letI : ∀ k, MetricSpace (M k) :=
      fun k => terminalSourceComponentMetricSpace (gPhysical k) (center k)
    letI : ∀ n, Nonempty (U n) := fun n => ⟨terminalSourceCountableZero (hrho (label n).1)⟩
    letI : ∀ n, ChartedSpace E (U n) :=
      fun n => (U n).isOpen.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI : ∀ n, IsManifold (𝓡 3) ∞ (U n) :=
      fun n => (U n).isOpen.isOpenEmbedding_subtypeVal.isManifold_singleton
    letI : ∀ n, LocallyCompactSpace (U n) := fun n => (U n).isOpen.locallyCompactSpace
    ∀ (_hzero : ∀ n C, IsCompact C → C ⊆ U n → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ 0 (f0 n (sigma k)))
      (iteratedFDeriv ℝ 0 (B0 n)) atTop C)
    (_hnegative : ∀ n m C, IsCompact C →
      C ⊆ Ioo (-(tau (label n).1 / 2)) 0 ×ˢ (U n : Set E) → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m (terminalSourceCountableNegative (label n).1
        (fun a => (src (label n).1 a : Type u)) (flow (label n).1)
        (fun a => chart (label n).1 a (label n).2) (f0 n) (sigma k)))
      (iteratedFDeriv ℝ m (Bminus n)) atTop C)
    (G : ∀ n, RicciFlow 3 (U n) (Icc (-(tau (label n).1 / 4)) 0))
    (_hcoeff : ∀ n t, t ∈ Icc (-(tau (label n).1 / 4)) 0 → ∀ (x : U n) v w,
      ((G n).metric t).inner x v w =
        (if t < 0 then Bminus n (t, x) else B0 n x) v w)
    (D : ∀ n n', C(U n × U n', ℝ))
    (hD : ∀ n n', TendstoLocallyUniformly
      (fun k z => dist (total (sigma k) n z.1) (total (sigma k) n' z.2)) (D n n') atTop),
    let c := fun n => terminalSourceCountableScaleFactor (rho 0) (rho (label n).1) / 2
    ∃ he : ∀ k n, LipschitzWith (3 / 2 : ℝ≥0) (total k n),
    ∃ hc : ∀ n, 0 < c n,
    ∃ hlower : ∀ k n x y, c n * dist x y ≤ dist (total k n x) (total k n y),
    ∃ ho : ∀ k n, Topology.IsOpenEmbedding (total k n),
    ∃ hconn : ∀ k (x : M k) s, IsPreconnected (ball x s),
    let hpoint := fun n n' x y =>
      (hD n n').tendstoLocallyUniformlyOn.tendsto_at (mem_univ (x, y))
    let overlap := ChartDistance.overlapSystem hpoint (fun _ => (3 / 2 : ℝ≥0))
      (fun k => he (sigma k)) c hc (fun k => hlower (sigma k))
      (fun k => ho (sigma k)) (fun k => hconn (sigma k))
    ∀ hO : SmoothOverlap Uset hU overlap,
    letI := quotientChartedSpace Uset hU overlap
    letI := quotient_isManifold Uset hU overlap hO
    ∀ (gQ : RiemannianMetric 3 (Quotient overlap.setoid))
    (_hterminal : ∀ n (x : U n) v w, B0 n x v w = gQ.inner (overlap.include n x)
      (mfderiv (𝓡 3) (𝓡 3) (overlap.include n) x v)
      (mfderiv (𝓡 3) (𝓡 3) (overlap.include n) x w))
    (V : ℕ → Set (Quotient overlap.setoid)) (hV : ∀ m, IsOpen (V m))
    (_hconnected : ∀ m, IsConnected (V m))
    (_hcompact : ∀ m, IsCompact (closure (V m)))
    (_hnested : ∀ m, closure (V m) ⊆ V (m + 1))
    (_hexhaust : (⋃ m, V m) = univ),
    TerminalSourceCountableFiniteGermsResult (fun n => tau (label n).1 / 4)
      G overlap.include gQ V hV := by
  classical
  let : ∀ k, MetricSpace (M k) :=
    fun k => terminalSourceComponentMetricSpace (gPhysical k) (center k)
  let : ∀ n, Nonempty (U n) := fun n => ⟨terminalSourceCountableZero (hrho (label n).1)⟩
  let : ∀ n, ChartedSpace E (U n) :=
    fun n => (U n).isOpen.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let : ∀ n, IsManifold (𝓡 3) ∞ (U n) :=
    fun n => (U n).isOpen.isOpenEmbedding_subtypeVal.isManifold_singleton
  let : ∀ n, LocallyCompactSpace (U n) := fun n => (U n).isOpen.locallyCompactSpace
  dsimp only
  intro hzero hnegative G hcoeff D hD
  let c := fun n => terminalSourceCountableScaleFactor (rho 0) (rho (label n).1) / 2
  let cyl := fun (j : ℕ) (a : {k : ℕ // j ≤ k}) => (data a.val j a.property).cylinder
  have hGood (j : ℕ) (i : Fin (N j + 1)) :
      ∀ᶠ a in Filter.comap (Subtype.val : {k : ℕ // j ≤ k} → ℕ) atTop,
        TerminalSourceJetsG4Good S B p (obs a.val) (H a.val) (src j a) (cyl j a) (flow j a)
          (rNext := r a.val) (L := L j) (eta := 1) (chart j a i) :=
    Filter.Eventually.of_forall (fun a => (data a.val j a.property).good i)
  have hUR (n : ℕ) : (U n : Set E) ⊆ Metric.ball 0 (R (label n).1) :=
    Metric.ball_subset_ball (by linarith [hrho (label n).1, hrhoR (label n).1])
  have hgeometry := terminalSourceCountableMap_geometry hrho e
    (fun k j hjk i => ((data k j hjk).geometry i).1)
    (fun k j hjk i => ((data k j hjk).geometry i).2)
  have hdistances := terminalSourceCountableMap_distances hrho e
    (fun k j hjk => (data k j hjk).distances)
  have he (k n : ℕ) : LipschitzWith (3 / 2 : ℝ≥0) (total k n) := by
    apply LipschitzWith.of_dist_le_mul
    exact fun x y => (hdistances.2 k (label n).1 (label n).2 x y).2
  have hc : ∀ n, 0 < c n := fun n => hdistances.1 (label n).1
  have hlower : ∀ k n x y, c n * dist x y ≤ dist (total k n x) (total k n y) :=
    fun k n x y => (hdistances.2 k (label n).1 (label n).2 x y).1
  have ho : ∀ k n, Topology.IsOpenEmbedding (total k n) :=
    fun k n => (hgeometry k (label n).1 (label n).2).1
  have hconn (k : ℕ) (x : M k) (s : ℝ) : IsPreconnected (ball x s) :=
    (terminalSourceComponent_balls (gPhysical k) (center k) x s).2.2
  have hsmooth (k n : ℕ) : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (total k n) := by
    change letI := (U n).isOpen.isOpenEmbedding_subtypeVal.singletonChartedSpace
      IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (total k n)
    rw [canonicalDomain_chartedSpace_eq_opens]
    exact (hgeometry k (label n).1 (label n).2).2
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
  let physical : ∀ k, M k → ((F k).slice (base k + 0 / Q k)).carrier :=
    fun k z => by simpa only [zero_div, add_zero] using z.val
  have hterminal (n : ℕ) (a : {k : ℕ // (label n).1 ≤ k})
      (ha : TerminalSourceJetsG4Good S B p (obs a.val) (H a.val)
        (src (label n).1 a) (cyl (label n).1 a) (flow (label n).1 a)
        (rNext := r a.val) (L := L (label n).1) (eta := 1)
        (chart (label n).1 a (label n).2)) (x : U n) :
      physical a.val (total a.val n x) =
        (H a.val).history.forward (base a.val + 0 / Q a.val)
          (ha.htime 0 ⟨neg_nonpos.mpr (htau (label n).1).le, le_rfl⟩)
          ((cyl (label n).1 a).forward 0 ⟨neg_nonpos.mpr (htau (label n).1).le, le_rfl⟩
            ((chart (label n).1 a (label n).2).chart x.val).val) := by
    dsimp only
    rw [terminalSourceCountableMap_good hrho e a.property]
    exact terminalSource_regular_terminal_projection (data a.val (label n).1 a.property)
      ⟨neg_nonpos.mpr (htau (label n).1).le, le_rfl⟩ (label n).2 x
  refine ⟨he, hc, hlower, ho, hconn, ?_⟩
  intro hO
  exact terminalSourceCountable_actual_finite_germs U total D hsigma
    (fun n n' x y => (hD n n').tendstoLocallyUniformlyOn.tendsto_at (mem_univ (x, y)))
    (fun _ => (3 / 2 : ℝ≥0)) he c hc hlower ho hconn hsmooth S B p
    (fun n => (label n).1) (fun n => tau (label n).1) (fun n => R (label n).1)
    (fun n => L (label n).1) (fun _ => 1) (fun n => htau (label n).1) hUR
    F base Q r (fun _ a => obs a.val) (fun _ a => W a.val) (fun _ a => H a.val)
    (fun _ a => (F a.val).slice (base a.val))
    (fun n => src (label n).1) (fun n => cyl (label n).1) (fun n => flow (label n).1)
    (fun n a => chart (label n).1 a (label n).2)
    (fun n => hGood (label n).1 (label n).2)
    (fun n a => (data a.val (label n).1 a.property).metric)
    physical hterminal f0 P (fun n => rho (label n).1) (fun n => hrho (label n).1)
    (fun _ => rfl) (fun n => hrhoR (label n).1) (fun n => hsmall (label n).1)
    g (fun _ _ _ _ => rfl) hread hQ B0 Bminus hB0 hminus hzero hnegative G hcoeff hO

end Family

end PoincareConjecture.M47
