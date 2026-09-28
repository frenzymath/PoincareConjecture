import PoincareConjecture.Proofs.M47.TerminalSourceCountableExtraction
import PoincareConjecture.Proofs.M47.TerminalSourceCountableClosedBounds
import PoincareConjecture.Proofs.M47.TerminalSourceCountableCoreCover
import PoincareConjecture.Proofs.M47.TerminalGermsTerminalGeometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter Metric TopologicalSpace Poincare.Gluing Poincare.Analysis.Calculus
open scoped Manifold ContDiff Bundle Topology NNReal ENNReal

universe u

namespace PoincareConjecture.M47

open ChartDistance

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "V" => E →L[ℝ] E →L[ℝ] ℝ

private theorem locallyCompact_t3 (X : Type*) [TopologicalSpace X]
    [T2Space X] [LocallyCompactSpace X] : T3Space X := inferInstance

def TerminalSourceCountableAtlasResult
    (U : ℕ → Set E) (hU : ∀ n, IsOpen (U n)) [∀ n, Nonempty (Piece U n)]
    {M : ℕ → Type u} [∀ k, MetricSpace (M k)] [∀ k, ChartedSpace E (M k)]
    [∀ k, IsManifold (𝓡 3) ∞ (M k)]
    (g : ∀ k, RiemannianMetric 3 (M k)) (e : ∀ k n, Piece U n → M k)
    (D : ∀ n n', C(Piece U n × Piece U n', ℝ))
    (hD : ∀ n n', TendstoLocallyUniformly
      (fun k (z : Piece U n × Piece U n') => dist (e k n z.1) (e k n' z.2)) (D n n') atTop)
    (L : ℕ → ℝ≥0) (he : ∀ k n, LipschitzWith (L n) (e k n))
    (c : ℕ → ℝ) (hc : ∀ n, 0 < c n)
    (hlower : ∀ k n x y, c n * dist x y ≤ dist (e k n x) (e k n y))
    (ho : ∀ k n, Topology.IsOpenEmbedding (e k n))
    (hconn : ∀ k (x : M k) r, IsPreconnected (ball x r))
    (B0 : ℕ → E → V) (p0 : Piece U 0) : Prop :=
  letI : ∀ n, ChartedSpace E (Piece U n) :=
    fun n => (hU n).isOpenEmbedding_subtypeVal.singletonChartedSpace
  letI : ∀ n, IsManifold (𝓡 3) ∞ (Piece U n) :=
    fun n => (hU n).isOpenEmbedding_subtypeVal.isManifold_singleton
  letI : ∀ n, LocallyCompactSpace (Piece U n) := fun n => (hU n).locallyCompactSpace
  let hpoint := fun n n' x y =>
    (hD n n').tendstoLocallyUniformlyOn.tendsto_at (mem_univ (x, y))
  let O := overlapSystem hpoint L he c hc hlower ho hconn
  T2Space (Quotient O.setoid) ∧ SecondCountableTopology (Quotient O.setoid) ∧
    ∃ hO : SmoothOverlap U hU O,
    ∃ g0 : ∀ n, CanonicalMetric U hU n,
    ∃ _hcompat : CompatibleMetrics U hU O g0,
      (∀ n (x : Piece U n) v w, (g0 n).inner x v w = B0 n x v w) ∧
      ConnectedSpace (Quotient O.setoid) ∧
      letI : T2Space (Quotient O.setoid) := O.quotient_t2Space
        (overlapSystem_closed hpoint L he c hc hlower ho hconn)
      letI := quotientChartedSpace U hU O
      letI := quotient_isManifold U hU O hO
      letI : LocallyCompactSpace (Quotient O.setoid) := ChartedSpace.locallyCompactSpace E _
      letI : T3Space (Quotient O.setoid) := locallyCompact_t3 _
      ∃ gQ : RiemannianMetric 3 (Quotient O.setoid), MetricComplete gQ ∧
        (∀ n (x : Piece U n) (v w : TangentSpace (𝓡 3) x),
          (g0 n).inner x v w = gQ.inner (O.include n x)
            (mfderiv (𝓡 3) (𝓡 3) (O.include n) x v)
            (mfderiv (𝓡 3) (𝓡 3) (O.include n) x w)) ∧
        ∃ X : ℕ → Set (Quotient O.setoid),
          (∀ m, IsOpen (X m)) ∧ (∀ m, IsConnected (X m)) ∧
          (∀ m, O.include 0 p0 ∈ X m) ∧ (∀ m, IsCompact (closure (X m))) ∧
          (∀ m, closure (X m) ⊆ X (m + 1)) ∧ (⋃ m, X m) = univ ∧
        ∃ kappa : ℕ → ℕ, StrictMono kappa ∧
        ∃ f : ∀ k, Quotient O.setoid → M (kappa k),
          (∀ k, Topology.IsOpenEmbedding (fun x : X k => f k x) ∧
            IsLocalDiffeomorphOn (𝓡 3) (𝓡 3) ∞ (f k) (X k) ∧
            f k (O.include 0 p0) = e (kappa k) 0 p0) ∧
          (∀ n K, IsCompact K → TendstoUniformlyOn
            (fun k (x : Piece U n) => dist (f k (O.include n x)) (e (kappa k) n x))
            (fun _ => 0) atTop K) ∧
          (∀ n m K, IsCompact K → K ⊆ U n → TendstoUniformlyOn
            (fun k => iteratedFDeriv ℝ m ((g (kappa k)).pullbackCoefficients
              (chartParametrization U hU (f k ∘ O.include n))))
            (iteratedFDeriv ℝ m (B0 n)) atTop K) ∧
          ∀ r : ℝ, 0 < r → ∃ m, ∀ᶠ k in atTop, ∀ x ∈ frontier (X m),
            ENNReal.ofReal r ≤ (g (kappa k)).edist (f k (O.include 0 p0)) (f k x)

theorem terminalSourceCountable_complete_atlas
    (S : RepairedControlledSchedulesData.{u})
    (B : M47ComponentAnalyticBounds.{u} S.setup.C)
    (p : SurgeryParameterPrefix S.constants) (P : M46Predecessors.{u})
    {M : ℕ → Type u} [∀ k, MetricSpace (M k)] [∀ k, ChartedSpace E (M k)]
    [∀ k, IsManifold (𝓡 3) ∞ (M k)]
    (g : ∀ k, RiemannianMetric 3 (M k))
    (hactual : ∀ k (x y : M k), edist x y = (g k).edist x y)
    (hconn : ∀ k (x : M k) r, IsPreconnected (ball x r))
    (rho tau R L eta : ℕ → ℝ) (N : ℕ → ℕ)
    (hrho : ∀ j, 0 < rho j) (htau : ∀ j, 0 < tau j)
    (hrhoR : ∀ j, 2 * rho j < R j)
    (hsmall : ∀ j, ∀ s : ℝ, |s| ≤ 2 * rho j →
      ((13 * max (4 * L j / 3) 1) * s ^ 2) *
        Real.exp (max 1 ((13 * max (4 * L j / 3) 1) * s ^ 2)) ≤ 3)
    (F0 : ∀ j, {k : ℕ // j ≤ k} → SurgeryFlowData.{u})
    (obs : ∀ j a, SurgeryObservation (F0 j a))
    (W : ∀ j a, M33RegularHistoryWindow (F0 j a))
    (H : ∀ j a, M33RegularHistoryData (W j a))
    (C0 : ∀ j, {k : ℕ // j ≤ k} → GeneralizedSliceCarrier.{u})
    (base Q rNext : ∀ j, {k : ℕ // j ≤ k} → ℝ)
    (source : ∀ j a, Opens (C0 j a).carrier)
    (cyl : ∀ j a, GeneralizedFlowCylinder (H j a).generalized (C0 j a)
      (base j a) (Q j a) (Icc (-tau j) 0) (source j a : Set (C0 j a).carrier))
    (F : ∀ j a, RicciFlow 3 (source j a) (Icc (-tau j) 0))
    (C : ∀ j a, Fin (N j + 1) → TerminalSourceChart ((F j a).metric 0) (R j))
    (hGood : ∀ j i, ∀ᶠ a in Filter.comap
        (Subtype.val : {k : ℕ // j ≤ k} → ℕ) atTop,
      TerminalSourceJetsG4Good S B p (obs j a) (H j a) (source j a) (cyl j a) (F j a)
        (τ := tau j) (base := base j a) (Q := Q j a) (rNext := rNext j a)
        (R := R j) (L := L j) (eta := eta j) (C j a i))
    (e : ∀ k j, j ≤ k → Fin (N j + 1) → terminalSourceCountableDomain (rho j) → M k)
    (hopen : ∀ k j hjk i, Topology.IsOpenEmbedding (e k j hjk i))
    (hsmooth : ∀ k j hjk i, IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (e k j hjk i))
    (hdist : ∀ k j hjk i x y,
      (1 / 2 : ℝ) * dist x y ≤ dist (e k j hjk i x) (e k j hjk i y) ∧
        dist (e k j hjk i x) (e k j hjk i y) ≤ (3 / 2 : ℝ) * dist x y)
    (point : ∀ k, M k)
    (hzero : ∀ k, e k 0 (Nat.zero_le k) 0 (terminalSourceCountableZero (hrho 0)) = point k)
    (A : ℕ → ℝ) (hA : ∀ r : ℝ, 0 < r → ∃ j, r ≤ A j)
    (hcover : ∀ k j hjk,
      ball (point k) (A j) ⊆ ⋃ i, e k j hjk i '' terminalSourceCountableCore (rho j))
    (hmetric : ∀ k j hjk i (x : terminalSourceCountableDomain (rho j))
      (v w : TangentSpace (𝓡 3) x),
      (g k).inner (e k j hjk i x)
        (mfderiv (𝓡 3) (𝓡 3) (e k j hjk i) x v)
        (mfderiv (𝓡 3) (𝓡 3) (e k j hjk i) x w) =
      ((F j ⟨k, hjk⟩).metric 0).inner ((C j ⟨k, hjk⟩ i).chart x.val)
        (mfderiv (𝓡 3) (𝓡 3)
          (fun y : terminalSourceCountableDomain (rho j) =>
            (C j ⟨k, hjk⟩ i).chart y.val) x v)
        (mfderiv (𝓡 3) (𝓡 3)
          (fun y : terminalSourceCountableDomain (rho j) =>
            (C j ⟨k, hjk⟩ i).chart y.val) x w))
    {sigma : ℕ → ℕ} (hsigma : StrictMono sigma)
    (B0 : ℕ → E → V)
    (hBsmooth : ∀ n, ContDiffOn ℝ ∞ (B0 n)
      (terminalSourceCountableDomain (rho (terminalSourceCountableLabel N n).1)))
    (hBjets :
      let label := terminalSourceCountableLabel N
      let U := fun n => terminalSourceCountableDomain (rho (label n).1)
      letI : ∀ n, Nonempty (U n) := fun n => ⟨terminalSourceCountableZero (hrho (label n).1)⟩
      ∀ n m K, IsCompact K → K ⊆ U n → TendstoUniformlyOn
        (fun k => iteratedFDeriv ℝ m ((g (sigma k)).pullbackCoefficients
          (chartParametrization (fun n => (U n : Set E)) (fun n => (U n).isOpen)
            (terminalSourceCountableMap hrho e (sigma k) (label n).1 (label n).2))))
        (iteratedFDeriv ℝ m (B0 n)) atTop K)
    (D : ∀ n n', C(terminalSourceCountableDomain (rho (terminalSourceCountableLabel N n).1) ×
      terminalSourceCountableDomain (rho (terminalSourceCountableLabel N n').1), ℝ))
    (hD : ∀ n n', TendstoLocallyUniformly
      (fun k z => dist
        (terminalSourceCountableMap hrho e (sigma k) (terminalSourceCountableLabel N n).1
          (terminalSourceCountableLabel N n).2 z.1)
        (terminalSourceCountableMap hrho e (sigma k) (terminalSourceCountableLabel N n').1
          (terminalSourceCountableLabel N n').2 z.2)) (D n n') atTop) :
    let label := terminalSourceCountableLabel N
    let U := fun n => terminalSourceCountableDomain (rho (label n).1)
    letI : ∀ n, Nonempty (U n) := fun n => ⟨terminalSourceCountableZero (hrho (label n).1)⟩
    let Uset := fun n => (U n : Set E)
    let hU := fun n => (U n).isOpen
    let total := fun k n => terminalSourceCountableMap hrho e (sigma k) (label n).1 (label n).2
    let c := fun n => terminalSourceCountableScaleFactor (rho 0) (rho (label n).1) / 2
    ∃ he : ∀ k n, LipschitzWith (3 / 2 : ℝ≥0) (total k n),
      ∃ hc : ∀ n, 0 < c n,
      ∃ hlower : ∀ k n x y, c n * dist x y ≤ dist (total k n x) (total k n y),
      ∃ ho : ∀ k n, Topology.IsOpenEmbedding (total k n),
        (∀ k, total k 0 (terminalSourceCountableZero (hrho (label 0).1)) = point (sigma k)) ∧
        TerminalSourceCountableAtlasResult Uset hU (fun k => g (sigma k)) total D hD
          (fun _ => (3 / 2 : ℝ≥0)) he c hc hlower ho (fun k => hconn (sigma k)) B0
          (terminalSourceCountableZero (hrho (label 0).1)) := by
  classical
  let label := terminalSourceCountableLabel N
  let U := fun n => terminalSourceCountableDomain (rho (label n).1)
  let : ∀ n, Nonempty (U n) := fun n => ⟨terminalSourceCountableZero (hrho (label n).1)⟩
  let Uset := fun n => (U n : Set E)
  let hU := fun n => (U n).isOpen
  let original := fun k n => terminalSourceCountableMap hrho e k (label n).1 (label n).2
  let total := fun k n => original (sigma k) n
  let f0 := fun n k => (g k).pullbackCoefficients
    (chartParametrization Uset hU (original k n))
  have hgeometry := terminalSourceCountableMap_geometry hrho e hopen hsmooth
  have hdistances := terminalSourceCountableMap_distances hrho e hdist
  have hUR (n : ℕ) : (U n : Set E) ⊆ ball 0 (R (label n).1) :=
    ball_subset_ball (by linarith [hrho (label n).1, hrhoR (label n).1])
  have hread (n : ℕ) (a : {k : ℕ // (label n).1 ≤ k}) :
      EqOn (f0 n a.val) (((F (label n).1 a).metric 0).pullbackCoefficients
        (C (label n).1 a (label n).2).chart) (U n) := by
    dsimp only [f0, original]
    rw [terminalSourceCountableMap_good hrho e a.property]
    exact terminalSourceCountable_pullback_readout U (g a.val)
      ((F (label n).1 a).metric 0)
      (hsmooth a.val (label n).1 a.property (label n).2).contMDiff
      (C (label n).1 a (label n).2).chart
      ((C (label n).1 a (label n).2).smooth.mono (hUR n))
      (hmetric a.val (label n).1 a.property (label n).2)
  have hjets (n : ℕ) : LocallyEventuallyBoundedDerivatives (U n)
      (fun k => f0 n (sigma k)) := by
    intro K _hK hKU m
    obtain ⟨d, _hd, hbound⟩ := (terminalSourceCountable_g4_jet_bounds (label n).1 S B p P
      (htau (label n).1) (hrho (label n).1) (hrhoR (label n).1) (hsmall (label n).1)
      (F0 (label n).1) (obs (label n).1) (W (label n).1) (H (label n).1)
      (C0 (label n).1) (base (label n).1) (Q (label n).1) (rNext (label n).1)
      (source (label n).1) (cyl (label n).1) (F (label n).1)
      (fun a => C (label n).1 a (label n).2) (hGood (label n).1 (label n).2)
      (f0 n) (hread n)).1 m
    exact ⟨d, hsigma.tendsto_atTop.eventually
      (hbound.mono fun k hk x hx => hk x (hKU hx))⟩
  have helliptic : ∀ n K, IsCompact K → K ⊆ U n →
      ∃ a : ℝ, 0 < a ∧ ∀ᶠ k in atTop, ∀ x ∈ K, ∀ v,
        a * ‖v‖ ^ 2 ≤ f0 n (sigma k) x v v := by
    intro n K _hK hKU
    have hbound := (terminalSourceCountable_g4_closed_bounds (label n).1 S B p P
      (htau (label n).1) (hrho (label n).1) (hrhoR (label n).1) (hsmall (label n).1)
      (F0 (label n).1) (obs (label n).1) (W (label n).1) (H (label n).1)
      (C0 (label n).1) (base (label n).1) (Q (label n).1) (rNext (label n).1)
      (source (label n).1) (cyl (label n).1) (F (label n).1)
      (fun a => C (label n).1 a (label n).2) (hGood (label n).1 (label n).2)
      (f0 n) (hread n)).1
    refine ⟨terminalSourceLower (13 * max (4 * L (label n).1 / 3) 1) (tau (label n).1),
      terminalSourceLower_pos _ _, ?_⟩
    filter_upwards [hsigma.tendsto_atTop.eventually hbound] with k hk x hx v
    have hb := hk 0 ⟨by linarith [htau (label n).1], le_rfl⟩ x (hKU hx) v
    have hz := terminalSourceCountableNegative_zero (label n).1
      (fun a => (source (label n).1 a : Type u)) (F (label n).1)
      (fun a => C (label n).1 a (label n).2) (U n) (f0 n) (hread n)
      (sigma k) (hKU hx)
    dsimp only at hz
    rw [hz] at hb
    exact hb
  have hLip (k n : ℕ) : LipschitzWith (3 / 2 : ℝ≥0) (total k n) := by
    apply LipschitzWith.of_dist_le_mul
    exact fun x y => (hdistances.2 (sigma k) (label n).1 (label n).2 x y).2
  let c := fun n => terminalSourceCountableScaleFactor (rho 0) (rho (label n).1) / 2
  have hc : ∀ n, 0 < c n := fun n => hdistances.1 (label n).1
  have hlower : ∀ k n x y, c n * dist x y ≤ dist (total k n x) (total k n y) :=
    fun k n x y => (hdistances.2 (sigma k) (label n).1 (label n).2 x y).1
  have ho : ∀ k n, Topology.IsOpenEmbedding (total k n) :=
    fun k n => (hgeometry (sigma k) (label n).1 (label n).2).1
  have hsCanonical :
      letI : ∀ n, ChartedSpace E (U n) :=
        fun n => (hU n).isOpenEmbedding_subtypeVal.singletonChartedSpace
      ∀ k n, IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (total k n) := by
    intro k n
    change letI := (U n).isOpen.isOpenEmbedding_subtypeVal.singletonChartedSpace
      IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (fun x : U n => total k n x)
    rw [canonicalDomain_chartedSpace_eq_opens]
    exact (hgeometry (sigma k) (label n).1 (label n).2).2
  have hcores := terminalSourceCountable_core_covers hrho e point hzero A hA hcover
  let p0 : U 0 := terminalSourceCountableZero (hrho (label 0).1)
  have hcover' : ∀ r : ℝ, 0 < r → ∃ s : Finset ℕ, ∃ K : ∀ n, Set (U n),
      (∀ n ∈ s, IsCompact (K n)) ∧
        ∀ᶠ k in atTop, ball (total k 0 p0) r ⊆ ⋃ n ∈ s, total k n '' K n := by
    intro r hr
    obtain ⟨s, K, _hKeq, hK, hball⟩ := hcores.2 r hr
    refine ⟨s, K, hK, ?_⟩
    filter_upwards [hsigma.tendsto_atTop.eventually hball] with k hk
    have hz : total k 0 p0 = point (sigma k) := hcores.1 (sigma k)
    rw [hz]
    exact hk
  let : ∀ n, ChartedSpace E (U n) :=
    fun n => (hU n).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let : ∀ n, IsManifold (𝓡 3) ∞ (U n) :=
    fun n => (hU n).isOpenEmbedding_subtypeVal.isManifold_singleton
  let : ∀ n, LocallyCompactSpace (U n) := fun n => (hU n).locallyCompactSpace
  let hpoint := fun n n' x y =>
    (hD n n').tendstoLocallyUniformlyOn.tendsto_at (mem_univ (x, y))
  let O := overlapSystem hpoint (fun _ => (3 / 2 : ℝ≥0)) hLip c hc hlower ho
    (fun k => hconn (sigma k))
  have hBlocal := fun n =>
    CoordinateTransition.locallyUniformly_of_tendsto_zeroJet (hU n) (hBjets n 0)
  obtain ⟨hT2, hSecond, hO, g0, hcompat, hcoeff, _hreadout⟩ :=
    terminalGerms_terminal_atlas Uset hU hpoint (fun _ => (3 / 2 : ℝ≥0)) hLip c hc
      hlower ho (fun k => hconn (sigma k)) hsCanonical (fun k => g (sigma k))
      hjets helliptic B0 hBlocal hBsmooth
  obtain ⟨hO', hconnected, gQ, hcomplete, hmetricQ, X, hX, hXc, hXp, hXK,
      hXnested, hXcover, kappa, hkappa, f, hf, happrox, hfjets, hescape⟩ :=
    terminalGerms_complete_terminal_geometry Uset hU (fun k => g (sigma k))
      (fun k => hactual (sigma k)) hD (fun _ => (3 / 2 : ℝ≥0)) hLip c hc hlower ho
      (fun k => hconn (sigma k)) hsCanonical hjets helliptic p0 hcover'
      B0 hBsmooth hBjets
  refine ⟨hLip, hc, hlower, ho, fun k => hcores.1 (sigma k), hT2, hSecond, hO, g0, hcompat, hcoeff,
    hconnected, gQ, hcomplete, ?_, X, hX, hXc, hXp, hXK, hXnested, hXcover,
    kappa, hkappa, f, hf, happrox, hfjets, hescape⟩
  intro n x v w
  exact (hcoeff n x v w).trans (hmetricQ n x v w)

end PoincareConjecture.M47
