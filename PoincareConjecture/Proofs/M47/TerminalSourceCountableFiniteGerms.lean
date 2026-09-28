import PoincareConjecture.Proofs.M47.TerminalSourceCountableCompatibility
import PoincareConjecture.Proofs.M47.TerminalSourceCountableOperator
import PoincareConjecture.Proofs.M47.TerminalGermsExhaustionOperator
import PoincareConjecture.Proofs.M47.TerminalSourceNormalHistory

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter Metric TopologicalSpace Poincare.Gluing Poincare.Analysis.Calculus
open scoped Manifold ContDiff Bundle Topology NNReal

universe u v

namespace PoincareConjecture.M47

open ChartDistance

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "V" => E →L[ℝ] E →L[ℝ] ℝ

def TerminalSourceCountableFiniteGermsResult
    {P : ℕ → Type*} {X : Type*} [∀ n, TopologicalSpace (P n)] [TopologicalSpace X]
    [∀ n, ChartedSpace E (P n)] [ChartedSpace E X]
    [∀ n, IsManifold (𝓡 3) ∞ (P n)] [IsManifold (𝓡 3) ∞ X]
    (tau : ℕ → ℝ) (G : ∀ n, RicciFlow 3 (P n) (Icc (-tau n) 0))
    (q : ∀ n, P n → X) (gX : RiemannianMetric 3 X)
    (K : ℕ → Set X) (hK : ∀ m, IsOpen (K m)) : Prop :=
  let domains : ℕ → Opens X := fun m => ⟨K m, hK m⟩
  ∃ (s : ℕ → Finset ℕ) (delta : ℕ → ℝ),
    (∀ m, (s m).Nonempty) ∧
    (∀ m, closure (K m) ⊆ ⋃ n ∈ s m, range (q n)) ∧
    (∀ m, 0 < delta m) ∧ (∀ m n, n ∈ s m → delta m < tau n) ∧
    ∃ F : ∀ m, RicciFlow 3 (domains m) (Icc (-delta m) 0),
      (∀ m (y : domains m) (v w : TangentSpace (𝓡 3) y),
        ((F m).metric 0).inner y v w = gX.inner y.val v w) ∧
      (∀ m t, t ∈ Icc (-delta m) 0 → ∀ n, t ∈ Icc (-tau n) 0 →
        ∀ (x : P n) (hx : q n x ∈ domains m) (v w : TangentSpace (𝓡 3) x),
          ((G n).metric t).inner x v w = ((F m).metric t).inner ⟨q n x, hx⟩
            (mfderiv (𝓡 3) (𝓡 3) (q n) x v)
            (mfderiv (𝓡 3) (𝓡 3) (q n) x w)) ∧
      (∀ m l t, t ∈ Icc (-delta m) 0 → t ∈ Icc (-delta l) 0 →
        ∀ (y : X) (hym : y ∈ domains m) (hyl : y ∈ domains l) (v w : E),
          ((F m).metric t).inner ⟨y, hym⟩ v w = ((F l).metric t).inner ⟨y, hyl⟩ v w) ∧
      (∀ x y z : X, ∃ m, x ∈ domains m ∧ y ∈ domains m ∧ z ∈ domains m) ∧
      (∀ m t, t ∈ Icc (-delta m) 0 → ∀ y,
        ((F m).connection t).NonnegativeCurvatureOperator y) ∧
      ∀ D : LeviCivitaData gX, ∀ x, D.NonnegativeCurvatureOperator x

section ActualSources

variable (U : ℕ → Opens E) [∀ n, Nonempty (U n)]

local notation "Uset" => (fun n => (U n : Set E))
local notation "hU" => (fun n => TopologicalSpace.Opens.isOpen (U n))

noncomputable local instance finiteChartSpace (n : ℕ) : ChartedSpace E (U n) :=
  (U n).isOpen.isOpenEmbedding_subtypeVal.singletonChartedSpace

noncomputable local instance finiteChartManifold (n : ℕ) : IsManifold (𝓡 3) ∞ (U n) :=
  (U n).isOpen.isOpenEmbedding_subtypeVal.isManifold_singleton

local instance finiteChartsLocallyCompact : ∀ n, LocallyCompactSpace (Piece Uset n) :=
  fun n => (U n).isOpen.locallyCompactSpace

local instance finiteOpensLocallyCompact : ∀ n, LocallyCompactSpace (U n) :=
  fun n => (U n).isOpen.locallyCompactSpace

variable
    {M : ℕ → Type v} [∀ k, MetricSpace (M k)] [∀ k, ChartedSpace E (M k)]
    [∀ k, IsManifold (𝓡 3) ∞ (M k)]
    (maps : ∀ k n, U n → M k)
    (D : ∀ n n', C(U n × U n', ℝ))
    {sigma : ℕ → ℕ} (hsigma : StrictMono sigma)
    (hD : ∀ n n' x y,
      Tendsto (fun k => dist (maps (sigma k) n x) (maps (sigma k) n' y)) atTop
        (𝓝 (D n n' (x, y))))
    (Lip : ℕ → ℝ≥0) (he : ∀ k n, LipschitzWith (Lip n) (maps k n))
    (c : ℕ → ℝ) (hc : ∀ n, 0 < c n)
    (hlower : ∀ k n x y, c n * dist x y ≤ dist (maps k n x) (maps k n y))
    (hopen : ∀ k n, Topology.IsOpenEmbedding (maps k n))
    (hconn : ∀ k (x : M k) r, IsPreconnected (ball x r))
    (hsmooth : ∀ k n, IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (maps k n))
    (S : RepairedControlledSchedulesData.{u})
    (B : M47ComponentAnalyticBounds.{u} S.setup.C)
    (p : SurgeryParameterPrefix S.constants)
    (stage : ℕ → ℕ) (tau R L eta : ℕ → ℝ) (htau : ∀ n, 0 < tau n)
    (hUR : ∀ n, (U n : Set E) ⊆ ball 0 (R n))
    (raw : ℕ → SurgeryFlowData.{u}) (base Q rNext : ℕ → ℝ)
    (obs : ∀ n (a : {k : ℕ // stage n ≤ k}), SurgeryObservation (raw a.val))
    (W : ∀ n (a : {k : ℕ // stage n ≤ k}), M33RegularHistoryWindow (raw a.val))
    (H : ∀ n a, M33RegularHistoryData (W n a))
    (C0 : ∀ n, {k : ℕ // stage n ≤ k} → GeneralizedSliceCarrier.{u})
    (source : ∀ n a, Opens (C0 n a).carrier)
    (cyl : ∀ n a, GeneralizedFlowCylinder (H n a).generalized (C0 n a)
      (base a.val) (Q a.val) (Icc (-tau n) 0) (source n a))
    (F : ∀ n a, RicciFlow 3 (source n a) (Icc (-tau n) 0))
    (C : ∀ n a, TerminalSourceChart ((F n a).metric 0) (R n))
    (hGood : ∀ n, ∀ᶠ a in Filter.comap
        (Subtype.val : {k : ℕ // stage n ≤ k} → ℕ) atTop,
      TerminalSourceJetsG4Good S B p (obs n a) (H n a) (source n a) (cyl n a) (F n a)
        (L := L n) (eta := eta n) (rNext := rNext a.val) (C n a))
    (hmetric : ∀ n a s (hs : s ∈ Icc (-tau n) 0) (x : source n a),
      ∀ v w : TangentSpace (𝓡 3) x,
        ((F n a).metric s).inner x v w = (cyl n a).pullbackInner s hs x.val
          (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : source n a → (C0 n a).carrier) x v)
          (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : source n a → (C0 n a).carrier) x w))
    (physical : ∀ k, M k → ((raw k).slice (base k + 0 / Q k)).carrier)
    (hterminal : ∀ n a
        (ha : TerminalSourceJetsG4Good S B p (obs n a) (H n a) (source n a)
          (cyl n a) (F n a) (L := L n) (eta := eta n) (rNext := rNext a.val) (C n a))
        (x : U n),
      physical a.val (maps a.val n x) =
        (H n a).history.forward (base a.val + 0 / Q a.val)
          (ha.htime 0 ⟨neg_nonpos.mpr (htau n).le, le_rfl⟩)
          ((cyl n a).forward 0 ⟨neg_nonpos.mpr (htau n).le, le_rfl⟩
            ((C n a).chart x.val).val))
    (f0 : ℕ → ℕ → E → V)

include hsigma hD he hc hlower hopen hconn hsmooth htau hUR hGood hmetric hterminal in

theorem terminalSourceCountable_actual_source_identity
    (i j : ℕ) {s : ℝ} (hsi : s ∈ Icc (-(tau i / 4)) 0)
    (hsj : s ∈ Icc (-(tau j / 4)) 0) :
    ∀ x ∈ Subtype.val '' overlap (fun n n' => D n n') i j,
      ∀ᶠ k in atTop, ∀ v w,
        let T := coordinateRepresentative Uset hU
          (fun y => Function.invFun (maps (sigma k) j) (maps (sigma k) i y))
        terminalSourceCountableNegative (stage j) (fun a => (source j a : Type u))
          (F j) (C j) (f0 j) (sigma k) (s, T x) (fderiv ℝ T x v) (fderiv ℝ T x w) =
        terminalSourceCountableNegative (stage i) (fun a => (source i a : Type u))
          (F i) (C i) (f0 i) (sigma k) (s, x) v w := by
  have hgood (n : ℕ) : ∀ᶠ k in atTop,
      stage n ≤ sigma k ∧ ∀ a : {l : ℕ // stage n ≤ l}, a.val = sigma k →
        TerminalSourceJetsG4Good S B p (obs n a) (H n a) (source n a)
          (cyl n a) (F n a) (L := L n) (eta := eta n) (rNext := rNext a.val) (C n a) := by
    filter_upwards [hsigma.tendsto_atTop.eventually (eventually_ge_atTop (stage n)),
      hsigma.tendsto_atTop.eventually (Filter.eventually_comap.mp (hGood n))]
      with k hk hg
    exact ⟨hk, hg⟩
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((hgood i).and (hgood j))
  let ai := fun k => (⟨sigma (k + N), (hN (k + N) (Nat.le_add_left N k)).1.1⟩ :
    {l : ℕ // stage i ≤ l})
  let aj := fun k => (⟨sigma (k + N), (hN (k + N) (Nat.le_add_left N k)).2.1⟩ :
    {l : ℕ // stage j ≤ l})
  have hgi (k : ℕ) := (hN (k + N) (Nat.le_add_left N k)).1.2 (ai k) rfl
  have hgj (k : ℕ) := (hN (k + N) (Nat.le_add_left N k)).2.2 (aj k) rfl
  let ei := fun k => terminalSourceNormal_historyCylinder (H i (ai k))
    (source i (ai k)) (hgi k).htime (cyl i (ai k))
  let ej := fun k => terminalSourceNormal_historyCylinder (H j (aj k))
    (source j (aj k)) (hgj k).htime (cyl j (aj k))
  have hmi (k : ℕ) := terminalSourceNormal_historyCylinder_maps
    (H i (ai k)) (source i (ai k)) (hgi k).htime (cyl i (ai k))
  have hmj (k : ℕ) := terminalSourceNormal_historyCylinder_maps
    (H j (aj k)) (source j (aj k)) (hgj k).htime (cyl j (aj k))
  have hsi' : s ∈ Icc (-tau i) 0 := ⟨by linarith [htau i, hsi.1], hsi.2⟩
  have hsj' : s ∈ Icc (-tau j) 0 := ⟨by linarith [htau j, hsj.1], hsj.2⟩
  have htail := terminalSourceCountable_source_overlap Uset hU
    (fun k n => maps (sigma (k + N)) n) D
    (fun n n' x y => (hD n n' x y).comp (tendsto_add_atTop_nat N))
    Lip (fun k => he (sigma (k + N))) c hc
    (fun k => hlower (sigma (k + N))) (fun k => hopen (sigma (k + N)))
    (fun k => hconn (sigma (k + N))) (fun k => hsmooth (sigma (k + N))) i j
    (fun k => raw (sigma (k + N))) (fun k => base (sigma (k + N)))
    (fun k => Q (sigma (k + N))) (fun k => C0 i (ai k)) (fun k => C0 j (aj k))
    (fun k => source i (ai k)) (fun k => source j (aj k)) (htau i) (htau j)
    hsi' hsj' ei ej (fun k => (F i (ai k)).metric s) (fun k => (F j (aj k)).metric s)
    (fun k x v w => (hmetric i (ai k) s hsi' x v w).trans
      ((hmi k).2 s hsi' x.val x.property _ _).symm)
    (fun k x v w => (hmetric j (aj k) s hsj' x v w).trans
      ((hmj k).2 s hsj' x.val x.property _ _).symm)
    (fun k => (C i (ai k)).chart) (fun k => (C j (aj k)).chart)
    (fun k => (C i (ai k)).smooth.mono (hUR i))
    (fun k => (C j (aj k)).smooth.mono (hUR j))
    (fun k => physical (sigma (k + N)))
    (fun k x => (hterminal i (ai k) (hgi k) x).trans
      (congrFun ((hmi k).1 0 ⟨neg_nonpos.mpr (htau i).le, le_rfl⟩)
        ((C i (ai k)).chart x.val)).symm)
    (fun k x => (hterminal j (aj k) (hgj k) x).trans
      (congrFun ((hmj k).1 0 ⟨neg_nonpos.mpr (htau j).le, le_rfl⟩)
        ((C j (aj k)).chart x.val)).symm)
    (fun k x => terminalSourceCountableNegative (stage i)
      (fun a => (source i a : Type u)) (F i) (C i) (f0 i) (sigma (k + N)) (s, x))
    (fun k x => terminalSourceCountableNegative (stage j)
      (fun a => (source j a : Type u)) (F j) (C j) (f0 j) (sigma (k + N)) (s, x))
    (fun k x _ => congrFun (terminalSourceCountableNegative_good (stage i)
      (fun a => (source i a : Type u)) (F i) (C i) (f0 i) (ai k).property) (s, x))
    (fun k x _ => congrFun (terminalSourceCountableNegative_good (stage j)
      (fun a => (source j a : Type u)) (F j) (C j) (f0 j) (aj k).property) (s, x))
  intro x hx
  rw [← Filter.map_add_atTop_eq_nat N]
  exact htail x hx

local notation "O" => overlapSystem hD Lip (fun k => he (sigma k)) c hc
  (fun k => hlower (sigma k)) (fun k => hopen (sigma k)) (fun k => hconn (sigma k))

include hsigma hD he hc hlower hopen hconn hsmooth htau hUR hGood hmetric hterminal in

theorem terminalSourceCountable_actual_finite_germs
    (P : M46Predecessors.{u})
    (rho : ℕ → ℝ) (hrho : ∀ n, 0 < rho n)
    (hUball : ∀ n, (U n : Set E) = ball 0 (rho n / 2))
    (hrhoR : ∀ n, 2 * rho n < R n)
    (hsmall : ∀ n s, |s| ≤ 2 * rho n →
      ((13 * max (4 * L n / 3) 1) * s ^ 2) *
        Real.exp (max 1 ((13 * max (4 * L n / 3) 1) * s ^ 2)) ≤ 3)
    (g : ∀ k, RiemannianMetric 3 (M k))
    (hphysical : ∀ n k, EqOn (f0 n k)
      ((g k).pullbackCoefficients (chartParametrization Uset hU (maps k n))) (U n))
    (hread : ∀ n a, EqOn (f0 n a.val)
      (((F n a).metric 0).pullbackCoefficients (C n a).chart) (U n))
    (hQ : Tendsto Q atTop atTop)
    (B0 : ℕ → E → V) (Bminus : ℕ → ℝ × E → V)
    (hB0 : ∀ n, ContDiffOn ℝ ∞ (B0 n) (U n))
    (hminus : ∀ n, ContDiffOn ℝ ∞ (Bminus n) (Ioo (-(tau n / 2)) 0 ×ˢ (U n : Set E)))
    (hzero : ∀ n K, IsCompact K → K ⊆ U n → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ 0 (f0 n (sigma k))) (iteratedFDeriv ℝ 0 (B0 n)) atTop K)
    (hnegative : ∀ n m K, IsCompact K → K ⊆ Ioo (-(tau n / 2)) 0 ×ˢ (U n : Set E) →
      TendstoUniformlyOn (fun k => iteratedFDeriv ℝ m
        (terminalSourceCountableNegative (stage n) (fun a => (source n a : Type u))
          (F n) (C n) (f0 n) (sigma k))) (iteratedFDeriv ℝ m (Bminus n)) atTop K)
    (G : ∀ n, RicciFlow 3 (U n) (Icc (-(tau n / 4)) 0))
    (hcoeff : ∀ n t, t ∈ Icc (-(tau n / 4)) 0 → ∀ (x : U n) v w,
      ((G n).metric t).inner x v w =
        (if t < 0 then Bminus n (t, x) else B0 n x) v w)
    (hO : SmoothOverlap Uset hU O) :
    letI := quotientChartedSpace Uset hU O
    letI := quotient_isManifold Uset hU O hO
    ∀ (gX : RiemannianMetric 3 (Quotient (O).setoid))
    (_hzeroMetric : ∀ n (x : U n) v w,
      B0 n x v w = gX.inner ((O).include n x)
        (mfderiv (𝓡 3) (𝓡 3) ((O).include n) x v)
        (mfderiv (𝓡 3) (𝓡 3) ((O).include n) x w))
    (K : ℕ → Set (Quotient (O).setoid)) (hK : ∀ m, IsOpen (K m))
    (_hconnected : ∀ m, IsConnected (K m))
    (_hcompact : ∀ m, IsCompact (closure (K m)))
    (_hnested : ∀ m, closure (K m) ⊆ K (m + 1))
    (_hexhaust : (⋃ m, K m) = univ),
    TerminalSourceCountableFiniteGermsResult (fun n => tau n / 4) G (O).include gX K hK := by
  let := quotientChartedSpace Uset hU O
  let := quotient_isManifold Uset hU O hO
  intro gX hzeroMetric K hK hconnected hcompact hnested hexhaust
  let neg := fun n => terminalSourceCountableNegative (stage n)
    (fun a => (source n a : Type u)) (F n) (C n) (f0 n)
  let coeff := fun n (z : ℝ × E) => if z.1 < 0 then Bminus n z else B0 n z.2
  have hreadBall (n : ℕ) : ∀ a, EqOn (f0 n a.val)
      (((F n a).metric 0).pullbackCoefficients (C n a).chart) (ball 0 (rho n / 2)) := by
    simpa only [← hUball n] using hread n
  have hzeroPoint (n : ℕ) (x : E) (hx : x ∈ U n) :
      Tendsto (fun k => f0 n (sigma k) x) atTop (𝓝 (B0 n x)) := by
    have h := (hzero n {x} isCompact_singleton (singleton_subset_iff.mpr hx)).tendsto_at
      (mem_singleton x)
    have heval := ((ContinuousMultilinearMap.uniformContinuous_eval_const
      (𝕜 := ℝ) (0 : Fin 0 → E)).continuous.tendsto _).comp h
    simpa only [Function.comp_def, iteratedFDeriv_zero_apply] using heval
  have hclosed (n : ℕ) :
      ContDiffOn ℝ ∞ (coeff n) (Icc (-(tau n / 4)) 0 ×ˢ (U n : Set E)) ∧
        ∀ m K, IsCompact K → K ⊆ Ioo (-(tau n / 4)) 0 ×ˢ (U n : Set E) →
          TendstoUniformlyOn (fun k => iteratedFDeriv ℝ m (neg n (sigma k)))
            (iteratedFDeriv ℝ m (coeff n)) atTop K := by
    have h := terminalSourceCountable_g4_closed_limit (stage n) S B p P
      (htau n) (hrho n) (hrhoR n) (hsmall n) (fun a => raw a.val)
      (obs n) (W n) (H n) (C0 n) (fun a => base a.val) (fun a => Q a.val)
      (fun a => rNext a.val) (source n) (cyl n) (F n) (C n) (hGood n)
      (f0 n) (hreadBall n) hsigma (B0 n) (Bminus n)
      (by simpa only [← hUball n] using hB0 n)
      (by simpa only [← hUball n] using hminus n)
      (by
        intro x hx
        have hxU : x ∈ (U n : Set E) := (hUball n).symm ▸ hx
        exact hzeroPoint n x hxU)
      (by simpa only [← hUball n] using hnegative n)
    exact ⟨by simpa only [← hUball n] using h.1,
      by simpa only [← hUball n] using h.2.2⟩
  have hjets : ∀ n, LocallyEventuallyBoundedDerivatives (U n)
      (fun k => (g (sigma k)).pullbackCoefficients
        (chartParametrization Uset hU (maps (sigma k) n))) := by
    intro n Z _hZ hZU m
    obtain ⟨d, _hd, hbound⟩ := (terminalSourceCountable_g4_jet_bounds (stage n) S B p P
      (htau n) (hrho n) (hrhoR n) (hsmall n) (fun a => raw a.val)
      (obs n) (W n) (H n) (C0 n) (fun a => base a.val) (fun a => Q a.val)
      (fun a => rNext a.val) (source n) (cyl n) (F n) (C n) (hGood n)
      (f0 n) (hreadBall n)).1 m
    refine ⟨d, ?_⟩
    filter_upwards [hsigma.tendsto_atTop.eventually hbound] with k hk x hx
    rw [← terminalSourceCountable_coefficient_jets U (hphysical n (sigma k)) m (hZU hx)]
    exact hk x ((hUball n) ▸ hZU hx)
  have helliptic : ∀ n Z, IsCompact Z → Z ⊆ U n →
      ∃ a : ℝ, 0 < a ∧ ∀ᶠ k in atTop, ∀ x ∈ Z, ∀ v,
        a * ‖v‖ ^ 2 ≤ (g (sigma k)).pullbackCoefficients
          (chartParametrization Uset hU (maps (sigma k) n)) x v v := by
    intro n Z _hZ hZU
    have hbound := (terminalSourceCountable_g4_closed_bounds (stage n) S B p P
      (htau n) (hrho n) (hrhoR n) (hsmall n) (fun a => raw a.val)
      (obs n) (W n) (H n) (C0 n) (fun a => base a.val) (fun a => Q a.val)
      (fun a => rNext a.val) (source n) (cyl n) (F n) (C n) (hGood n)
      (f0 n) (hreadBall n)).1
    refine ⟨terminalSourceLower (13 * max (4 * L n / 3) 1) (tau n),
      terminalSourceLower_pos _ _, ?_⟩
    filter_upwards [hsigma.tendsto_atTop.eventually hbound] with k hk x hx v
    have hb := hk 0 ⟨neg_nonpos.mpr (htau n).le, le_rfl⟩ x ((hUball n) ▸ hZU hx) v
    have hz := terminalSourceCountableNegative_zero (stage n) (fun a => (source n a : Type u))
      (F n) (C n) (U n) (f0 n) (hread n) (sigma k) (hZU hx)
    dsimp only at hz
    rw [hz, hphysical n (sigma k) (hZU hx)] at hb
    exact hb
  have hconv (n : ℕ) (t : ℝ) (ht : t ∈ Icc (-(tau n / 4)) 0) :
      TendstoLocallyUniformlyOn (fun k x => neg n (sigma k) (t, x))
        (fun x => coeff n (t, x)) atTop (U n) :=
    terminalSourceCountable_negative_slice_convergence (stage n)
      (fun a => (source n a : Type u)) (htau n) (F n) (C n) (U n)
      (f0 n) (hread n) sigma (B0 n) (Bminus n) (hzero n) (hnegative n 0) ht
  have hcontinuous (n : ℕ) (t : ℝ) (ht : t ∈ Icc (-(tau n / 4)) 0) :
      ContinuousOn (fun x => coeff n (t, x)) (U n) :=
    (hclosed n).1.continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn (fun x hx => ⟨ht, hx⟩)
  have hsource := terminalSourceCountable_actual_source_identity U maps D hsigma hD
    Lip he c hc hlower hopen hconn hsmooth S B p stage tau R L eta htau hUR
    raw base Q rNext obs W H C0 source cyl F C hGood hmetric physical hterminal f0
  have hinv := terminalSourceCountable_limit_fibre_compatibility U
    (fun k => maps (sigma k)) D hD Lip (fun k => he (sigma k)) c hc
    (fun k => hlower (sigma k)) (fun k => hopen (sigma k))
    (fun k => hconn (sigma k)) (fun k => hsmooth (sigma k))
    (fun k => g (sigma k)) hjets helliptic hO (fun n => tau n / 4) G
    (fun n k => neg n (sigma k)) coeff hcoeff hconv hcontinuous
    (fun i j _ hti htj => hsource i j hti htj)
  have hop (n : ℕ) : ∀ t ∈ Icc (-(tau n / 4)) 0, ∀ x,
      ((G n).connection t).NonnegativeCurvatureOperator x := by
    apply terminalSourceCountable_chart_operator U n (stage n) S B p P (htau n) (hUR n)
      (fun a => raw a.val) (obs n) (W n) (H n) (C0 n) (fun a => base a.val)
      (fun a => Q a.val) (fun a => rNext a.val) (source n) (cyl n) (F n) (C n)
      (hGood n) (hmetric n) ?_ (f0 n) hsigma (coeff n) (G n) (hcoeff n) (hclosed n).2
    exact hQ.comp Filter.tendsto_comap
  have hq : ∀ n, IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ ((O).include n) :=
    fun n => include_isLocalDiffeomorph Uset hU O hO n
  have hcover : ∀ y, ∃ n x, (O).include n x = y := by
    intro y
    have hy : y ∈ ⋃ n, range ((O).include n) := by rw [(O).include_cover]; trivial
    obtain ⟨n, x, hx⟩ := mem_iUnion.mp hy
    exact ⟨n, x, hx⟩
  have hterm : ∀ n (x : U n) (v w : TangentSpace (𝓡 3) x),
      ((G n).metric 0).inner x v w = gX.inner ((O).include n x)
        (mfderiv (𝓡 3) (𝓡 3) ((O).include n) x v)
        (mfderiv (𝓡 3) (𝓡 3) ((O).include n) x w) := by
    intro n x v w
    rw [hcoeff n 0 ⟨by linarith [htau n], le_rfl⟩, if_neg (lt_irrefl 0)]
    exact hzeroMetric n x v w
  obtain ⟨s, delta, hsne, hs, hdelta, htime, flows, hmetricZero, hchart, hcompat, htriple⟩ :=
    terminalGerms_exists_exhaustion_flows (fun n => tau n / 4)
      (fun n => div_pos (htau n) (by norm_num)) G (O).include hq hcover hinv gX hterm
      K hK hconnected hcompact hnested hexhaust
  let domains : ℕ → Opens (Quotient (O).setoid) := fun m => ⟨K m, hK m⟩
  have hlocal : ∀ m t, t ∈ Icc (-delta m) 0 → ∀ x,
      ((flows m).connection t).NonnegativeCurvatureOperator x := by
    intro m
    apply terminalGerms_descended_operator (fun n => tau n / 4) G (O).include hq
      (domains m) (s m) ?_ (htime m) (flows m) (hchart m) hop
    intro y hy
    obtain ⟨n, hn⟩ := mem_iUnion.mp (hs m (subset_closure hy))
    obtain ⟨hns, x, hx⟩ := mem_iUnion.mp hn
    exact ⟨n, hns, x, hx⟩
  refine ⟨s, delta, hsne, hs, hdelta, htime, flows, hmetricZero, hchart, hcompat,
    htriple, hlocal, ?_⟩
  intro DX
  apply terminalGerms_ambient_operator_of_exhaustion DX domains delta hdelta flows
    hmetricZero hlocal
  intro y
  obtain ⟨m, hy, _, _⟩ := htriple y y y
  exact ⟨m, hy⟩

end ActualSources

end PoincareConjecture.M47
