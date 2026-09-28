import PoincareConjecture.Proofs.M47.TerminalSourceCountableJetBounds
import PoincareConjecture.Proofs.M47.TerminalSourceCountableMaps
import PoincareConjecture.Proofs.M47.TerminalSourceCountableLabels
import PoincareConjecture.Proofs.M47.TerminalGermsExtraction











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter TopologicalSpace
open scoped Manifold ContDiff Bundle Topology NNReal

universe u

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "V" => E →L[ℝ] E →L[ℝ] ℝ



theorem terminalSourceCountable_extract_actual_charts
    (S : RepairedControlledSchedulesData.{u})
    (B : M47ComponentAnalyticBounds.{u} S.setup.C)
    (p : SurgeryParameterPrefix S.constants) (P : M46Predecessors.{u})
    {M : ℕ → Type u} [∀ k, MetricSpace (M k)] [∀ k, ChartedSpace E (M k)]
    [∀ k, IsManifold (𝓡 3) ∞ (M k)]
    (g : ∀ k, RiemannianMetric 3 (M k))
    (rho tau R L eta : ℕ → ℝ) (N : ℕ → ℕ)
    (hrho : ∀ j, 0 < rho j) (htau : ∀ j, 0 < tau j)
    (hrhoR : ∀ j, 2 * rho j < R j)
    (hsmall : ∀ j, ∀ s : ℝ, |s| ≤ 2 * rho j →
      ((13 * max (4 * L j / 3) 1) * s ^ 2) *
        Real.exp (max 1 ((13 * max (4 * L j / 3) 1) * s ^ 2)) ≤ 3)
    (F0 : ∀ j, {k : ℕ // j ≤ k} → SurgeryFlowData.{u})
    (O : ∀ j a, SurgeryObservation (F0 j a))
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
      TerminalSourceJetsG4Good S B p (O j a) (H j a) (source j a) (cyl j a) (F j a)
        (τ := tau j) (base := base j a) (Q := Q j a) (rNext := rNext j a)
        (R := R j) (L := L j) (eta := eta j) (C j a i))
    (e : ∀ k j, j ≤ k → Fin (N j + 1) → terminalSourceCountableDomain (rho j) → M k)
    (hopen : ∀ k j hjk i, Topology.IsOpenEmbedding (e k j hjk i))
    (hsmooth : ∀ k j hjk i, IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (e k j hjk i))
    (hdist : ∀ k j hjk i x y,
      (1 / 2 : ℝ) * dist x y ≤ dist (e k j hjk i x) (e k j hjk i y) ∧
        dist (e k j hjk i x) (e k j hjk i y) ≤ (3 / 2 : ℝ) * dist x y)
    (point : ∀ k, M k) (baseBound : ℕ → ℝ)
    (hzero : ∀ k, e k 0 (Nat.zero_le k) 0 (terminalSourceCountableZero (hrho 0)) = point k)
    (hbase : ∀ k j hjk i x, dist (point k) (e k j hjk i x) ≤ baseBound j)
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
            (C j ⟨k, hjk⟩ i).chart y.val) x w)) :
    let label := terminalSourceCountableLabel N
    let U := fun n => terminalSourceCountableDomain (rho (label n).1)
    letI : ∀ n, Nonempty (U n) := fun n => ⟨terminalSourceCountableZero (hrho (label n).1)⟩
    let total := fun k n => terminalSourceCountableMap hrho e k (label n).1 (label n).2
    let f0 := fun n k => (g k).pullbackCoefficients
      (ChartDistance.chartParametrization (fun n => (U n : Set E))
        (fun n => (U n).isOpen) (total k n))
    let fminus := fun n => terminalSourceCountableNegative (label n).1
      (fun a => (source (label n).1 a : Type u)) (F (label n).1)
      (fun a => C (label n).1 a (label n).2) (f0 n)
    ∃ sigma : ℕ → ℕ, StrictMono sigma ∧
      (∀ n, ∀ᶠ k in atTop, ∃ hjk : (label n).1 ≤ sigma k,
        total (sigma k) n = e (sigma k) (label n).1 hjk (label n).2 ∧
        fminus n (sigma k) = fun z : ℝ × E =>
          ((F (label n).1 ⟨sigma k, hjk⟩).metric z.1).pullbackCoefficients
            (C (label n).1 ⟨sigma k, hjk⟩ (label n).2).chart z.2) ∧
      ∃ B0 : ℕ → E → V,
        (∀ n, ContDiffOn ℝ ∞ (B0 n) (U n)) ∧
        (∀ n m K, IsCompact K → K ⊆ U n → TendstoUniformlyOn
          (fun k => iteratedFDeriv ℝ m (f0 n (sigma k)))
          (iteratedFDeriv ℝ m (B0 n)) atTop K) ∧
        ∃ Bminus : ℕ → ℝ × E → V,
          (∀ n, ContDiffOn ℝ ∞ (Bminus n)
            (Ioo (-(tau (label n).1 / 2)) 0 ×ˢ (U n : Set E))) ∧
          (∀ n m K, IsCompact K →
            K ⊆ Ioo (-(tau (label n).1 / 2)) 0 ×ˢ (U n : Set E) →
            TendstoUniformlyOn (fun k => iteratedFDeriv ℝ m (fminus n (sigma k)))
              (iteratedFDeriv ℝ m (Bminus n)) atTop K) ∧
          ∃ D : ∀ n n', C(U n × U n', ℝ), ∀ n n', TendstoLocallyUniformly
            (fun k (z : U n × U n') =>
              dist (total (sigma k) n z.1) (total (sigma k) n' z.2))
            (D n n') atTop := by
  let label := terminalSourceCountableLabel N
  let U := fun n => terminalSourceCountableDomain (rho (label n).1)
  let : ∀ n, Nonempty (U n) := fun n => ⟨terminalSourceCountableZero (hrho (label n).1)⟩
  let total := fun k n => terminalSourceCountableMap hrho e k (label n).1 (label n).2
  let f0 := fun n k => (g k).pullbackCoefficients
    (ChartDistance.chartParametrization (fun n => (U n : Set E))
      (fun n => (U n).isOpen) (total k n))
  let fminus := fun n => terminalSourceCountableNegative (label n).1
    (fun a => (source (label n).1 a : Type u)) (F (label n).1)
    (fun a => C (label n).1 a (label n).2) (f0 n)
  have hgeometry := terminalSourceCountableMap_geometry hrho e hopen hsmooth
  have hdistances := terminalSourceCountableMap_distances hrho e hdist
  have hcross := (terminalSourceCountableMap_base_distances hrho e point baseBound
    hzero (fun k j hjk i x y => (hdist k j hjk i x y).2) hbase).2
  have hUR (n : ℕ) : (U n : Set E) ⊆ Metric.ball 0 (R (label n).1) :=
    Metric.ball_subset_ball (by linarith [hrho (label n).1, hrhoR (label n).1])
  have hf0 (n k : ℕ) : ContDiffOn ℝ ∞ (f0 n k) (U n) :=
    terminalSourceCountable_pullback_smooth U (g k)
      (hgeometry k (label n).1 (label n).2).2.contMDiff
  have hread (n : ℕ) (a : {k : ℕ // (label n).1 ≤ k}) :
      EqOn (f0 n a.val)
        (((F (label n).1 a).metric 0).pullbackCoefficients
          (C (label n).1 a (label n).2).chart) (U n) := by
    dsimp only [f0, total]
    rw [terminalSourceCountableMap_good hrho e a.property]
    exact terminalSourceCountable_pullback_readout U (g a.val)
      ((F (label n).1 a).metric 0)
      (hsmooth a.val (label n).1 a.property (label n).2).contMDiff
      (C (label n).1 a (label n).2).chart
      ((C (label n).1 a (label n).2).smooth.mono (hUR n))
      (hmetric a.val (label n).1 a.property (label n).2)
  have hbounds (n : ℕ) := terminalSourceCountable_g4_jet_bounds (label n).1 S B p P
    (htau (label n).1) (hrho (label n).1) (hrhoR (label n).1) (hsmall (label n).1)
    (F0 (label n).1) (O (label n).1) (W (label n).1) (H (label n).1)
    (C0 (label n).1) (base (label n).1) (Q (label n).1) (rNext (label n).1)
    (source (label n).1) (cyl (label n).1) (F (label n).1)
    (fun a => C (label n).1 a (label n).2) (hGood (label n).1 (label n).2)
    (f0 n) (hread n)
  have hfminus (n k : ℕ) : ContDiffOn ℝ ∞ (fminus n k)
      (Ioo (-(tau (label n).1 / 2)) 0 ×ˢ (U n : Set E)) := by
    apply (terminalSourceCountableNegative_smooth (label n).1
      (fun a => (source (label n).1 a : Type u)) (F (label n).1)
      (fun a => C (label n).1 a (label n).2) (U n) (hUR n) (f0 n) (hf0 n) k).mono
    intro z hz
    exact ⟨⟨by linarith [hz.1.1, htau (label n).1], hz.1.2.le⟩, hz.2⟩
  have hLip (k n : ℕ) : LipschitzWith (3 / 2 : ℝ≥0) (total k n) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    exact (hdistances.2 k (label n).1 (label n).2 x y).2
  obtain ⟨sigma, hsigma, rest⟩ := terminalGerms_extract_common_charts
    (fun n => (U n : Set E)) (fun n => (U n).isOpen)
    (fun n => tau (label n).1 / 2) total (fun _ => (3 / 2 : ℝ≥0)) hLip (by
      intro n n' x y
      exact ⟨max (baseBound (label n).1) (rho 0 / 2) +
        max (baseBound (label n').1) (rho 0 / 2),
        fun k => hcross k (label n).1 (label n).2 x (label n').1 (label n').2 y⟩)
    f0 hf0 (by
      intro n K _hK hKU m
      obtain ⟨D, _hD, hD⟩ := (hbounds n).1 m
      exact ⟨D, hD.mono (fun _ hk x hx => hk x (hKU hx))⟩)
    fminus hfminus (by
      intro n K _hK hKU m
      obtain ⟨D, _hD, hD⟩ := (hbounds n).2 m
      refine ⟨D, hD.mono ?_⟩
      intro k hk z hz
      have hsmallBall : (U n : Set E) ⊆ Metric.closedBall 0 (rho (label n).1) :=
        (Metric.ball_subset_ball (by linarith [hrho (label n).1])).trans
          Metric.ball_subset_closedBall
      exact hk z.1 (hKU hz).1 z.2 (hsmallBall (hKU hz).2))
  refine ⟨sigma, hsigma, ?_, rest⟩
  intro n
  filter_upwards [hsigma.tendsto_atTop.eventually (eventually_ge_atTop (label n).1)] with k hk
  exact ⟨hk, terminalSourceCountableMap_good hrho e hk (label n).2,
    terminalSourceCountableNegative_good (label n).1
      (fun a => (source (label n).1 a : Type u)) (F (label n).1)
      (fun a => C (label n).1 a (label n).2) (f0 n) hk⟩

end PoincareConjecture.M47
