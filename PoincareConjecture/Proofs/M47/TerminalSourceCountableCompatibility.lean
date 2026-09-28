import PoincareConjecture.Proofs.M47.TerminalSourceCountableSourceOverlap
import PoincareConjecture.Proofs.M47.TerminalSourceCountableSliceConvergence
import PoincareConjecture.Proofs.M47.TerminalGermsMetricOverlap
import PoincareConjecture.Proofs.M47.TerminalGermsFiberCompatibility
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Overlap.JetBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric TopologicalSpace Poincare.Gluing Poincare.Analysis.Calculus
open scoped Manifold ContDiff Topology NNReal

universe u

namespace PoincareConjecture.M47

open ChartDistance

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "V" => E →L[ℝ] E →L[ℝ] ℝ

section Charts

variable (U : ℕ → Opens E) [∀ n, Nonempty (U n)]

local notation "Uset" => (fun n => (U n : Set E))
local notation "hU" => (fun n => TopologicalSpace.Opens.isOpen (U n))

noncomputable local instance chartSpace (n : ℕ) : ChartedSpace E (U n) :=
  (U n).isOpen.isOpenEmbedding_subtypeVal.singletonChartedSpace

noncomputable local instance chartManifold (n : ℕ) : IsManifold (𝓡 3) ∞ (U n) :=
  (U n).isOpen.isOpenEmbedding_subtypeVal.isManifold_singleton

local instance chartsLocallyCompact : ∀ n, LocallyCompactSpace (Piece Uset n) :=
  fun n => (U n).isOpen.locallyCompactSpace

local instance opensLocallyCompact : ∀ n, LocallyCompactSpace (U n) :=
  fun n => (U n).isOpen.locallyCompactSpace

theorem terminalSourceCountable_limit_fibre_compatibility
    {M : ℕ → Type u} [∀ k, MetricSpace (M k)] [∀ k, ChartedSpace E (M k)]
    [∀ k, IsManifold (𝓡 3) ∞ (M k)]
    (maps : ∀ k n, U n → M k)
    (D : ∀ n n', C(U n × U n', ℝ))
    (hD : ∀ n n' x y, Tendsto (fun k => dist (maps k n x) (maps k n' y)) atTop
      (𝓝 (D n n' (x, y))))
    (L : ℕ → ℝ≥0) (he : ∀ k n, LipschitzWith (L n) (maps k n))
    (c : ℕ → ℝ) (hc : ∀ n, 0 < c n)
    (hlower : ∀ k n x y, c n * dist x y ≤ dist (maps k n x) (maps k n y))
    (hopen : ∀ k n, Topology.IsOpenEmbedding (maps k n))
    (hconn : ∀ k (x : M k) r, IsPreconnected (ball x r))
    (hsmooth : ∀ k n, IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (maps k n))
    (g : ∀ k, RiemannianMetric 3 (M k))
    (hjets : ∀ n, LocallyEventuallyBoundedDerivatives (U n)
      (fun k => (g k).pullbackCoefficients (chartParametrization Uset hU (maps k n))))
    (helliptic : ∀ n K, IsCompact K → K ⊆ U n →
      ∃ a : ℝ, 0 < a ∧ ∀ᶠ k in atTop, ∀ x ∈ K, ∀ v,
        a * ‖v‖ ^ 2 ≤ (g k).pullbackCoefficients
          (chartParametrization Uset hU (maps k n)) x v v)
    (hO : SmoothOverlap Uset hU (overlapSystem hD L he c hc hlower hopen hconn))
    (tau : ℕ → ℝ) (G : ∀ n, RicciFlow 3 (U n) (Icc (-tau n) 0))
    (f : ℕ → ℕ → ℝ × E → V) (coeff : ℕ → ℝ × E → V)
    (hcoeff : ∀ n t, t ∈ Icc (-tau n) 0 → ∀ (x : U n) v w,
      ((G n).metric t).inner x v w = coeff n (t, x) v w)
    (hconv : ∀ n t, t ∈ Icc (-tau n) 0 →
      TendstoLocallyUniformlyOn (fun k x => f n k (t, x))
        (fun x => coeff n (t, x)) atTop (U n))
    (hcontinuous : ∀ n t, t ∈ Icc (-tau n) 0 →
      ContinuousOn (fun x => coeff n (t, x)) (U n))
    (hsource : ∀ i j t, t ∈ Icc (-tau i) 0 → t ∈ Icc (-tau j) 0 →
      ∀ x ∈ Subtype.val '' overlap (fun n n' => D n n') i j,
      ∀ᶠ k in atTop, ∀ v w,
        let T := coordinateRepresentative Uset hU
          (fun y => Function.invFun (maps k j) (maps k i y))
        f j k (t, T x) (fderiv ℝ T x v) (fderiv ℝ T x w) = f i k (t, x) v w) :
    let O := overlapSystem hD L he c hc hlower hopen hconn
    letI := quotientChartedSpace Uset hU O
    letI := quotient_isManifold Uset hU O hO
    ∀ i j t, t ∈ Icc (-tau i) 0 → t ∈ Icc (-tau j) 0 →
      ∀ (x : U i) (y : U j), O.include i x = O.include j y →
      ∀ (a b : TangentSpace (𝓡 3) x) (c d : TangentSpace (𝓡 3) y),
        mfderiv (𝓡 3) (𝓡 3) (O.include i) x a =
          mfderiv (𝓡 3) (𝓡 3) (O.include j) y c →
        mfderiv (𝓡 3) (𝓡 3) (O.include i) x b =
          mfderiv (𝓡 3) (𝓡 3) (O.include j) y d →
        ((G i).metric t).inner x a b = ((G j).metric t).inner y c d := by
  let O := overlapSystem hD L he c hc hlower hopen hconn
  let := quotientChartedSpace Uset hU O
  let := quotient_isManifold Uset hU O hO
  have hbound := fun i j => locallyEventuallyBoundedDerivatives_source_transition
    Uset hU hD L he c hc hlower hopen hconn hsmooth g hjets helliptic i j
  have hq : ∀ i, IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (O.include i) :=
    fun i => include_isLocalDiffeomorph Uset hU O hO i
  dsimp only
  intro i j t hti htj x y hxy a b v w ha hb
  apply terminalGerms_metric_fibre_compatibility O hq i j (hO i j)
    ((G i).metric t) ((G j).metric t) ?_ x y hxy a b v w ha hb
  apply terminalGerms_metric_pair_compatibility Uset hU O hO i j
    ((G i).metric t) ((G j).metric t)
    (fun z => coeff i (t, z)) (fun z => coeff j (t, z))
    (hcoeff i t hti) (hcoeff j t htj)
  apply terminalGerms_local_coefficient_transition Uset hU hD L he c hc hlower
    hopen hconn hsmooth i j (hbound i j)
    (fun k z => f i k (t, z)) (fun k z => f j k (t, z))
    (fun z => coeff i (t, z)) (fun z => coeff j (t, z))
    ?_ (hconv j t htj) (hcontinuous j t htj) (hsource i j t hti htj)
  intro z hz v w
  have hev : Continuous (fun A : V => A v w) :=
    (continuous_id.clm_apply continuous_const).clm_apply continuous_const
  exact (hev.tendsto _).comp ((hconv i t hti).tendsto_at hz)

end Charts

end PoincareConjecture.M47
