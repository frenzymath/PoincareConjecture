import PoincareLib.Geometry.CurveShortening.Ramp.Family
import PoincareLib.Geometry.CurveShortening.Ramp.CurveEstimates
import PoincareLib.Geometry.CurveShortening.Ramp.LocalFlowTheory
import PoincareLib.Geometry.CurveShortening.Ramp.PolygonTheory

/-!
# M63 complete ramp and raw-family construction

All ten assigned blueprint blocks are retained: corrected Claim 19.8,
Claim 19.11, Claim 19.22, corrected Corollary 19.10, Corollary 19.13,
Definition 19.12, corrected Lemma 19.9, corrected Lemma 19.14,
Lemma 19.17 and corrected Lemma 19.24. The public geometry contains actual
flows and properties; M58/M62 theorem services occur only at the proof boundary.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT

section Analytic

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}

/-- M63's analytic conclusions about the supplied primitive geometry.
Local existence and continuation are outputs, so no global solution is
assumed to prove ramp existence. -/
structure M63AnalyticConclusion (F : RicciFlow n M (Set.Icc a b))
    (G : M63AmbientGeometry F) : Prop where
  local_base : M63LocalCurveTheory F
  local_product : ∀ circumference (h : 0 < circumference),
    M63LocalCurveTheory (G.product circumference h).flow
  base_estimates : ∀ T : ℝ, a < T → T ≤ b → ∀ c : ℝ → ℝ → M,
    M63C2ShrinkingCurveOn F c (Set.Icc a T) →
      M63C2CurveEstimates F c T G.K0 G.K1 G.K2
  product_estimates : ∀ circumference (h : 0 < circumference),
    ∀ T : ℝ, a < T → T ≤ b →
    ∀ c : ℝ → ℝ → (G.product circumference h).charts.Point,
      M63C2ShrinkingCurveOn (G.product circumference h).flow c (Set.Icc a T) →
        M63C2CurveEstimates (G.product circumference h).flow c T G.K0 G.K1 G.K2
  slope : ∀ circumference (h : 0 < circumference),
    ∀ T : ℝ, a < T → T ≤ b →
    ∀ c : ℝ → ℝ → (G.product circumference h).charts.Point,
      M63C2ShrinkingCurveOn (G.product circumference h).flow c (Set.Icc a T) →
        M63C2SlopeLaws (G.product circumference h) c T G.K2
  positive_degree : ∀ circumference (h : 0 < circumference),
    ∀ gamma : ℝ → (G.product circumference h).charts.Point,
      Function.Periodic gamma curvePeriod →
      ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) 2 gamma →
      ∀ t ∈ Set.Icc a b, M63IsRampAt (G.product circumference h) gamma t →
        Nonempty (M63PositiveDegreeLift (G.product circumference h) gamma)
  preservation : ∀ circumference (h : 0 < circumference),
    ∀ T : ℝ, a < T → T ≤ b →
    ∀ c : ℝ → ℝ → (G.product circumference h).charts.Point,
      M63C2ShrinkingCurveOn (G.product circumference h).flow c (Set.Icc a T) →
      M63IsRampAt (G.product circumference h) (fun x => c x a) a →
        M63RampPreservation (G.product circumference h) c T G.K0 G.K1 G.K2
  c2_ramp_existence : ∀ circumference (h : 0 < circumference),
    M63C2RampExistence (G.product circumference h)
  smooth_ramp_existence : ∀ circumference (h : 0 < circumference),
    M63SmoothRampExistence (G.product circumference h)
  polygons : ∀ circumference (h : 0 < circumference), ∀ t ∈ Set.Icc a b,
    ∀ N : ℕ, 0 < N →
    ∀ polygon : M63GeodesicPolygon (F.metric t) (F.connection t) N,
      M63PolygonEstimates (G.product circumference h) t N polygon
  sampled_length : M63SampledPolygonLengthComparison F
  uniform_derivatives : ∀ L0 Theta0 : ℝ, 0 ≤ L0 → 0 ≤ Theta0 →
    Nonempty (M63UniformDerivativeEstimates G L0 Theta0)

/-- One choice of actual geometry and M63's conclusions about that choice. -/
structure M63FlowConclusion (F : RicciFlow n M (Set.Icc a b)) where
  geometry : M63AmbientGeometry F
  analytic : M63AnalyticConclusion F geometry

end Analytic

section RawFamilies

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {a b : ℝ}

/-- The actual supremum of initial lengths in the given raw family. -/
noncomputable def m63FamilyLengthSup (g : RiemannianMetric 3 M)
    (Gamma : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M))) : ℝ :=
  sSup (Set.range (fun z => freeLoopLength g (Gamma z)))

/-- Full Lemma 19.17 and the subsequent family of canonical ramp solutions.
Approximation, constants and the fixed geometry precede circumference and
family member. Product curves have positive degree; only their base loops are null. -/
structure M63FamilyConclusion {F : RicciFlow 3 M (Set.Icc a b)}
    (G : M63AmbientGeometry F)
    (Gamma : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M))) (zeta : ℝ) where
  approximation : M63RawApproximation F Gamma zeta
  source_lengths_bounded : BddAbove (Set.range (fun z => freeLoopLength (F.metric a) (Gamma z)))
  source_length_attained : ∃ z, freeLoopLength (F.metric a) (Gamma z) =
    m63FamilyLengthSup (F.metric a) Gamma
  initial_bound : ℝ
  initial_bound_positive : 0 < initial_bound
  initial_length_bound : m63FamilyLengthSup (F.metric a) Gamma + 1 ≤ initial_bound
  initial_turning_bound : (approximation.count : ℝ) * Real.pi ≤ initial_bound
  derivative_estimates : M63UniformDerivativeEstimates G initial_bound initial_bound
  canonical_length : ∀ circumference (h : 0 < circumference), circumference < 1 →
    ∀ z : LoopTwoSphere,
      m62Length (G.product circumference h).flow
        (fun x _ => m63CanonicalRamp (G.product circumference h)
          (periodicFreeLoop (approximation.family z)) x) a ≤
        m63FamilyLengthSup (F.metric a) Gamma + 1
  canonical_total_curvature : ∀ circumference (h : 0 < circumference),
    ∀ z : LoopTwoSphere,
      m62TotalCurvature (G.product circumference h).flow
        (fun x _ => m63CanonicalRamp (G.product circumference h)
          (periodicFreeLoop (approximation.family z)) x) a ≤
        (approximation.count : ℝ) * Real.pi
  solutions : ∀ circumference (h : 0 < circumference),
    M63ProductSolutionFamily (G.product circumference h) approximation
  length_bound : ∀ circumference (h : 0 < circumference), circumference < 1 →
    ∀ z t, t ∈ Set.Icc a b →
      m62Length (G.product circumference h).flow (solutions circumference h |>.curve z) t ≤
        (m63FamilyLengthSup (F.metric a) Gamma + 1) * Real.exp (G.K2 * (t - a))
  total_bound : ∀ circumference (h : 0 < circumference), circumference < 1 →
    ∀ z t, t ∈ Set.Icc a b →
      m62TotalCurvature (G.product circumference h).flow (solutions circumference h |>.curve z) t +
        m62Length (G.product circumference h).flow (solutions circumference h |>.curve z) t ≤
          (m63FamilyLengthSup (F.metric a) Gamma + 1 + (approximation.count : ℝ) * Real.pi) *
            Real.exp ((m62C1 G.K0 G.K1 G.K2 + G.K2) * (t - a))

end RawFamilies

/-- The exact Corollary 18.28 disk service used twice on the short-loop
subset of the approximation proof. It supplies no smoothing or PDE theorem. -/
def M63SmallLoopFillingService : Prop :=
  ∀ {M : Type u} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
    (g : RiemannianMetric 3 M) (_compact : IsCompact (Set.univ : Set M)),
    ∀ η : ℝ, 0 < η → ∃ ζ : ℝ, 0 < ζ ∧ ζ < η / 2 ∧
      ∀ gamma : C1FreeLoopSpace (M := M), freeLoopLength g gamma < ζ →
        ∃ D : LipschitzSpanningDisk g gamma, D.area < η

/-- Complete M63 skeleton contract. Besides constructing an approximation,
construct the evolving family for each supplied raw approximation, preserving
that exact data. Generic and family construction use primitive geometry. -/
def M63RampEstimatesTheory : Prop :=
  (∀ N : ℕ, 0 < N → M63ProfileProperties N) ∧
  (∀ (n : ℕ) (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [T2Space M] [SecondCountableTopology M] (a b : ℝ)
    (F : RicciFlow n M (Set.Icc a b)), IsCompact (Set.univ : Set M) →
      Nonempty (M63FlowConclusion F)) ∧
  (∀ (M : Type u) [TopologicalSpace M] [ChartedSpace LoopAmbient M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [SecondCountableTopology M]
    (a b : ℝ) (F : RicciFlow 3 M (Set.Icc a b)),
    IsCompact (Set.univ : Set M) → ∀ G : M63AmbientGeometry F,
    ∀ Gamma : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M)),
      M61NullFamily Gamma → ∀ zeta : ℝ, 0 < zeta → zeta < 1 →
        Nonempty (M63FamilyConclusion G Gamma zeta)) ∧
  (∀ (M : Type u) [TopologicalSpace M] [ChartedSpace LoopAmbient M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [SecondCountableTopology M]
    (a b : ℝ) (F : RicciFlow 3 M (Set.Icc a b)),
    IsCompact (Set.univ : Set M) → ∀ G : M63AmbientGeometry F,
    ∀ Gamma : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M)),
      M61NullFamily Gamma → ∀ zeta : ℝ, 0 < zeta →
        ∀ A : M63RawApproximation F Gamma zeta,
          Nonempty {C : M63FamilyConclusion G Gamma zeta // C.approximation = A})

end PoincareMT
