import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.DouglasMorreyInterface
import PoincareConjecture.Proofs.M05.Geometry.Riemannian.Coordinates.Coefficients
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Distance.Basic
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.Sobolev.Weak.Derivatives

set_option autoImplicit false

open Set Filter MeasureTheory
open Poincare.Analysis.Sobolev.Weak
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}
  {c0 c1 : ℝ → M}

def M64AnnulusUniformlyOn (f : ℕ → LoopPlane → M) (limit : LoopPlane → M) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ᶠ k in atTop, ∀ p ∈ m64AnnulusDomain,
      g.edist (f k p) (limit p) < ENNReal.ofReal ε

def M64AnnulusCommonCircleModulus (f : ℕ → LoopPlane → M) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ k : ℕ, ∀ s ∈ Icc (0 : ℝ) 1, ∀ x y : ℝ, |x - y| < δ →
      g.edist (f k (annulusPoint x s)) (f k (annulusPoint y s)) < ENNReal.ofReal ε

def M64AnnulusGramNearlyConformal (f : LoopPlane → M) (epsilon : ℝ) : Prop :=
  0 ≤ epsilon ∧
    ∀ᵐ p ∂volume, p ∈ interior m64AnnulusDomain →
      ∃ scale : ℝ, 0 ≤ scale ∧ ∀ i j : Fin 2,
        |g.inner (f p)
            (mfderiv (𝓡 2) (𝓡 n) f p (EuclideanSpace.basisFun (Fin 2) ℝ i))
            (mfderiv (𝓡 2) (𝓡 n) f p (EuclideanSpace.basisFun (Fin 2) ℝ j)) -
          scale * (if i = j then (1 : ℝ) else 0)| ≤ epsilon

structure M64AnnulusMinimizingSequenceCertificate where
  seed : M64Annulus g c0 c1
  sequence : ℕ → M64Annulus g c0 c1
  sequence_antitone : Antitone (fun k => (sequence k).area)
  area_tendsto_infimum :
    Tendsto (fun k => (sequence k).area) atTop
      (𝓝 (m64LeastAnnulusArea g c0 c1))

noncomputable def m64AnnulusMinimizingSequence_of_seed
    (seed : M64Annulus g c0 c1) :
    M64AnnulusMinimizingSequenceCertificate (g := g) (c0 := c0) (c1 := c1) :=
  let witness := Classical.choose (m64Annulus_exists_minimizing_sequence seed)
  let properties := Classical.choose_spec (m64Annulus_exists_minimizing_sequence seed)
  { seed := seed
    sequence := witness
    sequence_antitone := properties.1
    area_tendsto_infimum := properties.2 }

structure M64AnnulusNearlyConformalSequenceCertificate
    (S : M64AnnulusMinimizingSequenceCertificate
      (g := g) (c0 := c0) (c1 := c1)) where
  energy_bound : ℝ
  energy_bound_nonnegative : 0 ≤ energy_bound
  energy_integrable : ∀ k, IntegrableOn (m60EnergyDensity g (S.sequence k).map)
    m64AnnulusDomain volume
  energy_le : ∀ k,
    (∫ p in m64AnnulusDomain, m60EnergyDensity g (S.sequence k).map p) ≤ energy_bound
  conformality_error : ℕ → ℝ
  conformality_error_tendsto : Tendsto conformality_error atTop (𝓝 0)
  nearly_conformal : ∀ k, M64AnnulusGramNearlyConformal (g := g)
    (S.sequence k).map (conformality_error k)

structure M64AnnulusWeakGradient (g : RiemannianMetric n M)
    (f : LoopPlane → M) where
  chart_center : M
  mapsTo_chart : MapsTo f m64AnnulusDomain
    (extChartAt (𝓡 n) chart_center).source
  coordinate : LoopPlane → EuclideanSpace ℝ (Fin n)
  coordinate_eq : ∀ p ∈ m64AnnulusDomain,
    coordinate p = extChartAt (𝓡 n) chart_center (f p)
  column : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin n)
  column_memLp : ∀ i, MemLp (column i) 2
    (volume.restrict (interior m64AnnulusDomain))
  weak_derivative : ∀ (i : Fin 2) (a : Fin n),
    HasWeakPartialDeriv i (fun z => column i z a)
      (fun z => coordinate z a) (interior m64AnnulusDomain)

noncomputable def m64AnnulusWeakEnergyDensity
    (g : RiemannianMetric n M) {f : LoopPlane → M}
    (V : M64AnnulusWeakGradient g f) (p : LoopPlane) : ℝ :=
  (1 / 2 : ℝ) * ∑ i : Fin 2,
    g.pullbackCoefficients (extChartAt (𝓡 n) V.chart_center).symm
      (V.coordinate p) (V.column i p) (V.column i p)

structure M64FiniteEnergyContinuousLimit where
  map : LoopPlane → M
  continuous_on_domain : ContinuousOn map m64AnnulusDomain
  gradient : M64AnnulusWeakGradient g map
  energy_bound : ℝ
  energy_bound_nonnegative : 0 ≤ energy_bound
  energy_integrable : IntegrableOn (m64AnnulusWeakEnergyDensity g gradient)
    m64AnnulusDomain volume
  energy_le : (∫ p in m64AnnulusDomain,
    m64AnnulusWeakEnergyDensity g gradient p) ≤ energy_bound
  weakly_conformal : ∀ᵐ p ∂volume, p ∈ interior m64AnnulusDomain →
    ∃ scale : ℝ, 0 ≤ scale ∧ ∀ i j : Fin 2,
      g.pullbackCoefficients (extChartAt (𝓡 n) gradient.chart_center).symm
        (gradient.coordinate p) (gradient.column i p) (gradient.column j p) =
        scale * (if i = j then (1 : ℝ) else 0)

structure M64CourantLebesgueArzelaCertificate
    (S : M64AnnulusMinimizingSequenceCertificate
      (g := g) (c0 := c0) (c1 := c1)) where
  normalization : M64AnnulusNearlyConformalSequenceCertificate S
  subsequence : ℕ → ℕ
  subsequence_strictMono : StrictMono subsequence
  limit : M64FiniteEnergyContinuousLimit (g := g)
  equicontinuity : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ k : ℕ, ∀ x ∈ m64AnnulusDomain, ∀ y ∈ m64AnnulusDomain, ‖x - y‖ < δ →
      g.edist ((S.sequence (subsequence k)).map x)
        ((S.sequence (subsequence k)).map y) < ENNReal.ofReal ε
  uniform_limit : M64AnnulusUniformlyOn (g := g)
    (fun k => (S.sequence (subsequence k)).map) limit.map
  common_circle_modulus : M64AnnulusCommonCircleModulus (g := g)
    (fun k => (S.sequence (subsequence k)).map)

structure M64HeinzHildebrandtBoundaryCertificate
    (L : M64FiniteEnergyContinuousLimit
      (g := g)) where
  periodic : ∀ x s : ℝ,
    L.map (annulusPoint (x + curvePeriod) s) = L.map (annulusPoint x s)
  lower_boundary : ∀ x : ℝ, L.map (annulusPoint x 0) = c0 x
  upper_boundary : ∀ x : ℝ, L.map (annulusPoint x 1) = c1 x
  lipschitz_constant : ℝ
  lipschitz_nonnegative : 0 ≤ lipschitz_constant
  lipschitz_on_domain : ∀ x y : m64AnnulusDomain,
    g.edist (L.map x) (L.map y) ≤
      ENNReal.ofReal lipschitz_constant *
        ENNReal.ofReal ‖(x : LoopPlane) - y‖
  ae_manifold_differentiable : ∀ᵐ p ∂volume,
    p ∈ m64AnnulusDomain → MDifferentiableAt (𝓡 2) (𝓡 n) L.map p
  area_integrable : IntegrableOn (m60AreaDensity g L.map)
    m64AnnulusDomain volume
  piecewise_c1_on_limit : ∃ k : ℕ, 0 < k ∧ ∃ cut : Fin (k + 1) → ℝ,
    StrictMono cut ∧ cut 0 = 0 ∧ cut (Fin.last k) = curvePeriod ∧
      ∀ j : Fin k, ContMDiffOn (𝓡 2) (𝓡 n) 1 L.map
        {p : LoopPlane | cut j.castSucc ≤ p 0 ∧ p 0 ≤ cut j.succ ∧
          0 ≤ p 1 ∧ p 1 ≤ 1}

def m64Annulus_of_heinzHildebrandt
    (L : M64FiniteEnergyContinuousLimit
      (g := g))
    (H : M64HeinzHildebrandtBoundaryCertificate
      (g := g) (c0 := c0) (c1 := c1) L) :
    M64Annulus g c0 c1 :=
  { map := L.map
    continuous_on_domain := L.continuous_on_domain
    periodic := H.periodic
    lower_boundary := H.lower_boundary
    upper_boundary := H.upper_boundary
    lipschitz_constant := H.lipschitz_constant
    lipschitz_nonnegative := H.lipschitz_nonnegative
    lipschitz_on_domain := H.lipschitz_on_domain
    ae_manifold_differentiable := H.ae_manifold_differentiable
    area_integrable := H.area_integrable }

theorem m64Annulus_of_heinzHildebrandt_piecewise_c1
    (L : M64FiniteEnergyContinuousLimit
      (g := g))
    (H : M64HeinzHildebrandtBoundaryCertificate
      (g := g) (c0 := c0) (c1 := c1) L) :
    M64PiecewiseC1Annulus
      (m64Annulus_of_heinzHildebrandt (c0 := c0) (c1 := c1) L H) := by
  exact H.piecewise_c1_on_limit

structure M64MorreyLowerSemicontinuityCertificate
    (S : M64AnnulusMinimizingSequenceCertificate
      (g := g) (c0 := c0) (c1 := c1))
    (C : M64CourantLebesgueArzelaCertificate S)
    (A : M64Annulus g c0 c1) : Prop where
  map_eq_limit : A.map = C.limit.map
  area_le_liminf : A.area ≤
    liminf (fun k => (S.sequence (C.subsequence k)).area) atTop

theorem M64MorreyLowerSemicontinuityCertificate.area_le_infimum
    (S : M64AnnulusMinimizingSequenceCertificate
      (g := g) (c0 := c0) (c1 := c1))
    (C : M64CourantLebesgueArzelaCertificate S)
    (A : M64Annulus g c0 c1)
    (L : M64MorreyLowerSemicontinuityCertificate S C A) :
    A.area ≤ m64LeastAnnulusArea g c0 c1 := by
  have hsub : Tendsto (fun k => (S.sequence (C.subsequence k)).area)
      atTop (𝓝 (m64LeastAnnulusArea g c0 c1)) :=
    S.area_tendsto_infimum.comp C.subsequence_strictMono.tendsto_atTop
  exact L.area_le_liminf.trans_eq hsub.liminf_eq

structure M64FixedBoundaryH0StationarityCertificate
    (A : M64Annulus g c0 c1) : Prop where
  stationarity : M64AnnulusAreaStationary A

noncomputable def m64DouglasMorreyAttainmentCertificate_of_pipeline
    [T3Space M] [PreconnectedSpace M]
    (S : M64AnnulusMinimizingSequenceCertificate
      (g := g) (c0 := c0) (c1 := c1))
    (C : M64CourantLebesgueArzelaCertificate S)
    (H : M64HeinzHildebrandtBoundaryCertificate
      (g := g) (c0 := c0) (c1 := c1) C.limit)
  (L : M64MorreyLowerSemicontinuityCertificate S C
      (m64Annulus_of_heinzHildebrandt (c0 := c0) (c1 := c1) C.limit H)) :
    M64DouglasMorreyAttainmentCertificate
      (g := g) (c0 := c0) (c1 := c1) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous,
      fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  let A := m64Annulus_of_heinzHildebrandt
    (c0 := c0) (c1 := c1) C.limit H
  refine {
    sequence := fun k => S.sequence (C.subsequence k)
    sequence_antitone := ?_
    sequence_tendsto_infimum := ?_
    limit := A
    sequence_tendsto_limit := ?_
    limit_area_le := ?_ }
  · intro i j hij
    exact S.sequence_antitone (C.subsequence_strictMono.monotone hij)
  · exact S.area_tendsto_infimum.comp C.subsequence_strictMono.tendsto_atTop
  · intro p hp
    refine (EMetric.tendsto_nhds (α := M)).mpr ?_
    intro epsilon hepsilon
    by_cases htop : epsilon = (⊤ : ℝ≥0∞)
    · have hε := C.uniform_limit 1 zero_lt_one
      filter_upwards [hε] with k hk
      change g.edist ((S.sequence (C.subsequence k)).map p) (C.limit.map p) < epsilon
      rw [htop]
      exact lt_top_iff_ne_top.mpr
        (PoincareConjecture.RiemannianMetric.edist_ne_top g _ _)
    · have hepos : 0 < epsilon.toReal :=
        ENNReal.toReal_pos (ne_of_gt hepsilon) htop
      have hε := C.uniform_limit epsilon.toReal hepos
      filter_upwards [hε] with k hk
      change g.edist ((S.sequence (C.subsequence k)).map p) (C.limit.map p) < epsilon
      simpa only [A, ENNReal.ofReal_toReal htop] using hk p hp
  · have hsub : Tendsto (fun k => (S.sequence (C.subsequence k)).area)
        atTop (𝓝 (m64LeastAnnulusArea g c0 c1)) :=
      S.area_tendsto_infimum.comp C.subsequence_strictMono.tendsto_atTop
    exact (L.area_le_liminf.trans_eq hsub.liminf_eq)

def M64AnnulusMovingBoundaryCompetitor
    (variation : ℝ × LoopPlane → M) : Prop :=
  ∀ s : ℝ, ∃ c0' c1' : ℝ → M, ∃ B : M64Annulus g c0' c1',
    B.map = fun p => variation (s, p)

end PoincareConjecture
