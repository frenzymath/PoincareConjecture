import PoincareConjecture.Proofs.M47.TerminalRegularStageFamily
import PoincareConjecture.Proofs.M47.TerminalRegularPhysicalCharts
import PoincareConjecture.Proofs.M47.TerminalSourceCountableCoreCover
import PoincareConjecture.Proofs.M47.TerminalCurvatureActualUniformScalar
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.Scalar.SharpBounds










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology

universe u v

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)

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
local notation "gSource" => (fun k : ℕ =>
  RiemannianMetric.connectedComponentMetric (gPhysical k) (center k))
local notation "e" => (fun (k j : ℕ) (hjk : j ≤ k) => TerminalRegularStageData.maps (data k j hjk))
local notation "point" => (fun k : ℕ => (Subtype.mk (center k) mem_connectedComponent : M k))




theorem terminalSource_regular_physical_scalar_ceiling
    {X : Type v} [TopologicalSpace X] [ChartedSpace E X]
    [IsManifold (𝓡 3) ∞ X] [T2Space X]
    (g0 : RiemannianMetric 3 X) (D0 : LeviCivitaData g0)
    (nu : ℕ → ℕ) (hnu : StrictMono nu)
    (f0 : ℕ → PartialDiffeomorph (𝓡 3) (𝓡 3) E X ∞)
    {B0 : ℝ} (hnorm : ∀ x, D0.curvatureTensorNorm x ≤ B0) :
    letI : ∀ k, MetricSpace (M k) :=
      fun k => terminalSourceComponentMetricSpace (gPhysical k) (center k)
    let label := terminalSourceCountableLabel N
    let U := fun i => terminalSourceCountableDomain (rho (label i).1)
    letI : ∀ i, Nonempty (U i) := fun i => ⟨terminalSourceCountableZero (hrho (label i).1)⟩
    let total := fun k i => terminalSourceCountableMap hrho e k (label i).1 (label i).2
    (∀ i, (f0 i).source = U i) →
    (∀ i m C, IsCompact C → C ⊆ U i → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m ((gSource (nu k)).pullbackCoefficients
        (ChartDistance.chartParametrization (fun i => (U i : Set E))
          (fun i => (U i).isOpen) (total (nu k) i))))
      (iteratedFDeriv ℝ m (g0.pullbackCoefficients (f0 i))) atTop C) →
    let K0 := max 1 (3 * B0)
    1 ≤ K0 ∧ ∀ a : ℝ, 0 < a → ∀ᶠ k in atTop,
      ∀ z ∈ ((F (nu k)).metric (base (nu k))).ball (center (nu k)) (a / Real.sqrt (Q (nu k))),
        ((F (nu k)).connection (base (nu k))).scalarCurvature z ≤ (2 * K0) * Q (nu k) := by
  classical
  let : ∀ k, MetricSpace (M k) :=
    fun k => terminalSourceComponentMetricSpace (gPhysical k) (center k)
  let label := terminalSourceCountableLabel N
  let U := fun i => terminalSourceCountableDomain (rho (label i).1)
  let : ∀ i, Nonempty (U i) := fun i => ⟨terminalSourceCountableZero (hrho (label i).1)⟩
  let total := fun k i => terminalSourceCountableMap hrho e k (label i).1 (label i).2
  dsimp only
  intro hsource0 hjets
  let K0 := max 1 (3 * B0)
  have hK0 : 0 < K0 := zero_lt_one.trans_le (le_max_left _ _)
  have hscalar (x : X) : D0.scalarCurvature x ≤ K0 :=
    (le_abs_self _).trans ((D0.abs_scalarCurvature_le_curvatureTensorNorm_sharp x).trans
      ((mul_le_mul_of_nonneg_left (hnorm x) (by norm_num : (0 : ℝ) ≤ 3)).trans
        (le_max_right _ _)))
  have hgeometry := terminalSourceCountableMap_geometry hrho e
    (fun k j hjk i => ((data k j hjk).geometry i).1)
    (fun k j hjk i => ((data k j hjk).geometry i).2)
  choose f hf hsource htarget using fun i k => terminalSource_regular_physical_chart
    U i (total k i) (hgeometry k (label i).1 (label i).2).1
      (hgeometry k (label i).1 (label i).2).2
  let D : ∀ k, LeviCivitaData (gSource k) := fun k => (gSource k).leviCivitaData
  have hzero (k : ℕ) : e k 0 (Nat.zero_le k) 0 (terminalSourceCountableZero (hrho 0)) = point k :=
    (data k 0 (Nat.zero_le k)).zero
  have hcofinal (a : ℝ) (_ha : 0 < a) : ∃ j : ℕ, a ≤ (j : ℝ) + 1 := by
    obtain ⟨j, hj⟩ := exists_nat_gt a
    exact ⟨j, by linarith⟩
  have hcover (k j : ℕ) (hjk : j ≤ k) : Metric.ball (point k) ((j : ℝ) + 1) ⊆
      ⋃ i, e k j hjk i '' terminalSourceCountableCore (rho j) := by
    obtain ⟨core, _hcore, hcoreEq, hcover⟩ := (data k j hjk).cores
    have hcore : core = terminalSourceCountableCore (rho j) := Set.ext hcoreEq
    rwa [hcore] at hcover
  have hcores := (terminalSourceCountable_core_covers hrho e point hzero
    (fun j : ℕ => (j : ℝ) + 1) hcofinal hcover).2
  refine ⟨le_max_left _ _, ?_⟩
  intro a ha
  obtain ⟨s, core, _hcoreEq, hcompact, hcapture⟩ := hcores a ha
  let C := fun i => (Subtype.val : U i → E) '' core i
  have hCU (i : ℕ) : C i ⊆ U i := by
    rintro _ ⟨x, _, rfl⟩
    exact x.property
  have hCcompact (i : ℕ) (hi : i ∈ s) : IsCompact (C i) :=
    (hcompact i hi).image continuous_subtype_val
  have herrors : ∀ᶠ k in atTop, ∀ i ∈ s, ∀ z ∈ C i,
      |(D (nu k)).scalarCurvature (f i (nu k) z) - D0.scalarCurvature (f0 i z)| < K0 := by
    apply (Filter.eventually_all_finset s).mpr
    intro i hi
    apply terminalCurvature_eventually_actual_scalar_error (fun k => D (nu k)) D0
      (fun k => f i (nu k)) (f0 i) (hCcompact i hi)
    · rw [hsource0]
      exact hCU i
    · exact Eventually.of_forall (fun k => by rw [hsource]; exact hCU i)
    · intro m _hm
      simpa only [hf] using hjets i m (C i) (hCcompact i hi) (hCU i)
    · exact hK0
  filter_upwards [hnu.tendsto_atTop.eventually hcapture, herrors] with k hk he z hz
  have hz' : z ∈ (RiemannianMetric.ball (gPhysical (nu k)) (center (nu k)) a) := by
    rw [terminalSourceNormal_scaled_ball]
    exact hz
  rw [← (terminalSourceComponent_balls (gPhysical (nu k)) (center (nu k)) (point (nu k)) a).2.1]
    at hz'
  obtain ⟨y, hy, hyz⟩ := hz'
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hk hy)
  obtain ⟨his, x, hx, hxy⟩ := mem_iUnion.mp hi
  have hfx : f i (nu k) x.val = y := by
    rw [hf, ChartDistance.chartParametrization_apply]
    exact hxy
  have herror := (abs_lt.mp (he i his x.val ⟨x, hx, rfl⟩)).2
  rw [hfx, terminalSource_regular_component_scalar
    ((F (nu k)).metric (base (nu k))) ((F (nu k)).connection (base (nu k)))
    (Q (nu k)) (data (nu k) 0 (Nat.zero_le _)).original.scale_pos (center (nu k)), hyz]
    at herror
  apply (div_le_iff₀ (data (nu k) 0 (Nat.zero_le _)).original.scale_pos).mp
  linarith [hscalar (f0 i x.val)]

end Family

end PoincareConjecture.M47
