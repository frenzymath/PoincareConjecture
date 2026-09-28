import PoincareConjecture.Proofs.M47.TerminalCurvatureActualUniformScalar
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.Scalar.SharpBounds
import PoincareConjecture.Definitions.Ch11.BlowupLimits

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u v

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem terminalCommonInterval_terminal_scalar
    (V : GeneralizedBlowupSequence.{u})
    {M : ℕ → ℕ → Type u} [∀ i k, TopologicalSpace (M i k)]
    [∀ i k, ChartedSpace E (M i k)] [∀ i k, IsManifold (𝓡 3) ∞ (M i k)]
    [∀ i k, T2Space (M i k)]
    {X : Type v} [TopologicalSpace X] [ChartedSpace E X]
    [IsManifold (𝓡 3) ∞ X] [T2Space X]
    {g : ∀ i k, RiemannianMetric 3 (M i k)} (D : ∀ i k, LeviCivitaData (g i k))
    {g0 : RiemannianMetric 3 X} (D0 : LeviCivitaData g0)
    (f : ∀ i k, PartialDiffeomorph (𝓡 3) (𝓡 3) E (M i k) ∞)
    (f0 : ℕ → PartialDiffeomorph (𝓡 3) (𝓡 3) E X ∞)
    (actual : ∀ i k, M i k → ((V.flow k).slice (V.base k).1).carrier)
    (hread : ∀ i, ∀ᶠ k in atTop, ∀ z,
      (D i k).scalarCurvature z =
        (V.flow k).scalar ⟨(V.base k).1, actual i k z⟩ / V.scale k)
    (hsource : ∀ i K, IsCompact K → K ⊆ (f0 i).source →
      ∀ᶠ k in atTop, K ⊆ (f i k).source)
    (hjet : ∀ i K, IsCompact K → K ⊆ (f0 i).source → ∀ j ≤ 2,
      TendstoUniformlyOn
        (fun k => iteratedFDeriv ℝ j ((g i k).pullbackCoefficients (f i k)))
        (iteratedFDeriv ℝ j (g0.pullbackCoefficients (f0 i))) atTop K)
    (hcover : ∀ A : ℝ, 0 < A → ∃ s : Finset ℕ, ∃ K : ℕ → Set E,
      (∀ i ∈ s, IsCompact (K i) ∧ K i ⊆ (f0 i).source) ∧
      ∀ᶠ k in atTop, ∀ y ∈ V.baseBall k A,
        ∃ i ∈ s, ∃ z ∈ K i, actual i k (f i k z) = y)
    {B0 : ℝ} (hnorm : ∀ z, D0.curvatureTensorNorm z ≤ B0) :
    let K0 := max 1 (3 * B0)
    1 ≤ K0 ∧ ∀ A : ℝ, 0 < A → ∀ᶠ k in atTop,
      ∀ y ∈ V.baseBall k A,
        (V.flow k).scalar ⟨(V.base k).1, y⟩ ≤ (2 * K0) * V.scale k := by
  let K0 := max 1 (3 * B0)
  have hK : 0 < K0 := zero_lt_one.trans_le (le_max_left _ _)
  have hscalar (z : X) : D0.scalarCurvature z ≤ K0 :=
    (le_abs_self _).trans ((D0.abs_scalarCurvature_le_curvatureTensorNorm_sharp z).trans
      ((mul_le_mul_of_nonneg_left (hnorm z) (by norm_num : (0 : ℝ) ≤ 3)).trans
        (le_max_right _ _)))
  refine ⟨le_max_left _ _, ?_⟩
  intro A hA
  obtain ⟨s, K, hKsource, hcapture⟩ := hcover A hA
  have herrors : ∀ᶠ k in atTop, ∀ i ∈ s, ∀ z ∈ K i,
      |(V.flow k).scalar ⟨(V.base k).1, actual i k (f i k z)⟩ / V.scale k -
        D0.scalarCurvature (f0 i z)| < K0 := by
    apply (Filter.eventually_all_finset s).mpr
    intro i hi
    have he := terminalCurvature_eventually_actual_scalar_error (D i) D0 (f i) (f0 i)
      (hKsource i hi).1 (hKsource i hi).2
      (hsource i (K i) (hKsource i hi).1 (hKsource i hi).2)
      (hjet i (K i) (hKsource i hi).1 (hKsource i hi).2) hK
    filter_upwards [he, hread i] with k hk hr z hz
    simpa only [hr] using hk z hz
  filter_upwards [hcapture, herrors] with k hk he y hy
  obtain ⟨i, hi, z, hz, hzy⟩ := hk y hy
  have herror := (abs_lt.mp (he i hi z hz)).2
  rw [hzy] at herror
  apply (div_le_iff₀ (V.base_scalar_pos k)).mp
  change (V.flow k).scalar ⟨(V.base k).1, y⟩ / V.scale k ≤ 2 * K0
  linarith [hscalar (f0 i z)]

end PoincareConjecture.M47
