import PoincareConjecture.Proofs.M47.TerminalCurvatureScaledCapScalar
import PoincareConjecture.Proofs.M47.TerminalCurvatureFiniteCoverNeck
import PoincareConjecture.Proofs.M47.TerminalCurvatureFiniteCoverScalar

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u v

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem terminalCurvature_eventually_captured_scaled_cap_readout
    {ι : Type*} [Finite ι] [Nonempty ι]
    {M : ℕ → Type u} [∀ k, TopologicalSpace (M k)] [∀ k, ChartedSpace E (M k)]
    [∀ k, IsManifold (𝓡 3) ∞ (M k)] [∀ k, T2Space (M k)] [∀ k, T3Space (M k)]
    [∀ k, MeasurableSpace (M k)] [∀ k, BorelSpace (M k)]
    {X : Type v} [TopologicalSpace X] [ChartedSpace E X]
    [IsManifold (𝓡 3) ∞ X] [T2Space X]
    (g : ∀ k, RiemannianMetric 3 (M k)) (Q : ℕ → ℝ) (hQ : ∀ k, 0 < Q k)
    (h : RiemannianMetric 3 X) (D : LeviCivitaData h)
    (psi : ∀ k, PartialDiffeomorph (𝓡 3) (𝓡 3) (M k) X ∞)
    (c : ι → PartialDiffeomorph (𝓡 3) (𝓡 3) X E ∞)
    (K : ι → Set E) (hK : ∀ i, IsCompact (K i))
    (hKtarget : ∀ i, K i ⊆ (c i).target)
    (hsource : ∀ i, ∀ᶠ k in atTop, K i ⊆ ((psi k).trans (c i)).target)
    (hjet : ∀ i j, TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ j ((rescaledMetric (g k) (Q k) (hQ k)).pullbackCoefficients
        ((psi k).trans (c i)).symm))
      (iteratedFDeriv ℝ j (h.pullbackCoefficients (c i).symm)) atTop (K i))
    {epsilon C H J : ℝ} (hepsilon : 0 < epsilon) (hsmall : 2 * epsilon < 1 / 2)
    (hC : 0 < C) (hH : 0 < H) :
    ∀ᶠ k in atTop, ∀ N : CapCertificate (g k), N.epsilon = epsilon →
      N.cap_constant ≤ C → ∀ x ∈ N.core,
      H ≤ (rescaledMetric_connection (g k) N.connection (Q k) (hQ k)).scalarCurvature x →
      (rescaledMetric_connection (g k) N.connection (Q k) (hQ k)).scalarCurvature x ≤ J →
      N.carrier ⊆ (psi k).source →
      (∀ z ∈ N.carrier, ∃ i, psi k z ∈ (c i).source ∧ c i (psi k z) ∈ K i) →
      ∃ W : EpsilonNeck h,
        W.epsilon = 2 * epsilon ∧ W.center = psi k N.end_neck.center ∧
        W.connection = D ∧
        D.scalarCurvature (psi k x) ≤ (4 * max 1 C) * D.scalarCurvature W.center ∧
        W.carrier = psi k '' N.end_neck.region (-(2 * epsilon)⁻¹) (2 * epsilon)⁻¹ ∧
        W.coordinate_map = psi k ∘ N.end_neck.coordinate_map := by
  let gQ := fun k => rescaledMetric (g k) (Q k) (hQ k)
  have hneck := terminalCurvature_eventually_image_neck_on_finite_cover
    gQ h D psi c K hK hKtarget hsource hjet hepsilon hsmall
      (div_pos hH hC) (H := C * J)
  have herror : 0 < H / (4 * max 1 C) :=
    div_pos hH (mul_pos (by norm_num) (zero_lt_one.trans_le (le_max_left _ _)))
  have hscalar := terminalCurvature_eventually_scalar_on_finite_cover
    gQ h D psi c K hK hKtarget hsource (fun i j _ => hjet i j) herror
  filter_upwards [hneck, hscalar] with k hkneck hkscalar N hN hNC x hx hlo hhi hNsource hcover
  let DQ := rescaledMetric_connection (g k) N.connection (Q k) (hQ k)
  let NQ := N.end_neck.rescale (Q k) (hQ k)
  have hDQ : NQ.connection = DQ := by
    change rescaledMetric_connection (g k) N.end_neck.connection (Q k) (hQ k) = _
    rw [N.end_neck_connection]
  have hxN := N.core_subset_carrier' hx
  have hendN : N.end_neck.center ∈ N.carrier :=
    N.end_neck_subset (N.end_neck.central_sphere_subset N.end_neck.center_on_central_sphere)
  obtain ⟨hendpos, hendlo, hendhi, hcompare⟩ :=
    terminalCurvature_scaled_cap_scalar_bounds N (hQ k) hNC hx hlo hhi
  have hNQepsilon : NQ.epsilon = epsilon := N.end_neck_epsilon.trans hN
  have hNQlo : H / C ≤ NQ.connection.scalarCurvature NQ.center := by
    rw [hDQ]
    exact hendlo
  have hNQhi : NQ.connection.scalarCurvature NQ.center ≤ C * J := by
    rw [hDQ]
    exact hendhi
  obtain ⟨W, hWepsilon, hWcenter, hWconnection, hWcarrier, hWmap⟩ :=
    hkneck NQ hNQepsilon hNQlo hNQhi
      (N.end_neck_subset.trans hNsource) (fun z hz => hcover z (N.end_neck_subset hz))
  have hratio := terminalCurvature_scalar_ratio_of_errors hendpos hcompare hlo
    (hkscalar DQ x (hNsource hxN) (hcover x hxN)).le
    (hkscalar DQ N.end_neck.center (hNsource hendN) (hcover _ hendN)).le
  refine ⟨W, hWepsilon, hWcenter, hWconnection, ?_, hWcarrier, hWmap⟩
  rw [hWcenter]
  exact hratio.2

end PoincareConjecture.M47
