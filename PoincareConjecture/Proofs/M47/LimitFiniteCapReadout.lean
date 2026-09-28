import PoincareConjecture.Proofs.M47.LimitFiniteCapDistance
import PoincareConjecture.Proofs.M47.TerminalCurvatureScaledSourceCap
import PoincareConjecture.Proofs.M47.TerminalCurvatureEarlierTangent

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal

universe u v

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)

private theorem half_scalar_radius_le {R C : ℝ} (hR : 0 < R) (hC : 0 < C) :
    2 * C * (R / 2) ^ (-1 / 2 : ℝ) ≤ 4 * C * R ^ (-1 / 2 : ℝ) := by
  have heq : (R / 2) ^ (-1 / 2 : ℝ) = Real.sqrt 2 * R ^ (-1 / 2 : ℝ) := by
    have h := (terminalCurvature_scaled_scalar_radius
      (Q := 2) (by norm_num) (half_pos hR)).symm
    rw [show 2 * (R / 2) = R by ring] at h
    exact h
  rw [heq]
  have hs : Real.sqrt 2 ≤ 2 := by norm_num
  have hm := mul_le_mul_of_nonneg_right hs (Real.rpow_nonneg hR.le (-1 / 2))
  have hm' := mul_le_mul_of_nonneg_left hm (by positivity : 0 ≤ 2 * C)
  calc
    2 * C * (Real.sqrt 2 * R ^ (-1 / 2 : ℝ)) ≤
        2 * C * (2 * R ^ (-1 / 2 : ℝ)) := hm'
    _ = 4 * C * R ^ (-1 / 2 : ℝ) := by ring

theorem limitFinite_eventually_scaled_cap_nearby_readout
    {ι : Type*}
    {M : ℕ → Type u} [∀ k, TopologicalSpace (M k)] [∀ k, ChartedSpace E (M k)]
    [∀ k, IsManifold (𝓡 3) ∞ (M k)] [∀ k, T2Space (M k)] [∀ k, T3Space (M k)]
    [∀ k, MeasurableSpace (M k)] [∀ k, BorelSpace (M k)]
    {X : Type v} [TopologicalSpace X] [ChartedSpace E X]
    [IsManifold (𝓡 3) ∞ X] [T2Space X] [T3Space X]
    (g : ∀ k, RiemannianMetric 3 (M k)) (Q : ℕ → ℝ) (hQ : ∀ k, 0 < Q k)
    (h : RiemannianMetric 3 X) (D : LeviCivitaData h)
    (U : ℕ → Set X) (hU : ∀ k, IsOpen (U k)) (hmono : Monotone U)
    (hcoverU : (⋃ k, U k) = univ) (hcompact : ∀ j, IsCompact (closure (U j)))
    (p : X) (hp : ∀ j, p ∈ U j)
    (phi : ∀ k, PartialDiffeomorph (𝓡 3) (𝓡 3) X (M k) ∞)
    (hsource : ∀ k, (phi k).source = U k)
    (c : ι → PartialDiffeomorph (𝓡 3) (𝓡 3) X E ∞)
    (hcoverC : ∀ x : X, ∃ i, x ∈ (c i).source)
    (hjet : ∀ i j K, IsCompact K → K ⊆ (c i).target → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ j ((rescaledMetric (g k) (Q k) (hQ k)).pullbackCoefficients
        (phi k ∘ (c i).symm)))
      (iteratedFDeriv ℝ j (h.pullbackCoefficients (c i).symm)) atTop K)
    (x : X) (hxscalar : 0 < D.scalarCurvature x)
    (hballs : ∀ R : ℝ, 0 < R → ∃ j, ∀ᶠ k in atTop,
      (rescaledMetric (g k) (Q k) (hQ k)).ball (phi k x) R ⊆ phi k '' U j)
    {epsilon C : ℝ} (hepsilon : 0 < epsilon) (hsmall : 2 * epsilon < 1 / 2)
    (hC : 0 < C) :
    ∀ᶠ k in atTop, ∀ N : CapCertificate (g k), N.epsilon = epsilon →
      N.cap_constant ≤ C → phi k x ∈ N.core →
      ∃ W : EpsilonNeck h,
        W.epsilon = 2 * epsilon ∧ W.connection = D ∧
        W.center = (phi k).symm N.end_neck.center ∧
        D.scalarCurvature x ≤ (4 * max 1 C) * D.scalarCurvature W.center ∧
        h.edist x W.center < ENNReal.ofReal (4 * C * D.scalarCurvature x ^ (-1 / 2 : ℝ)) ∧
        W.coordinate_map = (phi k).symm ∘ N.end_neck.coordinate_map := by
  classical
  let H := D.scalarCurvature x / 2
  have hH : 0 < H := half_pos hxscalar
  have hR : 0 < C * H ^ (-1 / 2 : ℝ) := mul_pos hC (Real.rpow_pos_of_pos hH _)
  obtain ⟨j, hj⟩ := hballs (C * H ^ (-1 / 2 : ℝ)) hR
  have hmetric := terminalCurvature_eventually_compact_tangent
    (fun k => rescaledMetric (g k) (Q k) (hQ k)) h U hU hmono hcoverU
    phi hsource c hcoverC (fun i K hK hKt => hjet i 0 K hK hKt)
      (closure (U j)) (hcompact j)
  have hscalar := terminalCurvature_eventually_source_point_scalar
    (fun k => rescaledMetric (g k) (Q k) (hQ k)) h D U hU hmono hcoverU
    phi hsource c hcoverC hjet x hH
  have hneck := terminalCurvature_eventually_scaled_source_cap_readout g Q hQ h D
    U hU hmono hcoverU hcompact p hp phi hsource c hcoverC hjet x hxscalar hballs
      hepsilon hsmall hC
  obtain ⟨jx, hjx⟩ := (isCompact_singleton (x := x)).elim_directed_cover U hU
    (by rw [hcoverU]; exact subset_univ _) hmono.directed_le
  filter_upwards [hneck, hscalar, hmetric, hj, eventually_ge_atTop jx]
    with k hkneck hkscalar hkmetric hkball hjxk N hN hNC hx
  let DQ := rescaledMetric_connection (g k) N.connection (Q k) (hQ k)
  have hfloor : H ≤ DQ.scalarCurvature (phi k x) := by
    have herr := (abs_lt.mp (hkscalar DQ)).1
    dsimp only [H] at herr ⊢
    linarith
  have hphysical : Q k * H ≤ N.connection.scalarCurvature (phi k x) := by
    have h := hfloor
    simp only [DQ, rescaledMetric_scalarCurvature] at h
    have hh := (le_div_iff₀ (hQ k)).mp
      (show H ≤ N.connection.scalarCurvature (phi k x) / Q k by
        simpa only [div_eq_mul_inv, mul_comm] using h)
    simpa only [mul_comm] using hh
  have hUj : U j ⊆ (phi k).source := by
    rw [hsource k]
    exact subset_closure.trans hkmetric.1
  have hcapBall := terminalCurvature_scaled_cap_carrier_subset_ball N (hQ k) hNC hH hx hfloor
  obtain ⟨hcaptured, hinverse, _⟩ := terminalCurvature_inverse_image_compact
    (phi k) hUj (hcompact j) (hcapBall.trans hkball)
  have hxsource : x ∈ (phi k).source := by
    rw [hsource k]
    exact hmono hjxk (hjx (mem_singleton x))
  have hdistance := limitFinite_cap_end_distance_of_forward_bound h N (phi k)
    (hQ k) hNC hH hxsource hx hphysical hcaptured
    (fun z hz w => hkmetric.2 _
      (subset_closure (hinverse (mem_image_of_mem (phi k).symm hz))) w)
  obtain ⟨W, hWe, hWD, hWcenter, hWscalar, hWmap⟩ := hkneck N hN hNC hx
  refine ⟨W, hWe, hWD, hWcenter, hWscalar, ?_, hWmap⟩
  rw [hWcenter]
  exact hdistance.trans_le (ENNReal.ofReal_le_ofReal (half_scalar_radius_le hxscalar hC))

end PoincareConjecture.M47
