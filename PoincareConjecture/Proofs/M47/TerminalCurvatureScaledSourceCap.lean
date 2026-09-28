import PoincareConjecture.Proofs.M47.TerminalCurvatureCapturedScaledCap
import PoincareConjecture.Proofs.M47.TerminalCurvatureCapCaptureAssembly
import PoincareConjecture.Proofs.M47.TerminalCurvatureSourcePointScalar










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u v

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)



theorem terminalCurvature_eventually_scaled_cap_readout_of_source_balls
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
    (x : X)
    (hballs : ∀ R : ℝ, 0 < R → ∃ j, ∀ᶠ k in atTop,
      (rescaledMetric (g k) (Q k) (hQ k)).ball (phi k x) R ⊆ phi k '' U j)
    {epsilon C H J : ℝ} (hepsilon : 0 < epsilon) (hsmall : 2 * epsilon < 1 / 2)
    (hC : 0 < C) (hH : 0 < H) :
    ∀ᶠ k in atTop, ∀ N : CapCertificate (g k), N.epsilon = epsilon →
      N.cap_constant ≤ C → phi k x ∈ N.core →
      H ≤ (rescaledMetric_connection (g k) N.connection (Q k) (hQ k)).scalarCurvature
        (phi k x) →
      (rescaledMetric_connection (g k) N.connection (Q k) (hQ k)).scalarCurvature
        (phi k x) ≤ J →
      ∃ W : EpsilonNeck h,
        W.epsilon = 2 * epsilon ∧ W.connection = D ∧
        W.center = (phi k).symm N.end_neck.center ∧
        D.scalarCurvature x ≤ (4 * max 1 C) * D.scalarCurvature W.center ∧
        W.coordinate_map = (phi k).symm ∘ N.end_neck.coordinate_map := by
  classical
  have hR : 0 < C * H ^ (-1 / 2 : ℝ) := mul_pos hC (Real.rpow_pos_of_pos hH _)
  obtain ⟨j, hj⟩ := hballs (C * H ^ (-1 / 2 : ℝ)) hR
  obtain ⟨s, hsne, index, K, hK, hKtarget, hfiniteCover⟩ :=
    terminalCurvature_exists_finite_original_chart_buffers c (hcompact j)
      ⟨p, subset_closure (hp j)⟩ (fun y _ => hcoverC y)
  obtain ⟨z, hzs⟩ := hsne
  let : Nonempty s := ⟨⟨z, hzs⟩⟩
  have hsourceK (i : s) : ∀ᶠ k in atTop,
      K i ⊆ ((phi k).symm.trans (c (index i))).target :=
    (terminalCurvature_source_chart_readout U hU hmono hcoverU phi hsource
      (c (index i)) (hK i) (hKtarget i)).2
  have hjetsK (i : s) (m : ℕ) : TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m ((rescaledMetric (g k) (Q k) (hQ k)).pullbackCoefficients
        ((phi k).symm.trans (c (index i))).symm))
      (iteratedFDeriv ℝ m (h.pullbackCoefficients (c (index i)).symm)) atTop (K i) :=
    hjet (index i) m (K i) (hK i) (hKtarget i)
  have hcap := terminalCurvature_eventually_captured_scaled_cap_readout g Q hQ h D
    (fun k => (phi k).symm) (fun i : s => c (index i)) K hK hKtarget hsourceK hjetsK
      hepsilon hsmall hC hH (J := J)
  obtain ⟨jx, hjx⟩ := (isCompact_singleton (x := x)).elim_directed_cover U hU
    (by rw [hcoverU]; exact subset_univ _) hmono.directed_le
  filter_upwards [hcap, hj, eventually_ge_atTop j, eventually_ge_atTop jx]
    with k hkcap hkball hjk hjxk N hN hNC hx hlo hhi
  have hUj : U j ⊆ (phi k).source := by
    rw [hsource k]
    exact hmono hjk
  have hNball := terminalCurvature_scaled_cap_carrier_subset_ball N (hQ k) hNC hH hx hlo
  have hNcapture : N.carrier ⊆ phi k '' U j := hNball.trans hkball
  obtain ⟨hNtarget, hNinverse, _⟩ := terminalCurvature_inverse_image_compact
    (phi k) hUj (hcompact j) hNcapture
  have hNcover (y : M k) (hy : y ∈ N.carrier) :
      ∃ i : s, (phi k).symm y ∈ (c (index i)).source ∧
        c (index i) ((phi k).symm y) ∈ K i :=
    hfiniteCover _ (subset_closure (hNinverse (mem_image_of_mem (phi k).symm hy)))
  obtain ⟨W, hWepsilon, hWcenter, hWconnection, hWscalar, _, hWmap⟩ :=
    hkcap N hN hNC (phi k x) hx hlo hhi hNtarget hNcover
  have hxsource : x ∈ (phi k).source := by
    rw [hsource k]
    exact hmono hjxk (hjx (mem_singleton x))
  have hleft : (phi k).symm (phi k x) = x := (phi k).left_inv hxsource
  rw [hleft] at hWscalar
  exact ⟨W, hWepsilon, hWconnection, hWcenter, hWscalar, hWmap⟩



theorem terminalCurvature_eventually_scaled_source_cap_readout
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
        W.coordinate_map = (phi k).symm ∘ N.end_neck.coordinate_map := by
  have hcap := terminalCurvature_eventually_scaled_cap_readout_of_source_balls
    g Q hQ h D U hU hmono hcoverU hcompact p hp phi hsource c hcoverC hjet x hballs
      hepsilon hsmall hC (half_pos hxscalar) (J := D.scalarCurvature x + 1)
  have heta : 0 < min (D.scalarCurvature x / 2) 1 :=
    lt_min (half_pos hxscalar) zero_lt_one
  have hscalar := terminalCurvature_eventually_source_point_scalar
    (fun k => rescaledMetric (g k) (Q k) (hQ k)) h D
    U hU hmono hcoverU phi hsource c hcoverC hjet x heta
  filter_upwards [hcap, hscalar] with k hkcap hkscalar N hN hNC hx
  have herr := abs_lt.mp (hkscalar
    (rescaledMetric_connection (g k) N.connection (Q k) (hQ k)))
  have hhalf := min_le_left (D.scalarCurvature x / 2) (1 : ℝ)
  have hone := min_le_right (D.scalarCurvature x / 2) (1 : ℝ)
  exact hkcap N hN hNC hx (by linarith [herr.1]) (by linarith [herr.2])

end PoincareConjecture.M47
