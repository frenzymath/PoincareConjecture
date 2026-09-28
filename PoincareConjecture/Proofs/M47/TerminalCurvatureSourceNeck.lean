import PoincareConjecture.Proofs.M47.TerminalCurvatureNeckLocalization
import PoincareConjecture.Proofs.M47.TerminalCurvatureCapCaptureAssembly
import PoincareConjecture.Proofs.M47.TerminalCurvatureSourcePointScalar

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u v

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem terminalCurvature_eventually_source_neck_readout
    {ι : Type*}
    {M : ℕ → Type u} [∀ k, TopologicalSpace (M k)] [∀ k, ChartedSpace E (M k)]
    [∀ k, IsManifold (𝓡 3) ∞ (M k)] [∀ k, T2Space (M k)] [∀ k, T3Space (M k)]
    [∀ k, MeasurableSpace (M k)] [∀ k, BorelSpace (M k)]
    {X : Type v} [TopologicalSpace X] [ChartedSpace E X]
    [IsManifold (𝓡 3) ∞ X] [T2Space X] [T3Space X]
    (g : ∀ k, RiemannianMetric 3 (M k)) (h : RiemannianMetric 3 X)
    (D : LeviCivitaData h)
    (U : ℕ → Set X) (hU : ∀ k, IsOpen (U k)) (hmono : Monotone U)
    (hcoverU : (⋃ k, U k) = univ) (hcompact : ∀ j, IsCompact (closure (U j)))
    (p : X) (hp : ∀ j, p ∈ U j)
    (phi : ∀ k, PartialDiffeomorph (𝓡 3) (𝓡 3) X (M k) ∞)
    (hsource : ∀ k, (phi k).source = U k)
    (c : ι → PartialDiffeomorph (𝓡 3) (𝓡 3) X E ∞)
    (hcoverC : ∀ x : X, ∃ i, x ∈ (c i).source)
    (hjet : ∀ i j K, IsCompact K → K ⊆ (c i).target → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ j ((g k).pullbackCoefficients (phi k ∘ (c i).symm)))
      (iteratedFDeriv ℝ j (h.pullbackCoefficients (c i).symm)) atTop K)
    (x : X) (hxscalar : 0 < D.scalarCurvature x)
    (hballs : ∀ R : ℝ, 0 < R → ∃ j, ∀ᶠ k in atTop,
      (g k).ball (phi k x) R ⊆ phi k '' U j)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hsmall : 2 * epsilon < 1 / 2) :
    ∀ᶠ k in atTop, ∀ N : EpsilonNeck (g k), N.epsilon = epsilon →
      N.center = phi k x →
      ∃ W : EpsilonNeck h,
        W.epsilon = 2 * epsilon ∧ W.connection = D ∧ W.center = x ∧
        W.coordinate_map = (phi k).symm ∘ N.coordinate_map := by
  classical
  let H := D.scalarCurvature x / 2
  have hH : 0 < H := half_pos hxscalar
  let R := H ^ (-1 / 2 : ℝ) * Real.sqrt (1 + epsilon) *
    (2 * epsilon⁻¹ + Real.sqrt 2 * (Real.pi + 1)) + 1
  have hR : 0 < R := by dsimp [R]; positivity
  obtain ⟨j, hj⟩ := hballs R hR
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
      (fun k => iteratedFDeriv ℝ m ((g k).pullbackCoefficients
        ((phi k).symm.trans (c (index i))).symm))
      (iteratedFDeriv ℝ m (h.pullbackCoefficients (c (index i)).symm)) atTop (K i) :=
    hjet (index i) m (K i) (hK i) (hKtarget i)
  have hneck := terminalCurvature_eventually_image_neck_on_finite_cover g h D
    (fun k => (phi k).symm) (fun i : s => c (index i)) K hK hKtarget hsourceK hjetsK
      hepsilon hsmall hH (H := D.scalarCurvature x + 1)
  have heta : 0 < min H 1 := lt_min hH zero_lt_one
  have hscalar := terminalCurvature_eventually_source_point_scalar
    g h D U hU hmono hcoverU phi hsource c hcoverC hjet x heta
  obtain ⟨jx, hjx⟩ := (isCompact_singleton (x := x)).elim_directed_cover U hU
    (by rw [hcoverU]; exact subset_univ _) hmono.directed_le
  filter_upwards [hneck, hscalar, hj, eventually_ge_atTop j, eventually_ge_atTop jx]
    with k hkneck hkscalar hkball hjk hjxk N hN hcenter
  have herr := abs_lt.mp (hkscalar N.connection)
  have hhalf := min_le_left H (1 : ℝ)
  have hone := min_le_right H (1 : ℝ)
  have hlo : H ≤ N.connection.scalarCurvature N.center := by
    rw [hcenter]
    dsimp [H] at hhalf ⊢
    linarith [herr.1]
  have hhi : N.connection.scalarCurvature N.center ≤ D.scalarCurvature x + 1 := by
    rw [hcenter]
    linarith [herr.2]
  have hNball : N.carrier ⊆ (g k).ball (phi k x) R := by
    simpa only [hN, hcenter] using terminalCurvature_neck_carrier_subset_ball N hH hlo
  have hUj : U j ⊆ (phi k).source := by
    rw [hsource k]
    exact hmono hjk
  obtain ⟨hNtarget, hNinverse, _⟩ := terminalCurvature_inverse_image_compact
    (phi k) hUj (hcompact j) (hNball.trans hkball)
  have hNcover (y : M k) (hy : y ∈ N.carrier) :
      ∃ i : s, (phi k).symm y ∈ (c (index i)).source ∧
        c (index i) ((phi k).symm y) ∈ K i :=
    hfiniteCover _ (subset_closure (hNinverse (mem_image_of_mem (phi k).symm hy)))
  obtain ⟨W, hWepsilon, hWcenter, hWconnection, _, hWmap⟩ :=
    hkneck N hN hlo hhi hNtarget hNcover
  have hxsource : x ∈ (phi k).source := by
    rw [hsource k]
    exact hmono hjxk (hjx (mem_singleton x))
  have hleft : (phi k).symm (phi k x) = x := (phi k).left_inv hxsource
  rw [hcenter, hleft] at hWcenter
  exact ⟨W, hWepsilon, hWconnection, hWcenter, hWmap⟩

end PoincareConjecture.M47
