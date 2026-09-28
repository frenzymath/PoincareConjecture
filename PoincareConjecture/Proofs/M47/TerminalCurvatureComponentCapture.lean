import PoincareConjecture.Proofs.M47.ComponentEstimateGeometry
import PoincareConjecture.Proofs.M47.TerminalCurvatureSourcePointScalar
import PoincareConjecture.Proofs.M47.TerminalCurvatureBallCapture

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u v

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem terminalCurvature_compact_of_component_captured
    {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold (𝓡 3) ∞ M]
    {X : Type v} [TopologicalSpace X] [ChartedSpace E X]
    [IsManifold (𝓡 3) ∞ X] [T2Space X] [ConnectedSpace X]
    (phi : PartialDiffeomorph (𝓡 3) (𝓡 3) X M ∞)
    {V : Set M} {q : M} (hV : V = connectedComponent q)
    (hcompact : IsCompact V) (hcapture : V ⊆ phi.target) :
    IsCompact (univ : Set X) := by
  let : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace E M
  let S := phi.symm '' V
  have hScompact : IsCompact S :=
    hcompact.image_of_continuousOn (phi.contMDiffOn_invFun.continuousOn.mono hcapture)
  have hVopen : IsOpen V := by
    rw [hV]
    exact isOpen_connectedComponent
  have hSopen : IsOpen S :=
    phi.toOpenPartialHomeomorph.isOpen_image_symm_of_subset_target hVopen hcapture
  have hSne : S.Nonempty := by
    refine ⟨phi.symm q, mem_image_of_mem _ ?_⟩
    rw [hV]
    exact mem_connectedComponent
  have hSclopen : IsClopen S := ⟨hScompact.isClosed, hSopen⟩
  have hSuniv : S = univ := hSclopen.eq_univ hSne
  rwa [hSuniv] at hScompact

theorem terminalCurvature_eventually_compact_of_source_component
    {ι : Type*}
    {M : ℕ → Type u} [∀ k, TopologicalSpace (M k)] [∀ k, ChartedSpace E (M k)]
    [∀ k, IsManifold (𝓡 3) ∞ (M k)] [∀ k, T2Space (M k)] [∀ k, T3Space (M k)]
    [∀ k, MeasurableSpace (M k)] [∀ k, BorelSpace (M k)]
    {X : Type v} [TopologicalSpace X] [ChartedSpace E X]
    [IsManifold (𝓡 3) ∞ X] [T2Space X] [T3Space X] [ConnectedSpace X]
    (g : ∀ k, RiemannianMetric 3 (M k)) (h : RiemannianMetric 3 X)
    (D : LeviCivitaData h)
    (U : ℕ → Set X) (hU : ∀ k, IsOpen (U k)) (hmono : Monotone U)
    (hcoverU : (⋃ k, U k) = univ)
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
    {C : ℝ} (hC : 0 < C) :
    ∀ᶠ k in atTop, ∀ Dk : LeviCivitaData (g k),
      ∀ N : SingularCComponent (g k) Dk C, phi k x ∈ N.carrier →
        IsCompact (univ : Set X) := by
  have hH := half_pos hxscalar
  obtain ⟨j, hj⟩ := hballs (C * (D.scalarCurvature x / 2) ^ (-1 / 2 : ℝ))
    (mul_pos hC (Real.rpow_pos_of_pos hH _))
  have hscalar := terminalCurvature_eventually_source_point_scalar
    g h D U hU hmono hcoverU phi hsource c hcoverC hjet x hH
  filter_upwards [hj, hscalar, eventually_ge_atTop j] with k hkball hkscalar hjk Dk N hx
  have hlo : D.scalarCurvature x / 2 ≤ Dk.scalarCurvature (phi k x) := by
    have he := (abs_lt.mp (hkscalar Dk)).1
    linarith
  have hpow := Real.rpow_le_rpow_of_nonpos hH hlo (by norm_num : (-1 / 2 : ℝ) ≤ 0)
  have hNball : N.carrier ⊆
      (g k).ball (phi k x) (C * (D.scalarCurvature x / 2) ^ (-1 / 2 : ℝ)) := by
    intro y hy
    exact (component_subset_ball N hx hy).trans_le (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left hpow hC.le))
  have hc : N.carrier ⊆ (phi k).target := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := hkball (hNball hy)
    apply (phi k).map_source
    rw [hsource k]
    exact hmono hjk hz
  exact terminalCurvature_compact_of_component_captured (phi k)
    N.component_eq N.compact hc

end PoincareConjecture.M47
