import PoincareConjecture.Proofs.M47.TerminalCurvatureFiniteCoverScalar
import PoincareConjecture.Proofs.M47.TerminalCurvatureSourceCharts









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u v

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)



theorem terminalCurvature_eventually_source_point_scalar
    {ι : Type*}
    {M : ℕ → Type u} [∀ k, TopologicalSpace (M k)] [∀ k, ChartedSpace E (M k)]
    [∀ k, IsManifold (𝓡 3) ∞ (M k)] [∀ k, T2Space (M k)]
    {X : Type v} [TopologicalSpace X] [ChartedSpace E X]
    [IsManifold (𝓡 3) ∞ X] [T2Space X]
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
    (x : X) {eta : ℝ} (heta : 0 < eta) :
    ∀ᶠ k in atTop, ∀ Dk : LeviCivitaData (g k),
      |Dk.scalarCurvature (phi k x) - D.scalarCurvature x| < eta := by
  obtain ⟨i, hxi⟩ := hcoverC x
  have hKtarget : ({c i x} : Set E) ⊆ (c i).target :=
    singleton_subset_iff.mpr ((c i).map_source hxi)
  have hsourceK := (terminalCurvature_source_chart_readout U hU hmono hcoverU phi hsource
    (c i) isCompact_singleton hKtarget).2
  have hjetK (j : ℕ) : TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ j ((g k).pullbackCoefficients
        ((phi k).symm.trans (c i)).symm))
      (iteratedFDeriv ℝ j (h.pullbackCoefficients (c i).symm)) atTop {c i x} :=
    hjet i j {c i x} isCompact_singleton hKtarget
  have hscalar := terminalCurvature_eventually_scalar_on_finite_cover g h D
    (fun k => (phi k).symm) (fun _ : Unit => c i) (fun _ : Unit => {c i x})
    (fun _ => isCompact_singleton) (fun _ => hKtarget) (fun _ => hsourceK)
    (fun _ j _ => hjetK j) heta
  obtain ⟨jx, hjx⟩ := (isCompact_singleton (x := x)).elim_directed_cover U hU
    (by rw [hcoverU]; exact subset_univ _) hmono.directed_le
  filter_upwards [hscalar, eventually_ge_atTop jx] with k hk hjxk Dk
  have hxsource : x ∈ (phi k).source := by
    rw [hsource k]
    exact hmono hjxk (hjx (mem_singleton x))
  have hleft : (phi k).symm (phi k x) = x := (phi k).left_inv hxsource
  have hcovered : ∃ _ : Unit, (phi k).symm (phi k x) ∈ (c i).source ∧
      c i ((phi k).symm (phi k x)) ∈ ({c i x} : Set E) := by
    rw [hleft]
    exact ⟨(), hxi, mem_singleton _⟩
  have herr := hk Dk (phi k x) ((phi k).map_source hxsource) hcovered
  rw [hleft] at herr
  rwa [abs_sub_comm] at herr

end PoincareConjecture.M47
