import PoincareConjecture.Proofs.M47.TerminalRegularStageFamily
import PoincareConjecture.Proofs.M47.TerminalCurvatureActualUniformScalar










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology

universe u v

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)



theorem terminalSource_regular_scalar_one
    (S : RepairedControlledSchedulesData.{u})
    (B : M47ComponentAnalyticBounds.{u} S.setup.C) (p : SurgeryParameterPrefix S.constants)
    (F : ℕ → SurgeryFlowData.{u}) (O : ∀ k, SurgeryObservation (F k))
    (W : ∀ k, M33RegularHistoryWindow (F k)) (H : ∀ k, M33RegularHistoryData (W k))
    (base Q r A tau0 tau K L a R rho : ℕ → ℝ) (N : ℕ → ℕ)
    (center : ∀ k, ((F k).slice (base k)).carrier)
    (data : ∀ k, TerminalRegularStageData S B p (O k) (H k)
      (base k) (Q k) (r k) (A k) (tau0 k) (tau k) (K k) (L k) (a k)
      (R k) (rho k) (N k) (center k))
    {X : Type v} [TopologicalSpace X] [ChartedSpace E X]
    [IsManifold (𝓡 3) ∞ X] [T2Space X]
    (g : RiemannianMetric 3 X) (D : LeviCivitaData g)
    (V : ℕ → Set X) (pX : X) (hpX : ∀ k, pX ∈ V k)
    (phi : ∀ k, PartialDiffeomorph (𝓡 3) (𝓡 3) X
      (terminalRegularStageSource (F k) (base k) (Q k) (A k) (center k)) ∞)
    (hsource : ∀ k, (phi k).source = V k)
    (hbase : ∀ k, phi k pX = (data k).point)
    (c : ℕ → PartialDiffeomorph (𝓡 3) (𝓡 3) X E ∞)
    (hcoverC : ∀ x : X, ∃ i, x ∈ (c i).source)
    (hjets : ∀ i m K, IsCompact K → K ⊆ (c i).target → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m
        (((data k).flow.metric 0).pullbackCoefficients (phi k ∘ (c i).symm)))
      (iteratedFDeriv ℝ m (g.pullbackCoefficients (c i).symm)) atTop K) :
    D.scalarCurvature pX = 1 := by
  obtain ⟨i, hpi⟩ := hcoverC pX
  let y := c i pX
  have hy : y ∈ (c i).target := (c i).map_source hpi
  have hleft : (c i).symm y = pX := (c i).left_inv hpi
  let maps := fun k => (c i).symm.trans (phi k)
  have hsourceK : ∀ᶠ k in atTop, ({y} : Set E) ⊆ (maps k).source := by
    apply Filter.Eventually.of_forall
    intro k z hz
    rcases mem_singleton_iff.mp hz with rfl
    refine ⟨hy, ?_⟩
    change (c i).symm y ∈ (phi k).source
    rw [hleft, hsource k]
    exact hpX k
  have hsame (k : ℕ) : maps k y = (data k).point := by
    change phi k ((c i).symm y) = (data k).point
    rw [hleft, hbase k]
  have hlimit : ∀ eta : ℝ, 0 < eta → ∀ᶠ k : ℕ in atTop,
      |1 - D.scalarCurvature pX| < eta := by
    intro eta heta
    have herror := terminalCurvature_eventually_actual_scalar_error
      (fun k => (data k).flow.connection 0) D maps (c i).symm
      isCompact_singleton (singleton_subset_iff.mpr hy) hsourceK
      (fun m _hm => hjets i m {y} isCompact_singleton (singleton_subset_iff.mpr hy)) heta
    filter_upwards [herror] with k hk
    have h := hk y (mem_singleton y)
    rw [hsame k, (data k).scalar_one] at h
    simpa only [hleft] using h
  by_contra hne
  have hpos : 0 < |1 - D.scalarCurvature pX| := abs_pos.mpr (by
    intro heq
    exact hne (by linarith))
  obtain ⟨k, hk⟩ := (hlimit _ hpos).exists
  exact (lt_irrefl _) hk

end PoincareConjecture.M47
