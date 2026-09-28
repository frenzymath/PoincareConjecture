import PoincareConjecture.Proofs.M09.CompactPhaseBound
import PoincareConjecture.Proofs.M09.LocalRegularizedCurve
import Mathlib.Topology.Order.IntermediateValue








set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [ConnectedSpace M] [T3Space M] [SecondCountableTopology M]

theorem exists_uniform_compact_local_phase_bound {J : Set ℝ}
    (F : RicciFlow n M J) (hM04 : RicciFlowCurvatureTheory.{u})
    (T τmax : ℝ) (hτmax : 0 < τmax) (hwindow : Set.Icc (T - τmax) T ⊆ J)
    (hcurvature : CompleteBoundedCurvatureOn F (Set.Icc (T - τmax) T))
    (p : M) (b Emax : ℝ) (hb : 0 < b) (hbmax : b < τmax) (hEmax : 0 ≤ Emax) :
    ∃ K : Set (ℝ × TangentBundle (𝓡 n) M), IsCompact K ∧
      ∀ (γ : ℝ → M) (U : Set ℝ), IsOpen U → IsPreconnected U → 0 ∈ U →
      IsLocalRegularizedCurveOn F T γ U → γ 0 = p →
      regularizedCurveEnergy F T γ 0 ≤ Emax →
      ∀ s ∈ U, 0 ≤ s → s < Real.sqrt b → (s, curvePhase (n := n) γ s) ∈ K := by
  obtain ⟨K, hK, hbound⟩ := exists_uniform_compact_phase_bound F hM04 T τmax hτmax
    hwindow hcurvature p b Emax hb hbmax hEmax
  refine ⟨K, hK, ?_⟩
  intro γ U hU hconn h0 hγ hstart henergy s hs hs0 hsb
  obtain ⟨a, c, hsac, hac⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    ((hU.inter isOpen_Iio).mem_nhds ⟨hs, hsb⟩)
  obtain ⟨h, hsh, hhc⟩ := exists_between hsac.2
  have hh : h ∈ U ∩ Set.Iio (Real.sqrt b) := hac ⟨hsac.1.trans hsh, hhc⟩
  have hh0 : 0 < h := hs0.trans_lt hsh
  have hIU : Set.Icc 0 h ⊆ U := hconn.ordConnected.out h0 hh.1
  have htime : Set.Icc 0 h ⊆ Set.Ioo (-Real.sqrt τmax) (Real.sqrt τmax) := by
    intro t ht
    exact ⟨(neg_lt_zero.mpr (Real.sqrt_pos.mpr hτmax)).trans_le ht.1,
      ht.2.trans_lt (hh.2.trans (Real.sqrt_lt_sqrt hb.le hbmax))⟩
  obtain ⟨E, heq⟩ := exists_regularizedExtensionOn_compact F hM04 T τmax hτmax hwindow
    γ U (Set.Icc 0 h) hU hIU isCompact_Icc (uniqueDiffOn_Icc hh0) htime hγ.smooth
    (fun t ht ↦ hγ.equation t (hIU ht))
  exact hbound γ U h hh0.le hh.2 hU hIU hγ.smooth hstart E heq henergy s ⟨hs0, hsh.le⟩

end PoincareConjecture.Proofs.M09
