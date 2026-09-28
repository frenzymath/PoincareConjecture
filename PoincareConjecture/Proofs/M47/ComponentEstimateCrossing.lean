import PoincareConjecture.Proofs.M47.ComponentEstimatePersistence
import PoincareConjecture.Proofs.M47.ComponentEstimateScalarPatch
import PoincareConjecture.Proofs.M34.Lemma12_3_Estimates.Regularity
import Mathlib.Topology.Order.Compact

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

theorem exists_last_component_scalar_crossing
    {f : ℝ → ℝ} {s t H : ℝ} (hst : s ≤ t)
    (hf : ContinuousOn f (Icc s t)) (hs : H ≤ f s) (ht : f t < H) :
    ∃ c ∈ Ico s t, f c = H ∧ (∀ u ∈ Icc c t, f u ≤ H) ∧
      ∀ u ∈ Ioc c t, f u < H := by
  have hclosed : IsClosed (Icc s t ∩ f ⁻¹' Ici H) :=
    hf.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  obtain ⟨c, hc, hmax⟩ :=
    (isCompact_Icc.of_isClosed_subset hclosed inter_subset_left).exists_isGreatest
      ⟨s, ⟨⟨le_rfl, hst⟩, hs⟩⟩
  have hct : c < t := by
    apply lt_of_le_of_ne hc.1.2
    intro heq
    have h := hc.2
    rw [heq] at h
    exact not_le_of_gt ht h
  have hvalue : f c = H := by
    obtain ⟨v, hv, hfv⟩ := intermediate_value_Icc' hct.le
      (hf.mono (Icc_subset_Icc hc.1.1 le_rfl)) ⟨ht.le, hc.2⟩
    have hvc : v ≤ c := hmax ⟨⟨hc.1.1.trans hv.1, hv.2⟩, hfv.ge⟩
    simpa only [le_antisymm hvc hv.1] using hfv
  have hstrict : ∀ u ∈ Ioc c t, f u < H := by
    intro u hu
    apply lt_of_not_ge
    intro hHu
    exact not_le_of_gt hu.1 (hmax ⟨⟨hc.1.1.trans hu.1.le, hu.2⟩, hHu⟩)
  refine ⟨c, ⟨hc.1.1, hct⟩, hvalue, ?_, hstrict⟩
  intro u hu
  rcases lt_or_eq_of_le hu.1 with hcu | rfl
  · exact (hstrict u ⟨hcu, hu.2⟩).le
  · exact hvalue.le

theorem exists_component_maximum_exclusion_duration
    (P : M47ScalarPersistencePredecessors.{u})
    (rescale : GeneralizedParabolicRescalingTheory.{u} 3)
    (K B : ℝ) (hK : 0 < K) (hB : 0 < B) :
    ∃ tau : ℝ, 0 < tau ∧ tau ≤ 1 ∧
      ∀ (M : Type u) [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [T2Space M] [SecondCountableTopology M] [CompactSpace M],
      ∀ (s t H : ℝ), s < t → 0 < H →
      ∀ F : RicciFlow 3 M (Icc s t),
        (∀ u ∈ Icc s t, ∀ x : M, (F.connection u).curvatureTensorNorm x ≤ K * H) →
        (∀ u ∈ Icc s t, ∀ x : M, -H ≤ (F.connection u).scalarCurvature x) →
        (∀ x : M, (F.connection s).scalarCurvature x ≤ H) →
        (∀ x : M, 3 * H / 4 ≤ (F.connection s).scalarCurvature x →
          ∀ v : TangentSpace (𝓡 3) x, (F.metric s).inner x v v = 1 →
            |mvfderiv (𝓡 3) (F.connection s).scalarCurvature x v| ≤
              B * (F.connection s).scalarCurvature x ^ (3 / 2 : ℝ)) →
        H * (t - s) ≤ tau →
        (∀ x : M, (F.connection t).scalarCurvature x < H / 4) →
        ∀ p : M, (F.connection s).scalarCurvature p ≠ H := by
  have ha : 0 < 1 / (8 * B) := by positivity
  obtain ⟨tau, htau, htau1, hpersist⟩ :=
    exists_physical_scalar_persistence P rescale K (1 / (8 * B)) hK ha
  refine ⟨tau, htau, htau1, ?_⟩
  intro M _ _ _ _ _ _ s t H hst hH F hcurvature hfloor hupper hgrad hshort hterminal p hp
  have hpatch := component_maximum_scalar_patch (F.metric s) (F.connection s)
    (M34.contMDiff_scalarCurvature (F.connection s)) hB hH p hp
    (fun x _hx => hupper x) (fun x _hx => hgrad x)
  have hradius : (Real.sqrt H)⁻¹ / (8 * B) = (1 / (8 * B)) / Real.sqrt H := by
    simp only [div_eq_mul_inv, one_mul]
    ring
  rw [hradius] at hpatch
  have hfinal := hpersist M s t H hst hH F p isClosed_closure.isCompact
    (fun u hu x _hx => hcurvature u hu x) (fun u hu x _hx => hfloor u hu x)
    hpatch hshort
  exact not_le_of_gt (hterminal p) hfinal

end PoincareConjecture.M47
