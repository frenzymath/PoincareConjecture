import PoincareConjecture.Proofs.M35.Uniqueness.Heat.Exhaustion.SmallKillingDefect
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.Exhaustion.TestedStationarity
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.Exhaustion.DistributionalKilling









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness.Heat

local notation "V" => StandardCapSpace

structure CompactKillingHeat {g₀ : StandardInitialMetric}
    (G : PartialStandardCapFlow g₀) (T B₀ J : ℝ) (B : V → V) (E : Set V) where
  field : ℝ → V → V
  slice_smooth : ∀ t, ContDiff ℝ ∞ (field t)
  joint_smooth : ContDiffOn ℝ ∞ (Function.uncurry field) (Ioo 0 G.lifetime ×ˢ univ)
  value_continuous : ContinuousOn (Function.uncurry field) (Icc 0 T ×ˢ univ)
  energy_zero_continuous :
    ContinuousOn (Function.uncurry (vectorHeatJetEnergy G field 0)) (Icc 0 T ×ˢ E)
  energy_one_continuous :
    ContinuousOn (Function.uncurry (vectorHeatJetEnergy G field 1)) (Icc 0 T ×ˢ E)
  defect_continuous : ContinuousOn (fun p : ℝ × V =>
    ((G.flow.metric p.1).tensorNorm
      (killingDefectTensor (G.flow.connection p.1) (field p.1)) p.2) ^ 2) (Icc 0 T ×ˢ E)
  metric_bound : ∀ t ∈ Icc 0 T, ∀ x ∈ E,
    (G.flow.metric t).inner x (field t x) (field t x) ≤ B₀
  initial_gradient : ∀ x ∈ E, vectorHeatJetEnergy G field 1 0 x ≤ J
  initial_killing : ∀ x ∈ E, ∀ u v : V,
    DeTurckNative.metricLieDerivative (G.flow.connection 0) (field 0) x u v = 0
  initial_value : ∀ x ∈ E, field 0 x = B x
  heat : ∀ t ∈ Ioc 0 T, ∀ x ∈ E, ∀ᶠ y in 𝓝 x,
    HasDerivWithinAt (fun s => field s y)
      (@Add.add V inferInstance
        (∑ i, fieldHessian (G.flow.connection t) (field t) y
          ((G.flow.metric t).orthonormalBasis y i) ((G.flow.metric t).orthonormalBasis y i))
        (RicciFlow.ricciSharp (G.flow.connection t) y (field t y))) (Ico 0 G.lifetime) t

theorem CompactKillingHeat.joint_field_smooth {g₀ : StandardInitialMetric}
    {G : PartialStandardCapFlow g₀} {T B₀ J : ℝ} {B : V → V} {E : Set V}
    (H : CompactKillingHeat G T B₀ J B E) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) ((𝓡 3).prod (𝓡 3)) ∞
      (fun p : ℝ × V => Bundle.TotalSpace.mk' V p.2
        (E := TangentSpace (𝓡 3)) (H.field p.1 p.2)) (Ioo 0 G.lifetime ×ˢ univ) := by
  have hj : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) ∞
      (Function.uncurry H.field) (Ioo 0 G.lifetime ×ˢ univ) := by
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
    exact H.joint_smooth.contMDiffOn
  intro p hp
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_snd, ?_⟩
  simpa only [trivializationAt_model_space_apply] using! hj p hp

theorem CompactKillingHeat.heat_hasDerivAt {g₀ : StandardInitialMetric}
    {G : PartialStandardCapFlow g₀} {T B₀ J : ℝ} {B : V → V} {E : Set V}
    (H : CompactKillingHeat G T B₀ J B E) (hTlt : T < G.lifetime)
    {t : ℝ} (ht : t ∈ Ioc 0 T) {x : V} (hx : x ∈ E) :
    HasDerivAt (fun s => H.field s x)
      (@Add.add V inferInstance
        (∑ i, fieldHessian (G.flow.connection t) (H.field t) x
          ((G.flow.metric t).orthonormalBasis x i) ((G.flow.metric t).orthonormalBasis x i))
        (RicciFlow.ricciSharp (G.flow.connection t) x (H.field t x))) t :=
  (Filter.Eventually.self_of_nhds (H.heat t ht x hx)).hasDerivAt
    (mem_of_superset (Ioo_mem_nhds ht.1 (ht.2.trans_lt hTlt)) Ioo_subset_Ico_self)

theorem raw_killing_of_compact_heat
    (P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
    (G : PartialStandardCapFlow g₀) {T B₀ J : ℝ}
    (hT : 0 < T) (hTlt : T < G.lifetime) (hB₀ : 0 ≤ B₀) (hJ : 0 ≤ J)
    {B : V → V} (hB : ContDiff ℝ ∞ B)
    (hproducer : ∀ E : Set V, IsCompact E → Nonempty (CompactKillingHeat G T B₀ J B E)) :
    ∀ t ∈ Icc 0 T, ∀ x u v : V,
      DeTurckNative.metricLieDerivative (G.flow.connection t) B x u v = 0 := by
  intro t ht
  apply metricLieDerivative_eq_zero_of_compact_tests (G.flow.connection t) hB
  intro φ hφ hc u v
  let ψ := fun k => lieTestCoefficient (G.flow.connection t) φ u v k
  have hψ (k : Fin 3) : ContDiff ℝ ∞ (ψ k) :=
    lieTestCoefficient_contDiff (G.flow.connection t) hφ u v k
  have hcψ (k : Fin 3) : HasCompactSupport (ψ k) :=
    lieTestCoefficient_hasCompactSupport (G.flow.connection t) hc u v k
  have hsψ (k : Fin 3) : tsupport (ψ k) ⊆ tsupport φ :=
    lieTestCoefficient_tsupport_subset (G.flow.connection t) φ u v k
  have hTJ : Icc 0 T ⊆ Ico 0 G.lifetime := fun _ hs => ⟨hs.1, hs.2.trans_lt hTlt⟩
  choose C _hC hstationary using fun k : Fin 3 =>
    exists_raw_tested_stationarity_bound G.flow hT.le hTJ (hψ k) (hcψ k) k
  apply integral_lie_eq_zero_of_small_defect_tests (G.flow.connection t) hB hφ hc u v C
  intro δ hδ
  obtain ⟨E, hE, hCE, hsmall⟩ := exists_raw_local_killing_defect_small P G hT hTlt
    hB₀ hJ (sq_pos_of_pos hδ) hc
  obtain ⟨H⟩ := hproducer E hE
  have hCE' : tsupport φ ⊆ E := hCE.trans interior_subset
  have hdefect := hsmall H.field H.slice_smooth H.joint_field_smooth
    H.energy_zero_continuous H.energy_one_continuous H.defect_continuous
    H.metric_bound H.initial_gradient H.initial_killing H.heat
  refine ⟨H.field t, H.slice_smooth t, hdefect t ht, ?_⟩
  intro k
  have hbound := hstationary k H.field H.slice_smooth H.value_continuous
    (H.joint_smooth.mono (prod_mono
      (Ioo_subset_Ioo le_rfl hTlt.le) Subset.rfl))
    (fun s hs x hx => H.heat_hasDerivAt hTlt ⟨hs.1, hs.2.le⟩ (hCE' (hsψ k hx)))
    δ hδ.le (fun s hs x hx => hdefect s hs x (hsψ k hx)) t ht
  have hi : (∫ x, ψ k x * H.field 0 x k) = ∫ x, ψ k x * B x k := by
    apply integral_congr_ae
    apply Eventually.of_forall
    intro x
    change ψ k x * H.field 0 x k = ψ k x * B x k
    by_cases hx : x ∈ tsupport (ψ k)
    · rw [H.initial_value x (hCE' (hsψ k hx))]
    · rw [image_eq_zero_of_notMem_tsupport hx, zero_mul, zero_mul]
  rw [hi] at hbound
  exact hbound

end PoincareConjecture.M35.Uniqueness.Heat
