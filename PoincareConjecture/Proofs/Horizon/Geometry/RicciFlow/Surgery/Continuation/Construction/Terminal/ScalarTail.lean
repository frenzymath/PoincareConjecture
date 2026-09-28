import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Extinction.Core
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Extinction.Reference
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Extinction.ScalarContinuity
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.ScalarEscape
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Construction

set_option autoImplicit false

open Set Filter Topology
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] [SecondCountableTopology M]
  {G : GeneralizedRicciFlowData.{u}} {T : ℝ} {H : SingularTimeAssumptions G T M}

theorem SingularLimitConclusion.exists_uniform_strict_scalar_tail
    (Q : SingularLimitConclusion H) (K : Set (Q.extension.extended.slice T).carrier)
    (hK : IsCompact K) (a : ℝ) (ha : ∀ z ∈ K, a < Q.terminal_scalar z) :
    ∃ s : ℝ, H.reference.tMinus < s ∧ s < T ∧
      ∀ t ∈ Ico s T, ∀ z ∈ K, a < H.reference.scalar t (Q.terminal_source z) := by
  let tT : Ioc H.reference.tMinus T := ⟨T, H.reference.tMinus_lt, le_rfl⟩
  have hu : ∀ᶠ t : Ioc H.reference.tMinus T in 𝓝 tT, ∀ z ∈ K,
      a < Q.extension.extended.scalar (Q.gluing_map (t, z)) := by
    apply hK.eventually_forall_of_forall_eventually
    intro z hz
    have hTa : a < (Q.extension.extended.scalar ∘ Q.gluing_map) (tT, z) := by
      simpa only [Function.comp_apply, tT, Q.gluing_scalar_terminal] using ha z hz
    exact Q.continuous_gluing_scalar.continuousAt.eventually (Ioi_mem_nhds hTa)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hu
  obtain ⟨s, hs, hsT⟩ := exists_between
    (max_lt H.reference.tMinus_lt (sub_lt_self T hδ))
  have hsref := (le_max_left H.reference.tMinus (T - δ)).trans_lt hs
  refine ⟨s, hsref, hsT, ?_⟩
  intro t ht z hz
  have htref : H.reference.tMinus < t := hsref.trans_le ht.1
  have hdist : dist (⟨t, htref, ht.2.le⟩ : Ioc H.reference.tMinus T) tT < δ := by
    rw [Subtype.dist_eq, Real.dist_eq, abs_of_neg (sub_neg.mpr ht.2)]
    have := (le_max_right H.reference.tMinus (T - δ)).trans_lt hs
    linarith [ht.1]
  have h := hball hdist z hz
  change a < Q.extension.extended.scalar
    (Q.gluing_map (⟨t, htref, ht.2.le⟩, z)) at h
  rwa [Q.gluing_scalar_old t ⟨htref, ht.2.le⟩ ht.2 z] at h

theorem SingularLimitConclusion.exists_uniform_scalar_tail_off_open
    (Q : SingularLimitConclusion H) (U : Set M) (hU : IsOpen U) (a : ℝ)
    (ha : ∀ z, Q.terminal_source z ∉ U → a < Q.terminal_scalar z) :
    ∃ s : ℝ, H.reference.tMinus < s ∧ s < T ∧
      ∀ t ∈ Ico s T, ∀ x : M, x ∉ U → a < H.reference.scalar t x := by
  let P04 : RicciFlowCurvatureTheory.{u} := ricciFlowCurvatureTheory
  let K := max (H.r₀⁻¹ ^ 2) a + 1
  have hrho : 0 < H.r₀⁻¹ ^ 2 := sq_pos_of_pos (inv_pos.mpr H.r₀_pos)
  have hrhoK : H.r₀⁻¹ ^ 2 ≤ K := by dsimp [K]; linarith [le_max_left (H.r₀⁻¹ ^ 2) a]
  have haK : a < K := by dsimp [K]; linarith [le_max_right (H.r₀⁻¹ ^ 2) a]
  have hK : 0 < K := hrho.trans_le hrhoK
  let δ := 1 / (4 * (H.analytic_constant + 1) * K)
  have hδ : 0 < δ := by dsimp [δ]; positivity [H.analytic_constant_pos]
  obtain ⟨b, hb, hbT, hcompact⟩ := H.exists_compact_scalar_sublevel_tail P04 (2 * K)
  obtain ⟨s, hs, hsT⟩ := exists_between (max_lt hbT (sub_lt_self T hδ))
  have hbs : b < s := (le_max_left b (T - δ)).trans_lt hs
  have hsref : H.reference.tMinus < s := hb.trans hbs
  have hshort : T - s < δ := by
    have := (le_max_right b (T - δ)).trans_lt hs
    linarith
  let A := {x | H.reference.scalar s x ≤ 2 * K} \ U
  have hA : IsCompact A := (hcompact s ⟨hbs.le, hsT⟩).1.inter_right hU.isClosed_compl
  have hArange : A ⊆ range Q.terminal_source := by
    rw [Q.terminal_source_image]
    exact fun x hx => (hcompact s ⟨hbs.le, hsT⟩).2 hx.1
  have hcompact' : IsCompact (Q.terminal_source ⁻¹' A) :=
    Q.terminal_source_openEmbedding.isEmbedding.isInducing.isCompact_preimage' hA hArange
  obtain ⟨r, hr, hrT, htail⟩ := Q.exists_uniform_strict_scalar_tail
    (Q.terminal_source ⁻¹' A) hcompact' a (fun z hz => ha z hz.2)
  refine ⟨max s r, hsref.trans_le (le_max_left s r), max_lt hsT hrT, ?_⟩
  intro t ht x hxU
  apply lt_of_not_ge
  intro hlow
  have hst : s ≤ t := (le_max_left s r).trans ht.1
  have hrt : r ≤ t := (le_max_right s r).trans ht.1
  have hcont : ContinuousOn (fun z => H.reference.scalar z x) (Icc s t) :=
    (H.reference_scalar_continuousOn P04 x).mono
      (fun z hz => ⟨hsref.le.trans hz.1, hz.2.trans_lt ht.2⟩)
  have hbound := SingularRegularLimit.scalar_lt_two_mul_of_short_interval_backward
    H.analytic_constant_pos.le hrho hrhoK hcont (hlow.trans_lt haK)
    (fun z hz => H.reference_scalar_derivative_bound x z
      ⟨hsref.trans hz.1, hz.2.trans ht.2⟩)
    ((sub_le_sub_right ht.2.le s).trans_lt hshort) s ⟨le_rfl, hst⟩
  have hxA : x ∈ A := ⟨hbound.le, hxU⟩
  obtain ⟨z, hz⟩ := hArange hxA
  have hzA : z ∈ Q.terminal_source ⁻¹' A := by
    simpa only [mem_preimage, hz] using hxA
  have hgt := htail t ⟨hrt, ht.2⟩ z hzA
  rw [hz] at hgt
  exact hgt.not_ge hlow

namespace RepairedContinuationLimitBridge

variable {L : RepairedSingularRegularLimitData H} {N : RepairedHornSelectionData H}
  {F : SurgeryFlowData.{u}} {I : RepairedContinuationInput F T}
  (B : RepairedContinuationLimitBridge H L N I)

include B

theorem core_map_isOpenEmbedding : Topology.IsOpenEmbedding B.core_map := by
  let t : Ico H.reference.tMinus T := ⟨H.reference.tMinus, le_rfl, H.reference.tMinus_lt⟩
  let s : Ico I.last_slab.start T :=
    ⟨H.reference.tMinus, B.reference_start_lt.le, H.reference.tMinus_lt⟩
  have heq : B.core_map = B.reference_identify t ∘ I.last_slab.identify s :=
    funext B.core_map_eq_reference
  rw [heq]
  exact (B.reference_identify t).toHomeomorph.isOpenEmbedding.comp
    (I.last_slab.identify s).toHomeomorph.isOpenEmbedding

theorem preterminal_uniform_scalar_tail_off_open
    (D : Set (F.slice I.last_slab.start).carrier) (hD : IsOpen D)
    (hcore : I.controlled_core ⊆ D) (a : ℝ) (ha : a < I.rho⁻¹ ^ 2) :
    ∃ s : ℝ, I.last_slab.start < s ∧ s < T ∧
      ∀ t ∈ Ico s T, ∀ x : (F.slice I.last_slab.start).carrier,
        x ∉ D → a < (I.last_slab.flow.connection t).scalarCurvature x := by
  have hterminal : ∀ z, N.limit.terminal_source z ∉ B.core_map '' D →
      a < N.limit.terminal_scalar z := by
    intro z hz
    apply ha.trans
    apply lt_of_not_ge
    intro hlow
    have hsource : N.limit.terminal_source z ∈ B.core_map '' I.controlled_core := by
      rw [B.core_map_image]
      exact ⟨N.limit.terminal_source_image ▸ mem_range_self z, z, rfl, hlow⟩
    exact hz (image_mono hcore hsource)
  obtain ⟨s, hs, hsT, htail⟩ := N.limit.exists_uniform_scalar_tail_off_open
    (B.core_map '' D) (B.core_map_isOpenEmbedding.isOpenMap D hD) a hterminal
  refine ⟨s, B.reference_start_lt.trans hs, hsT, ?_⟩
  intro t ht x hx
  rw [← B.reference_scalar_core_map t ⟨hs.le.trans ht.1, ht.2⟩ x]
  apply htail t ht (B.core_map x)
  rintro ⟨y, hy, heq⟩
  exact hx (B.core_map_isOpenEmbedding.injective heq ▸ hy)

theorem reference_pointwise_strict_scalar_tail (hempty : I.controlled_core = ∅) (x : M) :
    ∃ a : ℝ, I.rho⁻¹ ^ 2 < a ∧ ∃ s : ℝ, H.reference.tMinus < s ∧ s < T ∧
      ∀ t ∈ Ico s T, a < H.reference.scalar t x := by
  classical
  by_cases hx : x ∈ H.reference.regularLimitSet
  · have hx' : x ∈ range N.limit.terminal_source := by
      rwa [N.limit.terminal_source_image]
    obtain ⟨z, rfl⟩ := hx'
    obtain ⟨a, ha, haz⟩ := exists_between (B.terminal_scalar_gt_of_core_empty hempty z)
    exact ⟨a, ha, N.limit.exists_strict_scalar_tail z a haz⟩
  · obtain ⟨s, hs, hsT, htail⟩ := H.scalar_diverges_uniformly_off_regularLimitSet
      ricciFlowCurvatureTheory (I.rho⁻¹ ^ 2 + 1)
    exact ⟨I.rho⁻¹ ^ 2 + 1, by linarith, s, hs, hsT, fun t ht => htail t ht x hx⟩

theorem reference_uniform_scalar_tail (hempty : I.controlled_core = ∅)
    (a : ℝ) (ha : a < I.rho⁻¹ ^ 2) :
    ∃ s : ℝ, H.reference.tMinus < s ∧ s < T ∧
      ∀ t ∈ Ico s T, ∀ x : M, a < H.reference.scalar t x := by
  simpa using N.limit.exists_uniform_scalar_tail_off_open ∅ isOpen_empty a
    (fun z _ => ha.trans (B.terminal_scalar_gt_of_core_empty hempty z))

theorem preterminal_pointwise_strict_scalar_tail (hempty : I.controlled_core = ∅)
    (x : (F.slice I.last_slab.start).carrier) :
    ∃ a : ℝ, I.rho⁻¹ ^ 2 < a ∧ ∃ s : ℝ, I.last_slab.start ≤ s ∧ s < T ∧
      ∀ t ∈ Ico s T, a < (I.last_slab.flow.connection t).scalarCurvature x := by
  obtain ⟨a, ha, s, hs, hsT, htail⟩ :=
    B.reference_pointwise_strict_scalar_tail hempty (B.core_map x)
  refine ⟨a, ha, s, (B.reference_start_lt.trans hs).le, hsT, ?_⟩
  intro t ht
  rw [← B.reference_scalar_core_map t ⟨hs.le.trans ht.1, ht.2⟩ x]
  exact htail t ht

theorem preterminal_uniform_scalar_tail (hempty : I.controlled_core = ∅)
    (a : ℝ) (ha : a < I.rho⁻¹ ^ 2) :
    ∃ s : ℝ, I.last_slab.start ≤ s ∧ s < T ∧
      ∀ t ∈ Ico s T, ∀ x : (F.slice I.last_slab.start).carrier,
        a < (I.last_slab.flow.connection t).scalarCurvature x := by
  obtain ⟨s, hs, hsT, htail⟩ := B.reference_uniform_scalar_tail hempty a ha
  refine ⟨s, (B.reference_start_lt.trans hs).le, hsT, ?_⟩
  intro t ht x
  rw [← B.reference_scalar_core_map t ⟨hs.le.trans ht.1, ht.2⟩ x]
  exact htail t ht (B.core_map x)

end RepairedContinuationLimitBridge
end PoincareConjecture
