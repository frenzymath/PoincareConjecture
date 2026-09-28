import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Cap.Core.Truncation.Reference
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Cap.Core.Truncation.Model
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Cap.Core.Truncation.Boundary

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

noncomputable section

namespace PoincareConjecture.SingularRegularLimit

structure CapDomainTopology {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (kind : CapModelKind) (p : RealProjectiveThree)
    (U K core B E V : Set M) where
  carrier_open : IsOpen U
  closed_core_compact : IsCompact K
  core_nonempty : core.Nonempty
  core_eq_interior : core = interior K
  model_equivalence : CapModelEquivalence kind p U
  end_subset : E ⊆ U
  closed_core_eq_complement_end : K = U \ E
  boundary_eq_end_frontier : B = U ∩ frontier E
  boundary_subset_negative_end_closure : B ⊆ closure V
  boundary_subset : B ⊆ U
  core_frontier_eq_boundary : frontier K = B
  boundary_local_defining_function : ∀ x ∈ B, ∃ W : Set M, ∃ f : M → ℝ,
    IsOpen W ∧ x ∈ W ∧ W ⊆ U ∧
      (∀ y ∈ W, y ∈ K ↔ f y ≤ 0) ∧ f x = 0 ∧
      ContMDiffOn (𝓡 3) 𝓘(ℝ, ℝ) ∞ f W ∧
      ∃ v : TangentSpace (𝓡 3) x, v ≠ 0 ∧ mvfderiv (𝓡 3) f x v ≠ 0

end PoincareConjecture.SingularRegularLimit

namespace PoincareConjecture.CapCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M}

omit [T2Space M] in
theorem truncated_core_eq_complement_end (C : CapCertificate g) {a b : ℝ}
    (ha : -C.epsilon⁻¹ < a) (hab : a < b)
    (hK : C.closed_core ∪ closure (C.end_neck.region (-C.epsilon⁻¹) a) ⊆ C.carrier) :
    C.closed_core ∪ closure (C.end_neck.region (-C.epsilon⁻¹) a) =
      (C.closed_core ∪ C.end_neck.region (-C.epsilon⁻¹) b) \ C.end_neck.region a b := by
  ext x
  constructor
  · intro hx
    by_cases hxN : x ∈ C.end_neck.carrier
    · have hle := (C.truncated_closed_core_height_iff ha hxN).mp hx
      have hlo := (C.end_neck.coordinate_inverse_mem x hxN).2.1
      rw [C.end_neck_epsilon] at hlo
      exact ⟨Or.inr ⟨hxN, hlo, hle.trans_lt hab⟩,
        fun hz => (not_lt_of_ge hle) hz.2.1⟩
    · have hc := (C.carrier_eq_closed_core_union_end ▸ hK hx).resolve_right hxN
      exact ⟨Or.inl hc, fun hz => hxN hz.1⟩
  · rintro ⟨hc | hn, hnot⟩
    · exact Or.inl hc
    · apply (C.truncated_closed_core_height_iff ha hn.1).mpr
      exact le_of_not_gt (fun h => hnot ⟨hn.1, h, hn.2.2⟩)

omit [T2Space M] in

theorem truncated_slice_subset_positive_region_closure (C : CapCertificate g)
    {a d : ℝ} (ha : -C.epsilon⁻¹ < a) (had : a < d) (ha' : a < C.epsilon⁻¹) :
    range (fun q : UnitTwoSphere => C.end_neck.coordinate_map (q, a)) ⊆
      closure (C.end_neck.region a d) := by
  rintro _ ⟨q, rfl⟩
  have hz : (q, a) ∈ C.end_neck.cylinderDomain := by
    exact ⟨mem_univ _, by simpa only [C.end_neck_epsilon, mem_Ioo] using And.intro ha ha'⟩
  have hx := C.end_neck.coordinate_map_mem hz
  have himage : C.end_neck.coordinatePartialHomeomorph.symm.IsImage
      (C.end_neck.region a d) ((univ : Set UnitTwoSphere) ×ˢ Ioo a d) := by
    intro y hy
    change (C.end_neck.coordinate_inverse y).1 ∈ univ ∧
      (C.end_neck.coordinate_inverse y).2 ∈ Ioo a d ↔
        y ∈ C.end_neck.carrier ∧ a < (C.end_neck.coordinate_inverse y).2 ∧
          (C.end_neck.coordinate_inverse y).2 < d
    simp only [mem_univ, true_and, mem_Ioo, show y ∈ C.end_neck.carrier from hy]
  apply (himage.closure.apply_mem_iff hx).mp
  change C.end_neck.coordinate_inverse (C.end_neck.coordinate_map (q, a)) ∈
    closure ((univ : Set UnitTwoSphere) ×ˢ Ioo a d)
  rw [C.end_neck.coordinate_inverse_coordinate_map hz, closure_prod_eq, closure_univ,
    closure_Ioo had.ne]
  exact ⟨mem_univ _, le_rfl, had.le⟩

end PoincareConjecture.CapCertificate

namespace PoincareConjecture.SingularRegularLimit

theorem exists_terminal_truncated_domain_topology_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 1000 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M]
        {F : GeneralizedRicciFlowData.{u}} {T : ℝ}
        (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
        {t : ℝ} (ht : t ∈ Ico H.reference.tMinus T)
        (C : CapCertificate (F.metric t)), C.epsilon ≤ ε₀ →
        H.reference.inverse t ht '' C.carrier ⊆ H.reference.regularLimitSet →
        ∀ x₀ : H.regularRegion P04, H.reference.forward t ht x₀ ∈ C.core →
        ∀ a b d : ℝ, -C.epsilon⁻¹ < a → a < b → b < C.epsilon⁻¹ → a < d →
          Nonempty (CapDomainTopology C.model_kind C.puncture
            (H.regularReferencePreimage P04 t ht
              (C.closed_core ∪ C.end_neck.region (-C.epsilon⁻¹) b))
            (H.regularReferencePreimage P04 t ht
              (C.closed_core ∪ closure (C.end_neck.region (-C.epsilon⁻¹) a)))
            (H.regularReferencePreimage P04 t ht
              (C.closed_core ∪ C.end_neck.region (-C.epsilon⁻¹) a))
            (H.regularReferencePreimage P04 t ht
              (range (fun q : UnitTwoSphere => C.end_neck.coordinate_map (q, a))))
            (H.regularReferencePreimage P04 t ht (C.end_neck.region a b))
            (H.regularReferencePreimage P04 t ht (C.end_neck.region a d))) := by
  obtain ⟨ε₁, hε₁, hsmall, hdomain⟩ := CapCertificate.exists_truncated_core_domain_threshold.{u}
  obtain ⟨ε₂, hε₂, _, hmodel⟩ := CapCertificate.exists_truncated_carrier_model_threshold.{u}
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, (min_le_left _ _).trans hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ _ F T H P04 t ht C hε hcapture x₀ hx₀ a b d ha hab hb had
  let U := C.closed_core ∪ C.end_neck.region (-C.epsilon⁻¹) b
  let K := C.closed_core ∪ closure (C.end_neck.region (-C.epsilon⁻¹) a)
  let I := C.closed_core ∪ C.end_neck.region (-C.epsilon⁻¹) a
  let B := range (fun q : UnitTwoSphere => C.end_neck.coordinate_map (q, a))
  let E := C.end_neck.region a b
  let V := C.end_neck.region a d
  obtain ⟨hKcompact, hKsub, hI, hfrontier, _, _⟩ :=
    hdomain C (hε.trans (min_le_left _ _)) a ⟨ha, hab.trans hb⟩
  obtain ⟨_, _, hUb, _, _, _⟩ :=
    hdomain C (hε.trans (min_le_left _ _)) b ⟨ha.trans hab, hb⟩
  change IsCompact K at hKcompact
  change interior K = I at hI
  change frontier K = B at hfrontier
  have hUopen : IsOpen U := by
    change IsOpen (C.closed_core ∪ C.end_neck.region (-C.epsilon⁻¹) b)
    rw [← hUb]
    exact isOpen_interior
  have hUsub : U ⊆ C.carrier := union_subset C.closed_core_subset_carrier
    (fun _ hx => C.end_neck_subset hx.1)
  have hKeq : K = U \ E := C.truncated_core_eq_complement_end ha hab hKsub
  have hKU : K ⊆ U := hKeq ▸ sdiff_subset
  have hEU : E ⊆ U := fun x hx => Or.inr ⟨hx.1, ha.trans hx.2.1, hx.2.2⟩
  have hEeq : E = Kᶜ ∩ U := by
    rw [hKeq]
    ext x
    simp only [mem_inter_iff, mem_compl_iff, mem_sdiff]
    constructor
    · intro hx
      exact ⟨fun h => h.2 hx, hEU hx⟩
    · rintro ⟨hn, hU⟩
      by_contra h
      exact hn ⟨hU, h⟩
  have hBU : B ⊆ U := by
    rw [← hfrontier]
    exact (frontier_subset_closure.trans (by rw [hKcompact.isClosed.closure_eq])).trans hKU
  have hBfront : B = U ∩ frontier E := by
    rw [hEeq, inter_comm U, frontier_inter_open_inter hUopen, frontier_compl,
      hfrontier, inter_eq_left.mpr hBU]
  have hcaptureU : H.reference.inverse t ht '' U ⊆ H.reference.regularLimitSet :=
    (image_mono hUsub).trans hcapture
  have hcaptureK : H.reference.inverse t ht '' K ⊆ H.reference.regularLimitSet :=
    (image_mono hKsub).trans hcapture
  obtain ⟨J⟩ := hmodel C (hε.trans (min_le_right _ _)) b ⟨ha.trans hab, hb⟩
  refine ⟨{
    carrier_open := H.regularReferencePreimage_open P04 ht hUopen
    closed_core_compact := H.regularReferencePreimage_compact P04 ht x₀ hKcompact hcaptureK
    core_nonempty := ⟨x₀, Or.inl (C.core_subset_closed_core hx₀)⟩
    core_eq_interior := ?_
    model_equivalence := H.regularReferenceModelEquivalence P04 ht x₀ hcaptureU J
    end_subset := preimage_mono hEU
    closed_core_eq_complement_end := ?_
    boundary_eq_end_frontier := ?_
    boundary_subset_negative_end_closure := ?_
    boundary_subset := preimage_mono hBU
    core_frontier_eq_boundary := ?_
    boundary_local_defining_function := ?_ }⟩
  · change H.regularReferencePreimage P04 t ht I =
      interior (H.regularReferencePreimage P04 t ht K)
    rw [← H.regularReferencePreimage_interior P04 ht K, hI]
  · change H.regularReferencePreimage P04 t ht K = _
    rw [hKeq]
    rfl
  · change H.regularReferencePreimage P04 t ht B = _
    rw [hBfront, ← H.regularReferencePreimage_frontier P04 ht E]
    rfl
  · rw [← H.regularReferencePreimage_closure P04 ht V]
    exact preimage_mono (C.truncated_slice_subset_positive_region_closure ha had (hab.trans hb))
  · rw [← H.regularReferencePreimage_frontier P04 ht K, hfrontier]
  · exact H.regularReferencePreimage_local_defining_function P04 ht x₀ hKU hcaptureU
      (fun _ hx => C.truncated_core_local_defining_function ha hab hb hx)

end PoincareConjecture.SingularRegularLimit
