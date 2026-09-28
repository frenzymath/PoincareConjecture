import PoincareConjecture.Proofs.M38.CylinderEnds
import PoincareConjecture.Proofs.M38.CapModelTopology

set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.M38

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [T2Space M]

omit [T2Space M] in

theorem cylinder_union_not_compact {U V : Set M} (hU : IsOpen U)
    (hUnc : ¬ IsCompact U) (C : OpenCylinderModel V)
    (D : OpenCylinderModel (U ∩ V)) : ¬ IsCompact (U ∪ V) := by
  classical
  intro hcompact
  have hVU : ¬ V ⊆ U := by
    intro h
    exact hUnc (by simpa only [Set.union_eq_self_of_subset_right h] using hcompact)
  obtain ⟨x, hxV, hxU⟩ := Set.not_subset.mp hVU
  let K₀ : Set M := (U ∪ V) \ U
  have hK₀ : IsCompact K₀ := hcompact.inter_right hU.isClosed_compl
  have hK₀V : K₀ ⊆ Set.range (Subtype.val : V → M) := by
    rintro y ⟨hy, hyU⟩
    exact ⟨⟨y, hy.resolve_left hyU⟩, rfl⟩
  let L : Set V := Subtype.val ⁻¹' K₀
  have hL : IsCompact L :=
    IsEmbedding.subtypeVal.isInducing.isCompact_preimage' hK₀ hK₀V
  let K : Set (UnitTwoSphere × Set.Ioo (0 : ℝ) 1) := C.homeomorph ⁻¹' L
  have hK : IsCompact K := C.homeomorph.isCompact_preimage.mpr hL
  have hmem (z : UnitTwoSphere × Set.Ioo (0 : ℝ) 1) :
      z ∈ K ↔ (C.homeomorph z).val ∉ U := by
    change ((C.homeomorph z).val ∈ U ∪ V ∧ (C.homeomorph z).val ∉ U) ↔ _
    exact ⟨fun h => h.2, fun h => ⟨Or.inr (C.homeomorph z).property, h⟩⟩
  have hKne : K.Nonempty := by
    refine ⟨C.homeomorph.symm ⟨x, hxV⟩, (hmem _).mpr ?_⟩
    simpa only [C.homeomorph.apply_symm_apply] using hxU
  let e₁ : (Kᶜ : Set (UnitTwoSphere × Set.Ioo (0 : ℝ) 1)) ≃ₜ
      {y : V // y.val ∈ U} :=
    C.homeomorph.subtype (fun z => by
      change (z ∉ K) ↔ (C.homeomorph z).val ∈ U
      rw [hmem, not_not])
  let e₂ : {y : V // y.val ∈ U} ≃ₜ (U ∩ V : Set M) :=
    { toFun := fun y => ⟨y.val.val, y.property, y.val.property⟩
      invFun := fun y => ⟨⟨y.val, y.property.2⟩, y.property.1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _ }
  let : ConnectedSpace UnitTwoSphere :=
    isConnected_iff_connectedSpace.mp
      (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp)) _ zero_le_one)
  exact (no_cylinder_homeomorph_compact_compl hK hKne).false
    ((e₁.trans e₂).trans D.homeomorph.symm)

variable [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M] [T3Space M]
  {g : RiemannianMetric 3 M}

omit [T2Space M] in

theorem capped_tube_not_compact (C : CappedTubeCertificate g)
    (hcap : ¬ IsCompact C.cap.carrier) : ¬ IsCompact C.carrier := by
  rw [C.carrier_eq_union]
  exact cylinder_union_not_compact C.cap.carrier_open hcap C.tube.cylinder
    C.attachment.overlap_model

omit [T2Space M] in

theorem no_capped_tube_containing_compact_component
    (x : M) (hx : IsCompact (connectedComponent x))
    (C : CappedTubeCertificate g) (hcap : ¬ IsCompact C.cap.carrier) :
    ¬ connectedComponent x ⊆ C.carrier := by
  intro hsub
  have heq : C.carrier = connectedComponent x :=
    Set.Subset.antisymm
      (C.connected.subset_connectedComponent (hsub mem_connectedComponent)) hsub
  exact capped_tube_not_compact C hcap (heq.symm ▸ hx)

end PoincareConjecture.M38
