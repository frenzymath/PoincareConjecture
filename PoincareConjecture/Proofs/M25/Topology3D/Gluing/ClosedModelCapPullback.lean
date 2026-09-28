import PoincareConjecture.Proofs.M25.Topology3D.Gluing.ClosedModelCapData
import Mathlib.Topology.OpenPartialHomeomorph.Composition

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M25.Topology3D

theorem ClosedModelCapData.exists_pullback
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T3Space M] {g : RiemannianMetric 3 M}
    (C : ClosedModelCapData g) (U : Set M)
    (Phi : OpenPartialHomeomorph M M)
    (hsource : Phi.source = U) (htarget : Phi.target = C.carrier)
    (hsmooth : ContMDiffOn (𝓡 3) (𝓡 3) ∞ Phi U)
    (hinverse : ContMDiffOn (𝓡 3) (𝓡 3) ∞ Phi.symm C.carrier) :
    ∃ B : ClosedModelCapData g,
      B.carrier = U ∧ B.epsilon = C.epsilon ∧
        B.model_kind = C.model_kind ∧ B.puncture = C.puncture := by
  classical
  have hUopen : IsOpen U := hsource ▸ Phi.open_source
  have hEsource : Phi.symm.source = C.carrier := htarget
  have hEtarget : Phi.symm.target = U := hsource
  have hmap {x : M} (hx : x ∈ U) : Phi x ∈ C.carrier :=
    htarget ▸ Phi.map_source (hsource.symm ▸ hx)
  have hsymm {y : M} (hy : y ∈ C.carrier) : Phi.symm y ∈ U :=
    hsource ▸ Phi.map_target (htarget.symm ▸ hy)
  have hleft {x : M} (hx : x ∈ U) : Phi.symm (Phi x) = x :=
    Phi.left_inv (hsource.symm ▸ hx)
  have hright {y : M} (hy : y ∈ C.carrier) : Phi (Phi.symm y) = y :=
    Phi.right_inv (htarget.symm ▸ hy)
  have himage : Phi.symm '' C.carrier = U := by
    rw [← htarget, Phi.symm_image_target_eq_source, hsource]
  have hinj : InjOn Phi.symm C.carrier := hEsource ▸ Phi.symm.injOn
  have himage_diff {A : Set M} (hA : A ⊆ C.carrier) :
      Phi.symm '' (C.carrier \ A) = U \ Phi.symm '' A := by
    rw [hinj.image_sdiff_subset hA, himage]
  have himage_target {A : Set M} (hA : A ⊆ C.carrier) :
      Phi.symm '' A ⊆ Phi.symm.target := by
    rintro y ⟨x, hx, rfl⟩
    exact Phi.symm.map_source (hEsource.symm ▸ hA hx)
  have hIsImage {A : Set M} (hA : A ⊆ C.carrier) :
      Phi.symm.IsImage A (Phi.symm '' A) := by
    apply OpenPartialHomeomorph.IsImage.of_image_eq
    rw [hEsource, inter_eq_right.mpr hA]
    exact (inter_eq_right.mpr (himage_target hA)).symm
  let e : OpenPartialHomeomorph RoundCylinderSpace M := C.end_chart.trans Phi.symm
  have hesource : e.source = univ ×ˢ Ioo (-C.epsilon⁻¹) C.epsilon⁻¹ := by
    dsimp only [e]
    rw [OpenPartialHomeomorph.trans_source, hEsource, ← C.end_chart_source]
    apply inter_eq_left.mpr
    intro z hz
    exact C.end_chart_target_subset (C.end_chart.map_source hz)
  have hetarget : e.target = Phi.symm '' C.end_chart.target := by
    dsimp only [e]
    rw [OpenPartialHomeomorph.trans_target'', hEsource,
      inter_eq_right.mpr C.end_chart_target_subset]
  have hetarget_subset : e.target ⊆ U := by
    rw [hetarget]
    rintro y ⟨x, hx, rfl⟩
    exact hsymm (C.end_chart_target_subset hx)
  have hesmooth : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ e e.source := by
    have h := hinverse.comp C.end_chart_smooth
      (fun z hz => C.end_chart_target_subset (C.end_chart.map_source hz))
    simpa only [e, OpenPartialHomeomorph.coe_trans, Function.comp_def,
      C.end_chart_source, ← hesource] using h
  have heinverse : ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞
      e.symm e.target := by
    have h := C.end_chart_inverse_smooth.comp (hsmooth.mono hetarget_subset)
      (fun x hx => by
        change x ∈ (C.end_chart.trans Phi.symm).target at hx
        rw [OpenPartialHomeomorph.trans_target] at hx
        exact hx.2)
    simpa only [e, OpenPartialHomeomorph.coe_trans_symm,
      OpenPartialHomeomorph.symm_symm, Function.comp_def] using h
  have htail (s : ℝ) : e.cylinderTail C.epsilon⁻¹ s =
      Phi.symm '' C.end_chart.cylinderTail C.epsilon⁻¹ s := by
    simp only [OpenPartialHomeomorph.cylinderTail, e,
      OpenPartialHomeomorph.coe_trans, image_comp]
  have hcompact (s : ℝ) (hs : s ∈ Ioo (-C.epsilon⁻¹) C.epsilon⁻¹) :
      IsCompact (U \ e.cylinderTail C.epsilon⁻¹ s) := by
    have hsub := (C.end_chart.cylinderTail_subset_target C.end_chart_source hs.1).trans
      C.end_chart_target_subset
    rw [htail, ← himage_diff hsub]
    exact (C.compact_tail_complement s hs).image_of_continuousOn
      (hinverse.continuousOn.mono sdiff_subset)
  have hcuts (s : ℝ) (hs : s ∈ Ioo (-C.epsilon⁻¹) C.epsilon⁻¹) :
      let T := e.cylinderTail C.epsilon⁻¹ s
      let K := U \ T
      let V := (Phi.symm '' C.closed_core) ∪
        e '' (univ ×ˢ Ioo (-C.epsilon⁻¹) s)
      let S := e '' (univ ×ˢ ({s} : Set ℝ))
      K ⊆ U ∧ IsOpen V ∧ closure V = K ∧ interior K = V ∧
        frontier V = S ∧ frontier K = S ∧ frontier U ⊆ closure T := by
    dsimp only
    let T0 := C.end_chart.cylinderTail C.epsilon⁻¹ s
    let K0 := C.carrier \ T0
    let V0 := C.closed_core ∪ C.end_chart '' (univ ×ˢ Ioo (-C.epsilon⁻¹) s)
    let S0 := C.end_chart '' (univ ×ˢ ({s} : Set ℝ))
    have hT0 : T0 ⊆ C.carrier :=
      (C.end_chart.cylinderTail_subset_target C.end_chart_source hs.1).trans
        C.end_chart_target_subset
    have hK0 : K0 ⊆ C.carrier := sdiff_subset
    have hcut := C.cut_topology s hs
    have hVopen : IsOpen V0 := hcut.2.1
    have hcl0 : closure V0 = K0 := hcut.2.2.1
    have hint0 : interior K0 = V0 := hcut.2.2.2.1
    have hfrontV0 : frontier V0 = S0 := hcut.2.2.2.2.1
    have hfrontK0 : frontier K0 = S0 := hcut.2.2.2.2.2.1
    have hVK : V0 ⊆ K0 := hcl0 ▸ subset_closure
    have hV0 : V0 ⊆ C.carrier := hVK.trans hK0
    have hS0 : S0 ⊆ C.carrier := by
      rintro y ⟨z, hz, rfl⟩
      apply C.end_chart_target_subset
      apply C.end_chart.map_source
      rw [C.end_chart_source]
      exact ⟨mem_univ _, (mem_singleton_iff.mp hz.2).symm ▸ hs⟩
    have hKcompact : IsCompact K0 := C.compact_tail_complement s hs
    have hKclosed : IsClosed (Phi.symm '' K0) :=
      (hKcompact.image_of_continuousOn (hinverse.continuousOn.mono hK0)).isClosed
    have hKtarget := himage_target hK0
    have hVimage := hIsImage hV0
    have hKimage := hIsImage hK0
    have hVimage_open : IsOpen (Phi.symm '' V0) :=
      Phi.symm.isOpen_image_of_subset_source hVopen (hEsource.symm ▸ hV0)
    have hclosure : closure (Phi.symm '' V0) = Phi.symm '' K0 := by
      refine Subset.antisymm (closure_minimal (image_mono hVK) hKclosed) ?_
      rintro y ⟨x, hx, rfl⟩
      exact (hVimage.closure.apply_mem_iff (hEsource.symm ▸ hK0 hx)).2
        (hcl0.symm ▸ hx)
    have hinterior : interior (Phi.symm '' K0) = Phi.symm '' V0 := by
      have h := hKimage.interior.image_eq
      rw [hint0, inter_eq_right.mpr (hEsource.symm ▸ hV0),
        inter_eq_right.mpr (interior_subset.trans hKtarget)] at h
      exact h.symm
    have hfrontV : frontier (Phi.symm '' V0) = Phi.symm '' S0 := by
      have hsub : frontier (Phi.symm '' V0) ⊆ Phi.symm.target := by
        apply frontier_subset_closure.trans
        rw [hclosure]
        exact hKtarget
      have h := hVimage.frontier.image_eq
      rw [hfrontV0, inter_eq_right.mpr (hEsource.symm ▸ hS0),
        inter_eq_right.mpr hsub] at h
      exact h.symm
    have hfrontK : frontier (Phi.symm '' K0) = Phi.symm '' S0 := by
      have hsub : frontier (Phi.symm '' K0) ⊆ Phi.symm.target := by
        apply frontier_subset_closure.trans
        rw [hKclosed.closure_eq]
        exact hKtarget
      have h := hKimage.frontier.image_eq
      rw [hfrontK0, inter_eq_right.mpr (hEsource.symm ▸ hS0),
        inter_eq_right.mpr hsub] at h
      exact h.symm
    have hKeq : U \ e.cylinderTail C.epsilon⁻¹ s = Phi.symm '' K0 := by
      rw [htail, ← himage_diff hT0]
    have hVeq : (Phi.symm '' C.closed_core) ∪
        e '' (univ ×ˢ Ioo (-C.epsilon⁻¹) s) = Phi.symm '' V0 := by
      simp only [e, V0, OpenPartialHomeomorph.coe_trans, image_comp, image_union]
    have hSeq : e '' (univ ×ˢ ({s} : Set ℝ)) = Phi.symm '' S0 := by
      simp only [e, S0, OpenPartialHomeomorph.coe_trans, image_comp]
    have hKU : Phi.symm '' K0 ⊆ U := hEtarget ▸ hKtarget
    have hTU : e.cylinderTail C.epsilon⁻¹ s ⊆ U :=
      (e.cylinderTail_subset_target hesource hs.1).trans hetarget_subset
    have hUnion : U = (Phi.symm '' K0) ∪ e.cylinderTail C.epsilon⁻¹ s := by
      rw [← hKeq]
      ext x
      constructor
      · intro hx
        by_cases ht : x ∈ e.cylinderTail C.epsilon⁻¹ s
        · exact Or.inr ht
        · exact Or.inl ⟨hx, ht⟩
      · rintro (hx | hx)
        · exact hx.1
        · exact hTU hx
    have hUclosure : closure U =
        (Phi.symm '' K0) ∪ closure (e.cylinderTail C.epsilon⁻¹ s) := by
      conv_lhs => rw [hUnion]
      rw [closure_union, hKclosed.closure_eq]
    refine ⟨sdiff_subset, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hVeq]
      exact hVimage_open
    · rw [hVeq, hKeq]
      exact hclosure
    · rw [hKeq, hVeq]
      exact hinterior
    · rw [hVeq, hSeq]
      exact hfrontV
    · rw [hKeq, hSeq]
      exact hfrontK
    · intro x hx
      change x ∈ closure U \ interior U at hx
      rw [hUclosure, hUopen.interior_eq] at hx
      rcases hx.1 with hxK | hxT
      · exact (hx.2 (hKU hxK)).elim
      · exact hxT
  let model : CapModelEquivalence C.model_kind C.puncture U :=
    { model := C.model_equivalence.model
      model_topology := C.model_equivalence.model_topology
      model_charted := C.model_equivalence.model_charted
      model_manifold := C.model_equivalence.model_manifold
      standard_model := C.model_equivalence.standard_model
      standard_smooth := C.model_equivalence.standard_smooth
      forward := fun x => C.model_equivalence.forward (Phi x)
      inverse := fun y => Phi.symm (C.model_equivalence.inverse y)
      inverse_mem := fun y => hsymm (C.model_equivalence.inverse_mem y)
      left_inverse := by
        intro x hx
        rw [C.model_equivalence.left_inverse _ (hmap hx), hleft hx]
      right_inverse := by
        intro y
        rw [hright (C.model_equivalence.inverse_mem y), C.model_equivalence.right_inverse]
      forward_smooth := by
        let _i1 := C.model_equivalence.model_topology
        let _i2 := C.model_equivalence.model_charted
        let _i3 := C.model_equivalence.model_manifold
        exact C.model_equivalence.forward_smooth.comp hsmooth (fun _ hx => hmap hx)
      inverse_smooth := by
        let _i1 := C.model_equivalence.model_topology
        let _i2 := C.model_equivalence.model_charted
        let _i3 := C.model_equivalence.model_manifold
        exact hinverse.comp C.model_equivalence.inverse_smooth
          (fun y _ => C.model_equivalence.inverse_mem y) }
  refine ⟨{
    epsilon := C.epsilon
    epsilon_pos := C.epsilon_pos
    carrier := U
    carrier_open := hUopen
    puncture := C.puncture
    model_kind := C.model_kind
    model_equivalence := model
    end_chart := e
    end_chart_source := hesource
    end_chart_target_subset := hetarget_subset
    end_chart_smooth := hesmooth
    end_chart_inverse_smooth := heinverse
    closed_core := Phi.symm '' C.closed_core
    closed_core_compact := C.closed_core_compact.image_of_continuousOn
      (hinverse.continuousOn.mono (C.closed_core_eq_complement_end ▸ sdiff_subset))
    closed_core_eq_complement_end := ?_
    compact_tail_complement := hcompact
    cut_topology := hcuts
    core := Phi.symm '' C.core
    core_nonempty := C.core_nonempty.image _
    core_subset_closed_core := image_mono C.core_subset_closed_core
    carrier_connected := ?_ }, rfl, rfl, rfl, rfl⟩
  · rw [hetarget, C.closed_core_eq_complement_end,
      himage_diff C.end_chart_target_subset]
  · rw [← himage]
    exact C.carrier_connected.image _ hinverse.continuousOn

end PoincareConjecture.M25.Topology3D
