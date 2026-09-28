import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Cap.Calibration
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Neck.Coordinates.Centered
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Topology.Transport



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

noncomputable section

namespace PoincareConjecture.SingularTimeAssumptions

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {F : GeneralizedRicciFlowData.{u}} {T : ℝ}
  (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
  {t : ℝ} (ht : t ∈ Ico H.reference.tMinus T) (x₀ : H.regularRegion P04)


def regularReferencePartialHomeomorph :
    OpenPartialHomeomorph (F.slice t).carrier (H.regularRegion P04) where
  toFun := SingularRegularLimit.openRetraction (H.regularRegion P04) x₀ ∘
    H.reference.inverse t ht
  invFun := H.regularNeckSourceMap P04 ht
  source := H.reference.inverse t ht ⁻¹' H.reference.regularLimitSet
  target := univ
  map_source' := fun _ _ => mem_univ _
  map_target' := fun y _ => by
    change H.reference.inverse t ht (H.reference.forward t ht y) ∈
      H.reference.regularLimitSet
    rw [H.reference.left_inverse]
    exact y.property
  left_inv' := fun y hy => by
    change H.reference.forward t ht
      (SingularRegularLimit.openRetraction (H.regularRegion P04) x₀
        (H.reference.inverse t ht y) : M) = y
    rw [SingularRegularLimit.openRetraction_val _ _ hy, H.reference.right_inverse]
  right_inv' := fun y _ => by
    change SingularRegularLimit.openRetraction (H.regularRegion P04) x₀
      (H.reference.inverse t ht (H.reference.forward t ht y)) = y
    rw [H.reference.left_inverse, SingularRegularLimit.openRetraction_coe]
  open_source := (H.regularRegion P04).isOpen.preimage
    (H.reference.inverse_smooth t ht).continuous
  open_target := isOpen_univ
  continuousOn_toFun :=
    (SingularRegularLimit.contMDiffOn_openRetraction_comp (H.regularRegion P04) x₀
      (H.reference.inverse_smooth t ht).contMDiffOn (fun _ hy => hy)).continuousOn
  continuousOn_invFun := (H.regularNeckSourceMap_smooth P04 ht).continuous.continuousOn

theorem regularReferencePartialHomeomorph_smooth :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (H.regularReferencePartialHomeomorph P04 ht x₀)
      (H.regularReferencePartialHomeomorph P04 ht x₀).source :=
  SingularRegularLimit.contMDiffOn_openRetraction_comp (H.regularRegion P04) x₀
    (H.reference.inverse_smooth t ht).contMDiffOn (fun _ hy => hy)

theorem regularReferencePartialHomeomorph_symm_smooth :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (H.regularReferencePartialHomeomorph P04 ht x₀).symm
      (H.regularReferencePartialHomeomorph P04 ht x₀).target :=
  (H.regularNeckSourceMap_smooth P04 ht).contMDiffOn

theorem regularReferencePartialHomeomorph_image {S : Set (F.slice t).carrier}
    (hS : H.reference.inverse t ht '' S ⊆ H.reference.regularLimitSet) :
    H.regularReferencePartialHomeomorph P04 ht x₀ '' S =
      H.regularReferencePreimage P04 t ht S := by
  let e := H.regularReferencePartialHomeomorph P04 ht x₀
  have hsource : S ⊆ e.source := fun y hy => hS ⟨y, hy, rfl⟩
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change e.symm (e y) ∈ S
    simpa only [e.left_inv (hsource hy)] using hy
  · intro hx
    refine ⟨e.symm x, hx, e.right_inv (mem_univ _)⟩

theorem regularReferencePreimage_open {S : Set (F.slice t).carrier} (hS : IsOpen S) :
    IsOpen (H.regularReferencePreimage P04 t ht S) :=
  hS.preimage (H.regularNeckSourceMap_smooth P04 ht).continuous

include x₀

theorem regularReferencePreimage_compact {S : Set (F.slice t).carrier}
    (hS : IsCompact S)
    (hcapture : H.reference.inverse t ht '' S ⊆ H.reference.regularLimitSet) :
    IsCompact (H.regularReferencePreimage P04 t ht S) := by
  rw [← H.regularReferencePartialHomeomorph_image P04 ht x₀ hcapture]
  exact hS.image_of_continuousOn
    ((H.regularReferencePartialHomeomorph P04 ht x₀).continuousOn.mono
      (fun y hy => hcapture ⟨y, hy, rfl⟩))

omit x₀ in
theorem regularReferencePreimage_interior (S : Set (F.slice t).carrier) :
    H.regularReferencePreimage P04 t ht (interior S) =
      interior (H.regularReferencePreimage P04 t ht S) :=
  ((H.reference.forward_openEmbedding t ht).comp
    (H.regularRegion P04).isOpen.isOpenEmbedding_subtypeVal).isOpenMap
    |>.preimage_interior_eq_interior_preimage
      (H.regularNeckSourceMap_smooth P04 ht).continuous S

omit x₀ in
theorem regularReferencePreimage_closure (S : Set (F.slice t).carrier) :
    H.regularReferencePreimage P04 t ht (closure S) =
      closure (H.regularReferencePreimage P04 t ht S) :=
  ((H.reference.forward_openEmbedding t ht).comp
    (H.regularRegion P04).isOpen.isOpenEmbedding_subtypeVal).isOpenMap
    |>.preimage_closure_eq_closure_preimage
      (H.regularNeckSourceMap_smooth P04 ht).continuous S

omit x₀ in
theorem regularReferencePreimage_frontier (S : Set (F.slice t).carrier) :
    H.regularReferencePreimage P04 t ht (frontier S) =
      frontier (H.regularReferencePreimage P04 t ht S) :=
  ((H.reference.forward_openEmbedding t ht).comp
    (H.regularRegion P04).isOpen.isOpenEmbedding_subtypeVal).isOpenMap
    |>.preimage_frontier_eq_frontier_preimage
      (H.regularNeckSourceMap_smooth P04 ht).continuous S


def regularReferenceModelEquivalence {S : Set (F.slice t).carrier}
    (hcapture : H.reference.inverse t ht '' S ⊆ H.reference.regularLimitSet)
    {kind : CapModelKind} {p : RealProjectiveThree} (J : CapModelEquivalence kind p S) :
    CapModelEquivalence kind p (H.regularReferencePreimage P04 t ht S) := by
  let e := H.regularReferencePartialHomeomorph P04 ht x₀
  have hS : S ⊆ e.source := fun y hy => hcapture ⟨y, hy, rfl⟩
  rw [← H.regularReferencePartialHomeomorph_image P04 ht x₀ hcapture]
  let : TopologicalSpace J.model := J.model_topology
  let : ChartedSpace (EuclideanSpace ℝ (Fin 3)) J.model := J.model_charted
  let : IsManifold (𝓡 3) ∞ J.model := J.model_manifold
  refine
    { model := J.model
      model_topology := J.model_topology
      model_charted := J.model_charted
      model_manifold := J.model_manifold
      standard_model := J.standard_model
      standard_smooth := J.standard_smooth
      forward := J.forward ∘ e.symm
      inverse := e ∘ J.inverse
      inverse_mem := fun y => mem_image_of_mem e (J.inverse_mem y)
      left_inverse := ?_
      right_inverse := ?_
      forward_smooth := ?_
      inverse_smooth := ?_ }
  · rintro _ ⟨y, hy, rfl⟩
    change e (J.inverse (J.forward (e.symm (e y)))) = e y
    simp only [e.left_inv (hS hy), J.left_inverse y hy]
  · intro y
    simp only [Function.comp_apply, e.left_inv (hS (J.inverse_mem y)), J.right_inverse]
  · apply J.forward_smooth.comp
      ((H.regularReferencePartialHomeomorph_symm_smooth P04 ht x₀).mono
        ((image_mono hS).trans e.image_source_subset))
    rintro _ ⟨y, hy, rfl⟩
    change e.symm (e y) ∈ S
    simpa only [mem_preimage, e.left_inv (hS hy)] using hy
  · exact (H.regularReferencePartialHomeomorph_smooth P04 ht x₀).comp J.inverse_smooth
      (fun y _ => hS (J.inverse_mem y))


theorem regularReferencePreimage_local_defining_function
    {U K B : Set (F.slice t).carrier} (hKU : K ⊆ U)
    (hcapture : H.reference.inverse t ht '' U ⊆ H.reference.regularLimitSet)
    (hlocal : ∀ y ∈ B, ∃ V : Set (F.slice t).carrier, ∃ f : (F.slice t).carrier → ℝ,
      IsOpen V ∧ y ∈ V ∧ V ⊆ U ∧
        (∀ z ∈ V, z ∈ K ↔ f z ≤ 0) ∧ f y = 0 ∧
        ContMDiffOn (𝓡 3) 𝓘(ℝ, ℝ) ∞ f V ∧
        ∃ d : TangentSpace (𝓡 3) y, d ≠ 0 ∧ mvfderiv (𝓡 3) f y d ≠ 0) :
    ∀ y ∈ H.regularReferencePreimage P04 t ht B,
      ∃ V : Set (H.regularRegion P04), ∃ f : H.regularRegion P04 → ℝ,
      IsOpen V ∧ y ∈ V ∧ V ⊆ H.regularReferencePreimage P04 t ht U ∧
        (∀ z ∈ V, z ∈ H.regularReferencePreimage P04 t ht K ↔ f z ≤ 0) ∧ f y = 0 ∧
        ContMDiffOn (𝓡 3) 𝓘(ℝ, ℝ) ∞ f V ∧
        ∃ d : TangentSpace (𝓡 3) y, d ≠ 0 ∧ mvfderiv (𝓡 3) f y d ≠ 0 := by
  let e := H.regularReferencePartialHomeomorph P04 ht x₀
  have hUs : U ⊆ e.source := fun y hy => hcapture ⟨y, hy, rfl⟩
  have hKs : K ⊆ e.source := hKU.trans hUs
  have he := H.regularReferencePartialHomeomorph_smooth P04 ht x₀
  have hei := H.regularReferencePartialHomeomorph_symm_smooth P04 ht x₀
  have hemd : e.MDifferentiable (𝓡 3) (𝓡 3) :=
    ⟨fun _ hz => (he _ hz).mdifferentiableWithinAt (by simp),
      fun _ hz => (hei _ hz).mdifferentiableWithinAt (by simp)⟩
  intro y hy
  obtain ⟨V, f, hV, hxV, hVU, hlevel, hfzero, hf, d, hd, hdf⟩ := hlocal (e.symm y) hy
  have hVs : V ⊆ e.source := hVU.trans hUs
  have hxs : e.symm y ∈ e.source := hVs hxV
  have hright : e (e.symm y) = y := e.right_inv (mem_univ _)
  refine ⟨e '' V, f ∘ e.symm, e.isOpen_image_of_subset_source hV hVs,
    hright ▸ mem_image_of_mem e hxV, ?_, ?_, hfzero, ?_, ?_⟩
  · rw [← H.regularReferencePartialHomeomorph_image P04 ht x₀ hcapture]
    exact image_mono hVU
  · rintro _ ⟨z, hz, rfl⟩
    change e.symm (e z) ∈ K ↔ f (e.symm (e z)) ≤ 0
    simpa only [e.left_inv (hVs hz)] using hlevel z hz
  · apply hf.comp (hei.mono ((image_mono hVs).trans e.image_source_subset))
    rintro _ ⟨z, hz, rfl⟩
    change e.symm (e z) ∈ V
    simpa only [mem_preimage, e.left_inv (hVs hz)] using hz
  · have hback := congrArg (fun L => L d) (hemd.symm_comp_deriv hxs)
    change mfderiv (𝓡 3) (𝓡 3) e.symm (e (e.symm y))
      (mfderiv (𝓡 3) (𝓡 3) e (e.symm y) d) = d at hback
    rw [hright] at hback
    let v : TangentSpace (𝓡 3) y := mfderiv (𝓡 3) (𝓡 3) e (e.symm y) d
    refine ⟨v, ?_, ?_⟩
    · intro hv
      apply hd
      change mfderiv (𝓡 3) (𝓡 3) e.symm y v = d at hback
      simpa only [hv, map_zero] using hback.symm
    · have hfx : MDifferentiableAt (𝓡 3) 𝓘(ℝ, ℝ) f (e.symm y) :=
        ((hf _ hxV).contMDiffAt (hV.mem_nhds hxV)).mdifferentiableAt (by simp)
      rw [mvfderiv_comp_apply y hfx (hemd.mdifferentiableAt_symm (mem_univ _))]
      exact hback ▸ hdf

end PoincareConjecture.SingularTimeAssumptions
