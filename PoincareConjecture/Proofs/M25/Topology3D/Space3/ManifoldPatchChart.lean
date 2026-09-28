import PoincareConjecture.Proofs.M25.Topology3D.Space3.ManifoldOpenChart













set_option autoImplicit false

open Set Function Filter
open scoped ContDiff Manifold Topology

namespace PoincareConjecture.M25.Topology3D

variable {E F M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
variable [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
variable [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ, F) ∞ N]



theorem exists_manifold_patch_local_inverse (f : M → N) {U : Set M}
    (hU : IsOpen U) (hf : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f U)
    (x : M) (hx : x ∈ U)
    (hb : Bijective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x)) :
    ∃ e : OpenPartialHomeomorph M N, x ∈ e.source ∧ e.source ⊆ U ∧
      EqOn e f e.source ∧ ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ e.symm e.target := by
  let c := chartAt F (f x)
  let V := U ∩ f ⁻¹' c.source
  have hV : IsOpen V := hf.continuousOn.isOpen_inter_preimage hU c.open_source
  have hcx : f x ∈ c.source := mem_chart_source F (f x)
  have hxV : x ∈ V := ⟨hx, hcx⟩
  have hcs : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, F) ∞ c c.source := contMDiffOn_chart
  have hg : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ (c ∘ f) V :=
    hcs.comp (hf.mono inter_subset_left) (fun _ hy => hy.2)
  have hc := mdifferentiable_chart (I := 𝓘(ℝ, F)) (f x)
  have hgb : Bijective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) (c ∘ f) x) := by
    rw [mfderiv_comp x (hc.mdifferentiableAt hcx)
      ((hf.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp))]
    exact (hc.mfderiv_bijective hcx).comp hb
  obtain ⟨e0, hx0, h0V, h0, h0i⟩ :=
    exists_manifold_source_local_inverse (c ∘ f) hV hg x hxV hgb
  let e := e0.trans c.symm
  have hxe : x ∈ e.source := by
    refine ⟨hx0, ?_⟩
    change e0 x ∈ c.target
    rw [h0 hx0]
    exact c.map_source hcx
  have hef : EqOn e f e.source := by
    intro y hy
    change c.symm (e0 y) = f y
    rw [h0 hy.1]
    exact c.left_inv (h0V hy.1).2
  have hei : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ e.symm e.target :=
    h0i.comp (hcs.mono inter_subset_left) (fun _ hy => hy.2)
  exact ⟨e, hxe, fun y hy => (h0V hy.1).1, hef, hei⟩

variable (f : M → N) {U : Set M} (hU : IsOpen U)
variable (hf : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f U)
variable (hb : ∀ x ∈ U, Bijective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x))

include hU hf hb



theorem manifold_patch_isOpen_image {T : Set M} (hT : IsOpen T) (hTU : T ⊆ U) :
    IsOpen (f '' T) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro y ⟨x, hx, rfl⟩
  obtain ⟨e, hxe, _, he, _⟩ :=
    exists_manifold_patch_local_inverse f hU hf x (hTU hx) (hb x (hTU hx))
  have hopen : IsOpen (e '' (e.source ∩ T)) :=
    e.isOpen_image_of_subset_source (e.open_source.inter hT) inter_subset_left
  apply mem_of_superset (hopen.mem_nhds ⟨x, ⟨hxe, hx⟩, he hxe⟩)
  rintro z ⟨v, hv, rfl⟩
  exact ⟨v, hv.2, (he hv.1).symm⟩



theorem manifold_patch_isOpenMap_restrict : IsOpenMap (U.domRestrict f) := by
  intro T hT
  have hopen : IsOpen (Subtype.val '' T : Set M) :=
    hU.isOpenEmbedding_subtypeVal.isOpenMap T hT
  have hsub : (Subtype.val '' T : Set M) ⊆ U := by
    rintro x ⟨y, _, rfl⟩
    exact y.2
  rw [domRestrict_eq, image_comp]
  exact manifold_patch_isOpen_image f hU hf hb hopen hsub

variable [Nonempty M] (hi : InjOn f U)



noncomputable def manifoldPatchChart : OpenPartialHomeomorph M N :=
  OpenPartialHomeomorph.ofContinuousOpenRestrict (hi.toPartialEquiv f U)
    hf.continuousOn (manifold_patch_isOpenMap_restrict f hU hf hb) hU


@[simp] theorem manifoldPatchChart_apply (x : M) :
    manifoldPatchChart f hU hf hb hi x = f x := rfl


@[simp] theorem manifoldPatchChart_source :
    (manifoldPatchChart f hU hf hb hi).source = U := rfl


@[simp] theorem manifoldPatchChart_target :
    (manifoldPatchChart f hU hf hb hi).target = f '' U := rfl



theorem manifoldPatchChart_symm_contMDiffOn :
    ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ (manifoldPatchChart f hU hf hb hi).symm (f '' U) := by
  let e := manifoldPatchChart f hU hf hb hi
  intro y hy
  have hx : e.symm y ∈ U := e.map_target hy
  obtain ⟨l, hxl, hlU, hlf, hls⟩ :=
    exists_manifold_patch_local_inverse f hU hf (e.symm y) hx (hb _ hx)
  have hly : y ∈ l.target := by
    have hlimage : l (e.symm y) = y := (hlf hxl).trans (e.right_inv hy)
    exact hlimage ▸ l.map_source hxl
  have hagree : e.symm =ᶠ[𝓝 y] l.symm := by
    filter_upwards [(e.open_target.inter l.open_target).mem_nhds ⟨hy, hly⟩] with z hz
    apply hi (e.map_target hz.1) (hlU (l.map_target hz.2))
    exact (e.right_inv hz.1).trans ((hlf (l.map_target hz.2)).symm.trans (l.right_inv hz.2)).symm
  exact ((hls.contMDiffAt (l.open_target.mem_nhds hly)).congr_of_eventuallyEq
    hagree).contMDiffWithinAt

end PoincareConjecture.M25.Topology3D
