import PoincareConjecture.Proofs.M34.Mathlib.PartialImageTopology
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace OpenPartialHomeomorph

variable {E F H H' M X : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  [TopologicalSpace M] [TopologicalSpace X] [ChartedSpace H M] [ChartedSpace H' X]

theorem exists_regular_sublevel_on_image
    {m : ℕ∞ω} (hm : 1 ≤ m)
    (e : OpenPartialHomeomorph M X)
    (hf : ContMDiffOn I J m e e.source) (hi : ContMDiffOn J I m e.symm e.target)
    {S W : Set M} (hS : S ⊆ e.source) (hW : IsOpen W) (hWs : W ⊆ e.source)
    {x : M} (hxW : x ∈ W)
    (hlocal : ∃ U : Set M, ∃ f : M → ℝ,
      IsOpen U ∧ x ∈ U ∧ (∀ y ∈ U, y ∈ S ↔ f y ≤ 0) ∧ f x = 0 ∧
      ContMDiffOn I 𝓘(ℝ, ℝ) m f U ∧
      ∃ d : TangentSpace I x, mvfderiv I f x d ≠ 0) :
    ∃ V : Set X, ∃ g : X → ℝ,
      IsOpen V ∧ e x ∈ V ∧ V ⊆ e '' W ∧
      (∀ y ∈ V, y ∈ e '' S ↔ g y ≤ 0) ∧ g (e x) = 0 ∧
      ContMDiffOn J 𝓘(ℝ, ℝ) m g V ∧
      ∃ d : TangentSpace J (e x), d ≠ 0 ∧ mvfderiv J g (e x) d ≠ 0 := by
  have hm0 : m ≠ 0 := by
    intro hzero
    simp [hzero] at hm
  obtain ⟨U, f, hU, hxU, hdefine, hzero, hsmooth, d, hd⟩ := hlocal
  let V := e '' (U ∩ W)
  let g : X → ℝ := f ∘ e.symm
  have hUW : U ∩ W ⊆ e.source := fun _ hz => hWs hz.2
  have hVo : IsOpen V := e.isOpen_image_of_subset_source (hU.inter hW) hUW
  have hxV : e x ∈ V := ⟨x, ⟨hxU, hxW⟩, rfl⟩
  have hVt : V ⊆ e.target := by
    rintro _ ⟨z, hz, rfl⟩
    exact e.map_source (hUW hz)
  have hmap : MapsTo e.symm V U := by
    rintro _ ⟨z, hz, rfl⟩
    simpa only [e.left_inv (hUW hz)] using hz.1
  have hg : ContMDiffOn J 𝓘(ℝ, ℝ) m g V :=
    hsmooth.comp (hi.mono hVt) hmap
  have hxs := hWs hxW
  have hfa := ((hf x hxs).contMDiffAt (e.open_source.mem_nhds hxs)).mdifferentiableAt
    hm0
  have hga := ((hg (e x) hxV).contMDiffAt (hVo.mem_nhds hxV)).mdifferentiableAt hm0
  have heq : g ∘ e =ᶠ[𝓝 x] f := by
    filter_upwards [e.open_source.mem_nhds hxs] with z hz
    simp only [g, Function.comp_apply, e.left_inv hz]
  have hderiv := heq.mfderiv_eq (I := I) (I' := 𝓘(ℝ, ℝ))
  have hread : mvfderiv J g (e x) (mfderiv I J e x d) = mvfderiv I f x d := by
    change mfderiv J 𝓘(ℝ, ℝ) g (e x) (mfderiv I J e x d) =
      mfderiv I 𝓘(ℝ, ℝ) f x d
    exact (mfderiv_comp_apply x hga hfa d).symm.trans (congrArg (fun A => A d) hderiv)
  have hnonzero : mvfderiv J g (e x) (mfderiv I J e x d) ≠ 0 := hread ▸ hd
  refine ⟨V, g, hVo, hxV, image_mono inter_subset_right, ?_, ?_, hg,
    mfderiv I J e x d, ?_, hnonzero⟩
  · rintro y ⟨z, hz, rfl⟩
    rw [(e.isImage_image_of_subset_source hS).apply_mem_iff (hUW hz)]
    simpa only [g, Function.comp_apply, e.left_inv (hUW hz)] using hdefine z hz.1
  · simpa only [g, Function.comp_apply, e.left_inv hxs] using hzero
  · intro hzero
    exact hnonzero (by rw [hzero, map_zero])

end OpenPartialHomeomorph
