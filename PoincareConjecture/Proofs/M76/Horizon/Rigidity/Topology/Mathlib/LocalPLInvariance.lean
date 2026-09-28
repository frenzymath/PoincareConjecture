import PoincareConjecture.Proofs.M76.Mathlib.FinitePLInterior
import PoincareConjecture.Proofs.M76.Mathlib.LocallyPiecewiseAffine
import Mathlib.Topology.IsLocalHomeomorph









set_option autoImplicit false
open Set Topology

namespace Geometry

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {f : E → F} {U : Set E}

theorem LocallyPiecewiseAffineOn.isOpen_image_of_injOn
    (hf : LocallyPiecewiseAffineOn f U)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F) (hinj : InjOn f U) :
    IsOpen (f '' U) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro y ⟨x, hx, rfl⟩
  obtain ⟨K, hK, hxK, hKU, hfK⟩ := hf x hx
  have hfinite : FinitePiecewiseAffineOn f K.space := ⟨K, hK, rfl, hfK⟩
  exact Filter.mem_of_superset
    (mem_interior_iff_mem_nhds.mp (hfinite.mem_interior_image hdim (hinj.mono hKU) hxK))
    (image_mono hKU)

set_option backward.isDefEq.respectTransparency false in
theorem LocallyPiecewiseAffineOn.isOpenEmbedding_domRestrict
    (hf : LocallyPiecewiseAffineOn f U)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F) (hinj : InjOn f U) :
    IsOpenEmbedding (U.domRestrict f) := by
  apply IsOpenEmbedding.of_continuous_injective_isOpenMap hf.continuousOn.domRestrict
    (injOn_iff_injective.mp hinj)
  intro V hV
  have hW : IsOpen ((Subtype.val : U → E) '' V) := hf.isOpen.isOpenMap_subtype_val V hV
  have hWU : (Subtype.val : U → E) '' V ⊆ U := by
    rintro _ ⟨x, _, rfl⟩
    exact x.property
  have h := (hf.mono hW hWU).isOpen_image_of_injOn hdim (hinj.mono hWU)
  simpa only [image_image, Function.comp_def, Set.domRestrict] using h

theorem LocallyPiecewiseAffineOn.isLocalHomeomorphOn_of_locallyInjective
    (hf : LocallyPiecewiseAffineOn f U)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F)
    (hinj : IsLocallyInjective (U.domRestrict f)) :
    IsLocalHomeomorphOn f U := by
  apply (isLocalHomeomorphOn_iff_isOpenEmbedding_restrict U).mpr
  intro x hx
  obtain ⟨V, hV, hxV, hinjV⟩ := hinj ⟨x, hx⟩
  let W := (Subtype.val : U → E) '' V
  have hW : IsOpen W := hf.isOpen.isOpenMap_subtype_val V hV
  have hWU : W ⊆ U := by
    rintro _ ⟨y, _, rfl⟩
    exact y.property
  have hfW : InjOn f W := by
    rintro y ⟨y', hy, rfl⟩ z ⟨z', hz, rfl⟩ heq
    exact congrArg Subtype.val (hinjV hy hz heq)
  exact ⟨W, hW.mem_nhds ⟨⟨x, hx⟩, hxV, rfl⟩,
    (hf.mono hW hWU).isOpenEmbedding_domRestrict hdim hfW⟩

end Geometry
