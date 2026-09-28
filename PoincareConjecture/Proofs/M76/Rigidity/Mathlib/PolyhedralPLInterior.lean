import PoincareConjecture.Proofs.M76.Mathlib.PolyhedralPLInCharts
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLInterior
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.EmbeddedPatchImage

set_option autoImplicit false

open Set

namespace Geometry

variable {E F X ι : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X F} {f : E → X} {S : Set E}

theorem PolyhedralPLInCharts.mem_interior_image_iff
    (hf : PolyhedralPLInCharts e f S)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F)
    (hemb : Topology.IsEmbedding (fun z : S => f z)) (x : S) :
    f x ∈ interior (f '' S) ↔ (x : E) ∈ interior S := by
  obtain ⟨i, J, V, _, hJS, hV, hxV, hVJ, hfJ, hcoords⟩ := hf.coordinates x
  have hxJ : (x : E) ∈ J.space := hVJ ⟨x, hxV, rfl⟩
  have hxG : f x ∈ (e i).source := hfJ hxJ
  have hinj : InjOn ((e i) ∘ f) J.space := by
    intro y hy z hz hyz
    have hfyz : f y = f z := (e i).injOn (hfJ hy) (hfJ hz) hyz
    have hsub : (⟨y, hJS hy⟩ : S) = ⟨z, hJS hz⟩ := hemb.injective hfyz
    exact congrArg Subtype.val hsub
  obtain ⟨H, hH, hHval⟩ := hcoords.exists_homeomorph_image hinj
  have hfinite : (e i) (f x) ∈ interior (((e i) ∘ f) '' J.space) ↔
      (x : E) ∈ interior J.space := by
    simpa only [hHval, Function.comp_apply] using hH.mem_interior_iff hdim ⟨x, hxJ⟩
  constructor
  · intro hx
    obtain ⟨O, hO, hxO, _, hfull⟩ :=
      hemb.exists_open_chart_image_eq_of_patch (e i) hJS hfJ x V hV hxV hVJ
    let W : Set F := ((e i) '' (interior (f '' S) ∩ (e i).source)) ∩ O
    have hW : IsOpen W :=
      ((e i).isOpen_image_of_subset_source
        (isOpen_interior.inter (e i).open_source) inter_subset_right).inter hO
    have hxW : (e i) (f x) ∈ W := ⟨⟨f x, ⟨hx, hxG⟩, rfl⟩, hxO⟩
    have hWJ : W ⊆ ((e i) ∘ f) '' J.space := by
      rintro y ⟨⟨z, hz, rfl⟩, hyO⟩
      exact (hfull.subset
        ⟨⟨z, ⟨interior_subset hz.1, hz.2⟩, rfl⟩, hyO⟩).1
    exact interior_mono hJS (hfinite.mp ((hW.subset_interior_iff.mpr hWJ) hxW))
  · intro hx
    have hxJint : (x : E) ∈ interior J.space := by
      obtain ⟨A, hA, hAV⟩ := isOpen_induced_iff.mp hV
      have hxA : (x : E) ∈ A := by
        change x ∈ (Subtype.val : S → E) ⁻¹' A
        rwa [hAV]
      have hAJ : A ∩ interior S ⊆ J.space := by
        intro y hy
        have hyV : (⟨y, interior_subset hy.2⟩ : S) ∈ V := by
          rw [← hAV]
          exact hy.1
        exact hVJ ⟨⟨y, interior_subset hy.2⟩, hyV, rfl⟩
      exact ((hA.inter isOpen_interior).subset_interior_iff.mpr hAJ) ⟨hxA, hx⟩
    have ht : interior (((e i) ∘ f) '' J.space) ⊆ (e i).target := by
      rintro y hy
      obtain ⟨z, hz, rfl⟩ := interior_subset hy
      exact (e i).map_source (hfJ hz)
    let W : Set X := (e i).symm '' interior (((e i) ∘ f) '' J.space)
    have hW : IsOpen W := (e i).symm.isOpen_image_of_subset_source isOpen_interior ht
    have hWS : W ⊆ f '' S := by
      rintro y ⟨z, hz, rfl⟩
      obtain ⟨w, hw, rfl⟩ := interior_subset hz
      change (e i).symm ((e i) (f w)) ∈ f '' S
      rw [(e i).left_inv (hfJ hw)]
      exact mem_image_of_mem f (hJS hw)
    exact (hW.subset_interior_iff.mpr hWS)
      ⟨(e i) (f x), hfinite.mpr hxJint, (e i).left_inv hxG⟩

end Geometry
