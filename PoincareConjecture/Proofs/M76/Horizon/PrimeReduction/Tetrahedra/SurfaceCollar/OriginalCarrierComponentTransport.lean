import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.SurfaceCollar.CarrierComponentTransport
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.SurfaceCollar.OriginalSphereCapReplacement

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem transport_original_carrier_component
    {X E ι : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3}
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {g : E → X} (hg : PolyhedralPLInCharts e g K.space) (hgi : InjOn g K.space)
    {A B T Z : Set E} (hAK : A ⊆ K.space) (hBK : B ⊆ K.space)
    (hTK : T ⊆ K.space) (H : A ≃ₜ B) {h : E → E}
    (hval : ∀ x : A, h x = (H x : E))
    (hT : ∀ x ∈ A, h x ∈ T ↔ x ∈ T) (hZA : Z ⊆ A) (hZT : Z ⊆ T)
    (hcc : ∀ x ∈ g '' Z,
      connectedComponentIn ((g '' A) ∩ (g '' T)) x = g '' Z) :
    ∀ x ∈ g '' (h '' Z),
      connectedComponentIn ((g '' B) ∩ (g '' T)) x = g '' (h '' Z) := by
  classical
  let : CompactSpace K.space := isCompact_iff_compactSpace.mp (K.isCompact_space_of_finite hK)
  let J := hg.continuousOn.domRestrict.isClosedEmbedding
    (fun x y h => Subtype.ext (hgi x.property y.property h)) |>.isEmbedding.toHomeomorph
  let pr : K.space ≃ₜ (g '' K.space) :=
    J.trans (Homeomorph.setCongr (image_eq_range g K.space).symm)
  have hpr (x : K.space) : g x = (pr x : X) := rfl
  have himage : h '' (A ∩ T) = B ∩ T := by
    apply Subset.antisymm
    · rintro _ ⟨x,⟨hxA,hxT⟩,rfl⟩
      refine ⟨?_,(hT x hxA).mpr hxT⟩
      rw [hval ⟨x,hxA⟩]
      exact (H ⟨x,hxA⟩).property
    · intro y hy
      let x := H.symm ⟨y,hy.1⟩
      have hx : h x = y := by rw [hval x]; exact congrArg Subtype.val (H.apply_symm_apply _)
      exact ⟨x,⟨x.property,(hT x x.property).mp (hx.symm ▸ hy.2)⟩,hx⟩
  have hinter (W : Set E) (hWK : W ⊆ K.space) :
      g '' (W ∩ T) = (g '' W) ∩ (g '' T) :=
    image_inter_on (fun x hx y hy hxy => hgi (hTK hx) (hWK hy) hxy)
  rintro _ ⟨_,⟨z,hz,rfl⟩,rfl⟩
  have hzAT : z ∈ A ∩ T := ⟨hZA hz,hZT hz⟩
  have hold := pr.image_connectedComponentIn_of_values hpr
    (inter_subset_left.trans hAK) hzAT
  rw [hinter A hAK,hcc _ (mem_image_of_mem g hz)] at hold
  have hold' : connectedComponentIn (A ∩ T) z = Z :=
    (hgi.image_eq_image_iff
      ((connectedComponentIn_subset _ _).trans (inter_subset_left.trans hAK))
      (hZA.trans hAK)).mp hold
  have hmove := H.image_connectedComponentIn_of_values hval inter_subset_left hzAT
  rw [hold',himage] at hmove
  have hznew : h z ∈ B ∩ T := himage.subset (mem_image_of_mem h hzAT)
  have hnew := pr.image_connectedComponentIn_of_values hpr
    (inter_subset_left.trans hBK) hznew
  rw [hinter B hBK,←hmove] at hnew
  exact hnew.symm

end PoincareConjecture.M76
