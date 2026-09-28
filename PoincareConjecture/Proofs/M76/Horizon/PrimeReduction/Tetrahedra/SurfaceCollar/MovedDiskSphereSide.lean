import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.SurfaceCollar.OriginalSubdiskUniqueness
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.SurfaceCollar.MovedDiskCoordinates
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.SurfaceCollar.OriginalRawCircleCaps

set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "Sphere" => sphere (0 : V3) 1

theorem ChartwisePLSphere.moved_disk_eq_opposite_side
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {S : Set X}
    (s : ChartwisePLSphere e S)
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (hcover : ∀ y, ∃ i, y ∈ (e i).source)
    {D r : Set P2} (hD : IsFinitePLBallPair P2 D r)
    {f : P2 → X} (hf : PolyhedralPLInCharts e f D) (hfi : InjOn f D)
    {F : Set X} (hF : IsClosed F) (hwhole : (f '' D) ∪ F = S)
    (hinter : (f '' D) ∩ F = f '' r) (hrne : (f '' r).Nonempty)
    (H : X ≃ₜ X)
    (hH : ∀ i j, (e i).symm.trans (H.toOpenPartialHomeomorph.trans (e j)) ∈
      piecewiseAffineGroupoid V3)
    (hnest : H '' (f '' D) ⊆ (f '' D) \ (f '' r))
    (d : Fin 2 → Set V3) {q : Set V3}
    (hd : ∀ i, IsFinitePLBallPair P2 (d i) q)
    (hdwhole : d 0 ∪ d 1 = Sphere) (hdinter : d 0 ∩ d 1 = q)
    (hrim : s.map '' q = H '' (f '' r)) (b : Fin 2)
    (havoid : Disjoint (f '' r) (s.map '' d b.rev)) :
    H '' (f '' D) = s.map '' d b.rev ∧
      (s.map '' d b) ∩ (f '' D) = (f '' D) \ (H '' (f '' (D \ r))) := by
  classical
  have hdS (i : Fin 2) : d i ⊆ Sphere := by
    fin_cases i
    · exact subset_union_left.trans hdwhole.subset
    · exact subset_union_right.trans hdwhole.subset
  have hsS : s.map '' Sphere = S := by
    apply Subset.antisymm
    · rintro _ ⟨x,hx,rfl⟩
      rw [s.map_eq ⟨x,hx⟩]
      exact (s.parametrization ⟨x,hx⟩).property
    · intro y hy
      obtain ⟨x,hx⟩ := s.parametrization.surjective ⟨y,hy⟩
      exact ⟨x,x.property,(s.map_eq x).trans (congrArg Subtype.val hx)⟩
  have hsi : InjOn s.map Sphere := by
    intro x hx y hy hxy
    rw [s.map_eq ⟨x,hx⟩,s.map_eq ⟨y,hy⟩] at hxy
    exact congrArg Subtype.val (s.parametrization.injective (Subtype.ext hxy))
  have hsideS : s.map '' d b.rev ⊆ S := (image_mono (hdS _)).trans hsS.subset
  have hsideconn := (hd b.rev).isConnected.image s.map
    (s.piecewiseAffine.continuousOn.mono (hdS _))
  have hfdclosed := (hD.isCompact.image_of_continuousOn hf.continuousOn).isClosed
  have hsplit := isPreconnected_iff_subset_of_disjoint_closed.mp hsideconn.isPreconnected
    (f '' D) F hfdclosed hF (hsideS.trans hwhole.symm.subset)
    (by rw [hinter,inter_comm,disjoint_iff_inter_eq_empty.mp havoid])
  have hsideD : s.map '' d b.rev ⊆ f '' D := by
    rcases hsplit with h | h
    · exact h
    · obtain ⟨x,hxr⟩ := hrne
      have hHx : H x ∈ s.map '' d b.rev :=
        image_mono (hd b.rev).1 (hrim.symm.subset (mem_image_of_mem H hxr))
      have hn := hnest (mem_image_of_mem H (image_mono hD.1 hxr))
      exact (hn.2 (hinter.subset ⟨hn.1,h hHx⟩)).elim
  obtain ⟨J,_,hJ,hJs,_,_⟩ := hD.exists_finite_carrier_and_rim_complexes
  have hHf : PolyhedralPLInCharts e (H ∘ f) D :=
    hJs ▸ (hJs.symm ▸ hf).comp_chart_homeomorph J hJ H hcover hH
  have hHfi : InjOn (H ∘ f) D := fun x hx y hy h => hfi hx hy (H.injective h)
  obtain ⟨L,_,hL,hLs,_,_⟩ := (hd b.rev).exists_finite_carrier_and_rim_complexes
  have hsidePL : PolyhedralPLInCharts e s.map (d b.rev) :=
    hLs ▸ s.piecewiseAffine.restrict_finite L hL (hLs.subset.trans (hdS _))
  have heq : H '' (f '' D) = s.map '' d b.rev := by
    rw [←image_comp]
    exact original_subdisk_images_eq_of_same_rim he hD hD (hd b.rev) hf hfi
      hHf hHfi hsidePL (hsi.mono (hdS _))
      (by simpa only [image_comp] using hnest.trans sdiff_subset) hsideD
      (by simpa only [image_comp] using hrim.symm)
  have hretwhole : (s.map '' d b) ∪ (s.map '' d b.rev) = S := by
    rw [←image_union]
    have h : d b ∪ d b.rev = Sphere := by
      fin_cases b
      · exact hdwhole
      · simpa [union_comm] using hdwhole
    rw [h,hsS]
  have hretinter : (s.map '' d b) ∩ (s.map '' d b.rev) = H '' (f '' r) := by
    rw [←hsi.image_inter (hdS b) (hdS b.rev)]
    have h : d b ∩ d b.rev = q := by
      fin_cases b
      · exact hdinter
      · simpa [inter_comm] using hdinter
    rw [h,hrim]
  have hdiff : H '' (f '' (D \ r)) = (H '' (f '' D)) \ (H '' (f '' r)) := by
    rw [←image_comp,←image_comp,←image_comp]
    simpa only [inter_eq_right.mpr hD.1] using (hHfi.image_sdiff (t := r))
  refine ⟨heq,?_⟩
  rw [hdiff,heq]
  ext x
  constructor
  · rintro ⟨hxret,hxf⟩
    exact ⟨hxf,fun hx => hx.2 (hretinter.subset ⟨hxret,hx.1⟩)⟩
  · rintro ⟨hxf,hxn⟩
    have hxS := hwhole.subset (Or.inl hxf)
    rcases hretwhole.symm.subset hxS with hret | hother
    · exact ⟨hret,hxf⟩
    · have hxr : x ∈ H '' (f '' r) := by
        by_contra hn
        exact hxn ⟨hother,hn⟩
      exact ⟨(hretinter.symm.subset hxr).1,hxf⟩

end PoincareConjecture.M76
