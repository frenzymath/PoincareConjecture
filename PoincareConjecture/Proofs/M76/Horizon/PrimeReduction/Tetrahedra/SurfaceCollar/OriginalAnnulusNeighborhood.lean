import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.SurfaceCollar.MovedDiskAnnulus
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.SquareAnnulusBoundary

set_option autoImplicit false
open Set Geometry PLAnnularStrip
namespace PoincareConjecture.M76
local notation "P2" => (ℝ × ℝ)
local notation "Ann" => squareAnnulus 8 1

theorem exists_original_moved_annulus_open_neighborhood
    {X : Type*} [TopologicalSpace X] [T2Space X]
    {D r : Set P2} (hD : IsCompact D) (hrD : r ⊆ D)
    {f : P2 → X} (hf : ContinuousOn f D)
    {S F : Set X} (hF : IsClosed F)
    (hwhole : (f '' D) ∪ F = S) (hinter : (f '' D) ∩ F = f '' r)
    (H : X ≃ₜ X) {a : P2 → X}
    (haimage : a '' Ann = (f '' D) \ (H '' (f '' (D \ r))))
    (haold : ∀ x ∈ Ann, a x ∈ f '' r ↔ depth 8 x = -1)
    (hanew : ∀ x ∈ Ann, a x ∈ H '' (f '' r) ↔ depth 8 x = 1) :
    ∃ U : Set X, IsOpen U ∧ S ∩ U = a '' interior Ann ∧
      Disjoint U (f '' r) ∧ Disjoint U (H '' (f '' r)) := by
  let U := (F ∪ H '' (f '' D))ᶜ
  have hU : IsOpen U :=
    (hF.union ((hD.image_of_continuousOn hf).image H.continuous).isClosed).isOpen_compl
  have hclosedrim : f '' r ⊆ F := hinter.symm.subset.trans inter_subset_right
  have hnewrim : H '' (f '' r) ⊆ H '' (f '' D) := image_mono (image_mono hrD)
  refine ⟨U,hU,?_,?_,?_⟩
  · apply Subset.antisymm
    · rintro y ⟨hyS,hyU⟩
      have hyD : y ∈ f '' D := (hwhole.symm.subset hyS).resolve_right
        (fun h => hyU (Or.inl h))
      have hyA : y ∈ a '' Ann := haimage.symm.subset
        ⟨hyD,fun h => hyU (Or.inr ((image_mono (image_mono sdiff_subset)) h))⟩
      obtain ⟨x,hx,rfl⟩ := hyA
      have hbounds := mem_squareAnnulus_iff_depth.mp hx
      refine ⟨x,?_,rfl⟩
      rw [interior_squareAnnulus (by norm_num : (2 : ℝ) * 1 < 8)]
      exact ⟨lt_of_le_of_ne hbounds.1 (fun h => hyU
        (Or.inl (hclosedrim ((haold x hx).mpr h.symm)))),
        lt_of_le_of_ne hbounds.2 (fun h => hyU
          (Or.inr (hnewrim ((hanew x hx).mpr h))))⟩
    · rintro _ ⟨x,hx,rfl⟩
      have hxA := interior_subset hx
      have hxdepth : depth 8 x ∈ Ioo (-1 : ℝ) 1 := by
        simpa only [interior_squareAnnulus (by norm_num : (2 : ℝ) * 1 < 8),
          mem_preimage,mem_Ioo] using hx
      have hximage := haimage.subset (mem_image_of_mem a hxA)
      refine ⟨hwhole.subset (Or.inl hximage.1),?_⟩
      rintro (hF | hH)
      · have h := (haold x hxA).mp (hinter.subset ⟨hximage.1,hF⟩)
        linarith [hxdepth.1]
      · obtain ⟨y,⟨z,hz,rfl⟩,hy⟩ := hH
        by_cases hzr : z ∈ r
        · have h := (hanew x hxA).mp ⟨f z,⟨z,hzr,rfl⟩,hy⟩
          linarith [hxdepth.2]
        · exact hximage.2 ⟨f z,⟨z,⟨hz,hzr⟩,rfl⟩,hy⟩
  · exact disjoint_left.mpr (fun _ hx hr => hx (Or.inl (hclosedrim hr)))
  · exact disjoint_left.mpr (fun _ hx hr => hx (Or.inr (hnewrim hr)))

end PoincareConjecture.M76
