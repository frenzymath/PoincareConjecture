import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.SurfaceCollar.OriginalInteriorCap
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Boundary.Annuli.NestedPolygonAnnulus

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)

theorem exists_moved_disk_coordinates
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3}
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (hcover : ∀ y, ∃ i, y ∈ (e i).source)
    {D r : Set P2} (hD : IsFinitePLBallPair P2 D r)
    {f : P2 → X} (hf : PolyhedralPLInCharts e f D) (hfi : InjOn f D)
    (H : X ≃ₜ X)
    (hH : ∀ i j, (e i).symm.trans (H.toOpenPartialHomeomorph.trans (e j)) ∈
      piecewiseAffineGroupoid V3)
    (hnest : H '' (f '' D) ⊆ (f '' D) \ (f '' r)) :
    ∃ q : P2 → P2,
      FinitePiecewiseAffineOn q D ∧ InjOn q D ∧
      (∀ x ∈ D, f (q x) = H (f x)) ∧
      q '' D ⊆ interior D ∧
      IsFinitePLBallPair P2 (q '' D) (q '' r) ∧
      f '' (q '' D) = H '' (f '' D) ∧ f '' (q '' r) = H '' (f '' r) := by
  classical
  let : CompactSpace D := isCompact_iff_compactSpace.mp hD.isCompact
  let b : D ≃ₜ f '' D := Continuous.homeoOfEquivCompactToT2
    (f := Equiv.Set.imageOfInjOn f D hfi) (hf.continuousOn.domRestrict.subtype_mk _)
  have hb (x : D) : (b x : X) = f x := rfl
  let q : P2 → P2 := fun x => if hx : x ∈ D then
    b.symm ⟨H (f x),(hnest (mem_image_of_mem H (mem_image_of_mem f hx))).1⟩ else 0
  have hqval (x : D) : q x =
      (b.symm ⟨H (f x),(hnest (mem_image_of_mem H (mem_image_of_mem f x.property))).1⟩ : P2) := by
    simp only [q,dif_pos x.property]
  have hqD : MapsTo q D D := by
    intro x hx
    rw [hqval ⟨x,hx⟩]
    exact (b.symm _).property
  have hqeq (x : P2) (hx : x ∈ D) : f (q x) = H (f x) := by
    rw [hqval ⟨x,hx⟩,←hb]
    exact congrArg Subtype.val (b.apply_symm_apply _)
  have hqcont : ContinuousOn q D := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have hh := continuous_subtype_val.comp (b.symm.continuous.comp
      ((H.continuous.comp hf.continuousOn.domRestrict).subtype_mk
        (fun x => (hnest (mem_image_of_mem H (mem_image_of_mem f x.property))).1)))
    convert hh using 1
    funext x
    exact hqval x
  obtain ⟨J,_,hJ,hJs,_,_⟩ := hD.exists_finite_carrier_and_rim_complexes
  have hHf : PolyhedralPLInCharts e (H ∘ f) D :=
    hJs ▸ (hJs.symm ▸ hf).comp_chart_homeomorph J hJ H hcover hH
  have hqPL : FinitePiecewiseAffineOn q D := by
    exact hJs ▸ hf.finitePiecewiseAffineOn_lift he hfi J hJ
      (hqcont.mono hJs.subset) (fun _ hx => hqD (hJs.subset hx))
      (hJs.symm ▸ hHf.congr (fun x hx => (hqeq x hx).symm))
  have hqi : InjOn q D := by
    intro x hx y hy hxy
    exact hfi hx hy (H.injective ((hqeq x hx).symm.trans
      ((congrArg f hxy).trans (hqeq y hy))))
  have hinner : q '' D ⊆ interior D := by
    rintro _ ⟨x,hx,rfl⟩
    apply (mem_interior_iff_notMem_frontier (hqD hx)).mpr
    rw [hD.frontier_eq_of_finrank_eq rfl]
    intro hqr
    exact (hnest (mem_image_of_mem H (mem_image_of_mem f hx))).2
      ⟨q x,hqr,hqeq x hx⟩
  refine ⟨q,hqPL,hqi,hqeq,hinner,hD.image hqPL hqi,?_,?_⟩
  · rw [image_image,image_image]
    exact image_congr (fun x hx => hqeq x hx)
  · rw [image_image,image_image]
    exact image_congr (fun x hx => hqeq x (hD.1 hx))

end PoincareConjecture.M76
