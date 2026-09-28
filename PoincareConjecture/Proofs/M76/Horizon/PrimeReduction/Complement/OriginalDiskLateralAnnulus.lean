import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.StandardDiskBandAnnulus
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Regions.OriginalDiskStripBall









set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip

namespace PoincareConjecture.M76.OriginalDiskProduct

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1
local notation "Annulus" => squareAnnulus 8 1
local notation "J" => Icc (-(1 / 2 : ℝ)) (1 / 2)

theorem exists_lateral_annulus
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e R j) :
    ∃ f : P2 → X, PolyhedralPLInCharts e f Annulus ∧ InjOn f Annulus ∧
      f '' Annulus = P.map '' (Q ×ˢ J) ∧
      ∀ b : Bool, (fun z : Annulus => f z) '' {z | depth 8 z = if b then 1 else -1} =
        P.map '' (Q ×ˢ {if b then (1 / 2 : ℝ) else -(1 / 2)}) := by
  obtain ⟨a,ha,hai,haimage,hadepth⟩ := exists_standard_disk_band_annulus
  have hfull : Q ×ˢ J ⊆ D ×ˢ Icc (-1 : ℝ) 1 := by
    rintro z ⟨hzQ,hzt⟩
    exact ⟨sphere_subset_closedBall hzQ,by linarith [hzt.1],by linarith [hzt.2]⟩
  have haMaps : MapsTo a Annulus (Q ×ˢ J) := fun x hx =>
    haimage.subset (mem_image_of_mem a hx)
  have hf : PolyhedralPLInCharts e (P.map ∘ a) Annulus := by
    obtain ⟨K,hK,hKs,hfaces⟩ := ha
    rw [← hKs]
    exact P.polyhedral.comp_finitePiecewiseAffineOn K hK ⟨K,hK,rfl,hfaces⟩
      (fun x hx => hfull (haMaps (hKs.subset hx)))
  have hfi : InjOn (P.map ∘ a) Annulus := by
    intro x hx y hy hxy
    exact hai hx hy (P.injective (hfull (haMaps hx)) (hfull (haMaps hy)) hxy)
  refine ⟨P.map ∘ a,hf,hfi,
    (image_image P.map a Annulus).symm.trans (congrArg (image P.map) haimage),?_⟩
  intro b
  apply Subset.antisymm
  · rintro _ ⟨z,hz,rfl⟩
    refine ⟨a z,⟨(haMaps z.property).1,?_⟩,rfl⟩
    change (a z).2 = _
    rw [hadepth z z.property,hz]
    cases b <;> norm_num
  · rintro _ ⟨z,hz,rfl⟩
    have hzJ : z ∈ Q ×ˢ J := by
      refine ⟨hz.1,?_⟩
      rw [show z.2 = if b then (1 / 2 : ℝ) else -(1 / 2) from hz.2]
      cases b <;> norm_num
    obtain ⟨x,hx,hax⟩ := haimage.symm.subset hzJ
    refine ⟨⟨x,hx⟩,?_,congrArg P.map hax⟩
    change depth 8 x = _
    have hh := hadepth x hx
    rw [hax] at hh
    have ht : z.2 = if b then (1 / 2 : ℝ) else -(1 / 2) := hz.2
    cases b <;> simp only [Bool.false_eq_true,if_false,if_true] at ht ⊢ <;> linarith

end PoincareConjecture.M76.OriginalDiskProduct
