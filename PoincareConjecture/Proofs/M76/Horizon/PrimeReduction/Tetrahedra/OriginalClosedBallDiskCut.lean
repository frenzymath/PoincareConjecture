import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.ClosedDiskCutBalls

set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Cube" => closedBall (0 : V3) 1
local notation "Sphere" => sphere (0 : V3) 1

theorem exists_original_closed_ball_disk_cut
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {B r d q : Set E} (hB : IsFinitePLBallPair V3 B r)
    (hd : IsFinitePLBallPair (ℝ × ℝ) d q) (hdB : d ⊆ B) (hdr : d ∩ r = q) :
    ∃ C : Bool → Set E,
      (∀ b, IsFinitePLBallPair V3 (C b) ((C b ∩ r) ∪ d)) ∧
      C false ∪ C true = B ∧ C false ∩ C true = d := by
  classical
  obtain ⟨D,hD,hDq⟩ := hd.exists_cube_chart (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm
  have hd2 : IsFinitePLBallPair V2 d q :=
    ⟨hd.1,Disk,isCompact_closedBall _ _,convex_closedBall _ _,
      ⟨0,ball_subset_interior_closedBall (mem_ball_self zero_lt_one)⟩,D,hD,hDq⟩
  obtain ⟨G,f,j,hG,hf,hGf,hGr,hjd,_,P,_,hopen,hPL,_,_⟩ :=
    exists_finitePL_ball_proper_disk_cut hB hd2 hdB hdr
      (fun _ : Empty => (∅ : Set E)) (fun i => i.elim) (fun i => i.elim) (fun i => i.elim)
  obtain ⟨C,s,hC,hunion,hinter,_,hmark⟩ := P.exists_closed_cube_disk_cut_balls hopen hPL
  obtain ⟨p,hp,hGp⟩ := hG.symm
  have hpB : MapsTo p Cube B := fun x hx =>
    (hGp ⟨x,hx⟩) ▸ (G.symm ⟨x,hx⟩).property
  have hpi : InjOn p Cube := by
    intro x hx y hy heq
    have hh : G.symm ⟨x,hx⟩ = G.symm ⟨y,hy⟩ :=
      Subtype.ext (by simpa only [hGp] using heq)
    exact congrArg Subtype.val (G.symm.injective hh)
  have hpf (x : E) (hx : x ∈ B) : p (f x) = x := by
    have hfx : f x ∈ Cube := (hGf ⟨x,hx⟩) ▸ (G ⟨x,hx⟩).property
    rw [←hGp ⟨f x,hfx⟩]
    have hGx : (⟨f x,hfx⟩ : Cube) = G ⟨x,hx⟩ := Subtype.ext (hGf ⟨x,hx⟩).symm
    rw [hGx,G.symm_apply_apply]
  have hpimage : p '' Cube = B := by
    apply Subset.antisymm (image_subset_iff.mpr hpB)
    intro x hx
    exact ⟨G ⟨x,hx⟩,(G ⟨x,hx⟩).property,by rw [hGf]; exact hpf x hx⟩
  have hprim : p '' Sphere = r := by
    apply Subset.antisymm
    · rintro _ ⟨x,hx,rfl⟩
      rw [←hGp ⟨x,sphere_subset_closedBall hx⟩,hGr,G.apply_symm_apply,
        frontier_closedBall _ one_ne_zero]
      exact hx
    · intro x hx
      refine ⟨G ⟨x,hB.1 hx⟩, ?_, ?_⟩
      · rw [←frontier_closedBall _ one_ne_zero]
        exact (hGr _).mp hx
      · rw [hGf]
        exact hpf x (hB.1 hx)
  have hcenter : p '' (j '' Disk) = d := by
    rw [hjd,←image_comp]
    apply Subset.antisymm
    · rintro _ ⟨x,hx,rfl⟩
      simpa only [Function.comp_apply,hpf x (hdB hx)] using hx
    · intro x hx
      exact ⟨x,hx,hpf x (hdB hx)⟩
  have hCCube (b : Bool) : C b ⊆ Cube := by
    intro x hx
    apply hunion.subset
    cases b
    · exact Or.inl hx
    · exact Or.inr hx
  refine ⟨fun b => p '' C b, ?_, ?_, ?_⟩
  · intro b
    have hb := (hC b).image_of_subset hp (hCCube b) hpi
    have hbound : p '' s b = ((p '' C b) ∩ r) ∪ d := by
      rw [hmark b,image_union,hcenter,hpi.image_inter (hCCube b) sphere_subset_closedBall,hprim]
    rw [hbound] at hb
    exact hb.three_coordinate_model (by simp [Module.finrank_prod])
  · rw [←image_union,hunion,hpimage]
  · rw [←hpi.image_inter (hCCube false) (hCCube true),hinter,hcenter]

end PoincareConjecture.M76
