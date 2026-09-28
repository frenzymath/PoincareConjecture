import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.NoL3SelectedCapSignedShell
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.NoL3SelectedCapShellSlide
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.NoL3SelectedCapSupportedMotion









set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)
local notation "Sphere" => sphere (0 : V3) 1
local notation "J" => Icc (0 : ℝ) (1/8)
local notation "T" => (norm : V3 → ℝ) ⁻¹' Icc (7/8) 1
local notation "D" => (norm : V3 → ℝ) ⁻¹' Icc (29/32) (31/32)
local notation "Small" => Icc (-(1/32 : ℝ)) (1/32)

theorem exists_original_signed_collar_slide
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} (c : V3 × ℝ → X)
    (hc : PolyhedralPLInCharts e c (Sphere ×ˢ Icc (-1 : ℝ) 1))
    (hci : InjOn c (Sphere ×ˢ Icc (-1 : ℝ) 1))
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ F : X ≃ₜ X,
      EqOn F id (c '' (Sphere ×ˢ Icc (-δ/2) (δ/2)))ᶜ ∧
      F '' (c '' (Sphere ×ˢ Icc (-δ/2) (δ/2))) = c '' (Sphere ×ˢ Icc (-δ/2) (δ/2)) ∧
      (∀ z ∈ Sphere ×ˢ Icc (-δ/2) (δ/2),
        F (c z) = c (z.1,if z.2 ≤ 0 then (3*z.2+δ/2)/2 else (z.2+δ/2)/2)) ∧
      (∀ x ∈ Sphere, F (c (x,0)) = c (x,δ/4)) ∧
      (∀ i j, (e i).symm.trans (F.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      ∀ i j, (e i).symm.trans (F.symm.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3 := by
  obtain ⟨Q,f,hQ,hQnorm,hf,hfi,_,hfv⟩ := exists_original_signed_collar_shell c hc hci hδ hδ1
  obtain ⟨P,H,_,hH,hDT,hfix,hPv,hmove⟩ := exists_selected_cap_shell_slide Q hQ hQnorm
  have hTcompact : IsCompact T := by
    have hT : T = closedBall (0 : V3) 1 ∩ (ball (0 : V3) (7/8))ᶜ := by
      ext x
      simp only [mem_preimage,mem_Icc,mem_inter_iff,mem_compl_iff,
        mem_closedBall,mem_ball,dist_zero_right,not_lt]
      tauto
    rw [hT]
    exact (isCompact_closedBall (0 : V3) 1).inter_right isOpen_ball.isClosed_compl
  obtain ⟨F,hFval,hFfix,hFimage,hforward,hbackward⟩ :=
    exists_original_supported_polyhedral_motion hTcompact hf hfi he H hH hDT hfix
  have hcoord (z : (Sphere ×ˢ Small : Set (V3 × ℝ))) :
      f (P z) = c ((z : V3 × ℝ).1,16*δ*(z : V3 × ℝ).2) := by
    rw [hPv,hfv]
    congr 1
    apply Prod.ext
    · rfl
    · ring
  have himage : f '' D = c '' (Sphere ×ˢ Icc (-δ/2) (δ/2)) := by
    apply Subset.antisymm
    · rintro _ ⟨x,hx,rfl⟩
      let z := P.symm ⟨x,hx⟩
      have hz : f x = c ((z : V3 × ℝ).1,16*δ*(z : V3 × ℝ).2) := by
        simpa only [z,P.apply_symm_apply] using hcoord z
      refine ⟨((z : V3 × ℝ).1,16*δ*(z : V3 × ℝ).2),⟨z.property.1,?_,?_⟩,hz.symm⟩ <;>
        nlinarith [z.property.2.1,z.property.2.2]
    · rintro _ ⟨z,hz,rfl⟩
      let u := z.2/(16*δ)
      have hu : u ∈ Small := by
        constructor
        · apply (le_div_iff₀ (by positivity : 0 < 16*δ)).mpr
          nlinarith [hz.2.1]
        · apply (div_le_iff₀ (by positivity : 0 < 16*δ)).mpr
          nlinarith [hz.2.2]
      refine ⟨P ⟨(z.1,u),hz.1,hu⟩,(P ⟨(z.1,u),hz.1,hu⟩).property,?_⟩
      rw [hcoord]
      have ht : 16*δ*u = z.2 := by dsimp [u]; field_simp
      simpa only [ht]
  have hphysical (z : V3 × ℝ) (hz : z ∈ Sphere ×ˢ Icc (-δ/2) (δ/2)) :
      F (c z) = c (z.1,if z.2 ≤ 0 then (3*z.2+δ/2)/2 else (z.2+δ/2)/2) := by
    let u := z.2/(16*δ)
    have hu : u ∈ Small := by
      constructor
      · apply (le_div_iff₀ (by positivity : 0 < 16*δ)).mpr
        nlinarith [hz.2.1]
      · apply (div_le_iff₀ (by positivity : 0 < 16*δ)).mpr
        nlinarith [hz.2.2]
    let y : (Sphere ×ˢ Small : Set (V3 × ℝ)) := ⟨(z.1,u),hz.1,hu⟩
    have ht : 16*δ*u = z.2 := by dsimp [u]; field_simp
    have hfy : f (P y) = c z := by simpa only [y,ht] using hcoord y
    rw [←hfy,hFval]
    let w := P.symm (H (P y))
    have hfw : f (H (P y)) = c ((w : V3 × ℝ).1,16*δ*(w : V3 × ℝ).2) := by
      simpa only [w,P.apply_symm_apply] using hcoord w
    rw [hfw]
    obtain ⟨hwfirst,hwtime⟩ := hmove y
    change (w : V3 × ℝ).1 = z.1 at hwfirst
    change (w : V3 × ℝ).2 = if u ≤ 0 then (3*u+1/32)/2 else (u+1/32)/2 at hwtime
    rw [hwfirst,hwtime]
    congr 1
    apply Prod.ext
    · rfl
    · by_cases hz0 : z.2 ≤ 0
      · have hu0 : u ≤ 0 := div_nonpos_of_nonpos_of_nonneg hz0 (by positivity)
        rw [if_pos hu0,if_pos hz0]
        nlinarith [ht]
      · have hu0 : ¬u ≤ 0 := by intro h; apply hz0; nlinarith [ht]
        rw [if_neg hu0,if_neg hz0]
        nlinarith [ht]
  refine ⟨F,himage ▸ hFfix,?_,hphysical,?_,hforward,hbackward⟩
  · simpa only [himage] using hFimage
  · intro x hx
    have h := hphysical (x,0) ⟨hx,by constructor <;> linarith⟩
    have ht : (if (0 : ℝ) ≤ 0 then (3*0+δ/2)/2 else (0+δ/2)/2) = δ/4 := by
      rw [if_pos le_rfl]
      ring
    exact h.trans (congrArg (fun u => c (x,u)) ht)

end PoincareConjecture.M76
