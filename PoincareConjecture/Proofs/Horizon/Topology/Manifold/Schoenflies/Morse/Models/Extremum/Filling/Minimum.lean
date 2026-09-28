import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Extremum.Filling.CapRange
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Extremum.Filling.Model
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.RegularBand.EndCapTransport



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

open Poincare.Geometry.Euclidean

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1





theorem exists_ambient_filling_of_capped_minimum_disk
    {f : S2 → E3} (hf : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f)
    {v : E3} (hv : ‖v‖ = 1)
    (d : OpenPartialHomeomorph E2 S2) (hds : closedBall 0 1 ⊆ d.source)
    {p : S2} (hp : p ∈ d '' closedBall 0 1) {b : Real}
    (hpb : inner Real v (f p) < b)
    (hboundary : ∀ x ∈ sphere (0 : E2) 1, inner Real v (f (d x)) = b)
    (hunique : ∀ x ∈ d '' closedBall 0 1,
      mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => inner Real v (f q)) x = 0 → x = p)
    (e : OpenPartialHomeomorph E2 S2) (he0 : 0 ∈ e.source) (hep : e 0 = p)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    (hform : ∀ x ∈ e.source, inner Real v (f (e x)) = inner Real v (f p) + ‖x‖ ^ 2)
    {ε : Real} (hε : 0 < ε) (T : OpenPartialHomeomorph (S1 × Real) S2)
    (hTs : T.source = univ ×ˢ Ioo (-ε) ε)
    (γ : S1 → Hemisphere.Plane v)
    (hTcylinder : ∀ q t, t ∈ Ioo (-ε) ε →
      f (T (q, t)) = (b + t) • v + (γ q : E3))
    (hTc : range (fun q : S1 => T (q, 0)) = d '' sphere (0 : E2) 1)
    (hTneg : ∀ q : S1, ∀ t ∈ Ioo (-ε) 0, T (q, t) ∈ d '' ball 0 1)
    {s : Real} (hs : 0 < s)
    (B : (Hemisphere.Plane v) ≃ₘ[Real] (Hemisphere.Plane v))
    (hB : B '' sphere (0 : Hemisphere.Plane v) 1 = range γ)
    (hrange : range f = f '' (d '' closedBall (0 : E2) 1) ∪
      liftPlaneDiffeomorph hv b s hs.ne' B '' boundedCylinderNorthernCap v) :
    ∃ F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      F '' sphere (0 : E3) 1 = range f := by
  let h : S2 → Real := fun q => inner Real v (f q)
  let c := h p
  let K := d '' closedBall (0 : E2) 1
  have hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h :=
    (innerSL Real v).contMDiff.comp hf.contMDiff
  have hzero : (0 : Real) ∈ Ioo (-ε) ε := ⟨by linarith, hε⟩
  have hboundarycap (q : S1) : b • v + (γ q : E3) ∈ f '' K := by
    have hq : T (q, 0) ∈ d '' sphere (0 : E2) 1 := by
      rw [← hTc]
      exact mem_range_self q
    obtain ⟨x, hx, hxt⟩ := hq
    refine ⟨T (q, 0), ⟨x, sphere_subset_closedBall hx, hxt⟩, ?_⟩
    simpa only [add_zero] using hTcylinder q 0 hzero
  have habove := height_above_disk_of_cap_range hv hf.isEmbedding.injective K b hs γ B hB
    hboundarycap hrange
  have hbc : 0 < (b - c) / 4 := by dsimp [c, h]; linarith
  have hη : 0 < Real.sqrt ((b - c) / 4) := Real.sqrt_pos.mpr hbc
  obtain ⟨J, r, hr, hsource, A, D, hDheight, hDupper, _, hprofile, _, hwhole⟩ :=
    exists_capped_minimum_disk_band_straightening hf hv d hds hp hpb hboundary hunique
      habove e he0 hep he hei hform hε T hTs γ hTcylinder hTc hTneg hη
  have hr2 : r ^ 2 < (b - c) / 4 := by
    have hm := mul_pos (sub_pos.mpr hr.2) (add_pos hη hr.1)
    nlinarith [Real.sq_sqrt hbc.le]
  have hsep : c + 2 * r ^ 2 < b := by nlinarith [sq_nonneg r]
  have hab : c + (7 * r / 8) ^ 2 < b := by nlinarith [sq_nonneg r]
  have hsmall := image_minimum_profile_disk c r J f e D hprofile
  rw [hsmall] at hwhole
  have hstrict := (height_bounds_on_disk_of_unique_critical hh d hds hp hpb hboundary hunique).2.2.2
  have htop := closed_disk_top_level_eq_boundary d h b hboundary hstrict
  have hboundaryimage := image_minimum_disk_top_boundary hv hr.1 hab f K
    (d '' sphere (0 : E2) 1) htop D hDheight hwhole
  let P := (Hemisphere.Plane v).orthogonalProjectionOnto
  have hprojfun : (fun q : S1 => P (D (f (T (q, 0))))) = fun q : S1 => A (γ q) := by
    funext q
    rw [hTcylinder q 0 hzero, add_zero, hDupper b (γ q) le_rfl]
    exact congrArg Prod.snd ((heightCoordinates hv).symm_apply_apply (b, A (γ q)))
  have hprojleft : P '' (D '' (f '' (d '' sphere (0 : E2) 1))) =
      range (fun q : S1 => A (γ q)) := by
    rw [← hTc]
    simp only [← range_comp, Function.comp_def]
    exact congrArg Set.range hprojfun
  have hprojright : P '' ((fun q : Hemisphere.Plane v => b • v + (q : E3)) ''
      sphere (0 : Hemisphere.Plane v) r) = sphere (0 : Hemisphere.Plane v) r := by
    rw [image_image]
    have heq : (fun q : Hemisphere.Plane v => P (b • v + (q : E3))) = id := by
      funext q
      exact congrArg Prod.snd ((heightCoordinates hv).symm_apply_apply (b, q))
    rw [heq, image_id]
  have hAγ : range (fun q : S1 => A (γ q)) = sphere (0 : Hemisphere.Plane v) r :=
    hprojleft.symm.trans ((congrArg (fun W : Set E3 => P '' W) hboundaryimage).trans hprojright)
  have hBA : (B.trans A) '' sphere (0 : Hemisphere.Plane v) 1 =
      sphere (0 : Hemisphere.Plane v) r := by
    change (A ∘ B) '' sphere (0 : Hemisphere.Plane v) 1 = _
    rw [image_comp, hB, ← range_comp]
    exact hAγ
  obtain ⟨G, hG⟩ := exists_ambient_filling_of_quadraticMinimum_and_cap hv c hr.1 hsep hs (B.trans A) hBA
  have hDcap := image_upper_cap_of_constant_plane_action hv (le_refl b) hs B A D hDupper
  have hDrange : D '' range f = quadraticMinimumCap v c r ∪
      (fun z : Real × Hemisphere.Plane v => z.1 • v + (z.2 : E3)) ''
        (Icc (c + (7 * r / 8) ^ 2) b ×ˢ sphere (0 : Hemisphere.Plane v) r) ∪
      liftPlaneDiffeomorph hv b s hs.ne' (B.trans A) '' boundedCylinderNorthernCap v := by
    rw [hrange, image_union, hwhole, hDcap]
  refine ⟨G.trans D.symm, ?_⟩
  change (D.symm ∘ G) '' sphere (0 : E3) 1 = _
  rw [image_comp, hG, ← hDrange, image_image]
  simp only [D.symm_apply_apply, image_id']

end Poincare.Manifold.Schoenflies
