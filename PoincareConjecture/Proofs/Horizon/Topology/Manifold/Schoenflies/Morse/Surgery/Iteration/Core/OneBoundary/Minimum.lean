import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.OneBoundary.Extrema
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.CapSlice.Disks
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.CapSlice.Normalization
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Extremum.Filling.Minimum



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Metric Filter Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies

open Poincare.Geometry.Euclidean

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1




theorem exists_filling_of_positive_cap_complement
    {v : E3} {g : S2 → E3}
    (hgEmb : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ g)
    {B : Set Real} (D : SphereSurgeryCoreCap v g B) (hs : 0 < D.scale)
    (p : S2) (hp : p ∉ D.chart '' ball (0 : E2) 1)
    (hpheight : inner Real v (g p) < D.center)
    (hunique : ∀ q ∉ D.chart '' ball (0 : E2) 1,
      mfderiv (𝓡 2) 𝓘(Real, Real) (fun y => inner Real v (g y)) q = 0 → q = p)
    (χ : OpenPartialHomeomorph E2 S2) (hχ0 : 0 ∈ χ.source) (hχp : χ 0 = p)
    (hχ : ContMDiffOn (𝓡 2) (𝓡 2) ∞ χ χ.source)
    (hχi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ χ.symm χ.target)
    (hχtarget : χ.target ⊆ (D.chart '' ball (0 : E2) 1)ᶜ)
    (hχform : ∀ x ∈ χ.source,
      inner Real v (g (χ x)) = inner Real v (g p) + ‖x‖ ^ 2) :
    ∃ F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      F '' sphere (0 : E3) 1 = range g := by
  obtain ⟨ε, hε, hεa, hε1, J, T, hTs, hT, hTi, hformula,
    d, e, hds, hes, hd, hdi, he, hei, hdc, hdo, heclosed, heopen,
    hdcenter, hecenter, hTneg, _⟩ :=
    D.exists_truncated_cap_disks hgEmb (a := 1/2) (by norm_num) (by norm_num)
  let b := D.center + D.scale*(1/2)
  let H : S2 → Real := fun q => (inner Real v (g q)-D.center)/D.scale
  have hcorekeep : (D.chart '' ball (0 : E2) 1)ᶜ ⊆ e '' closedBall (0 : E2) 1 := by
    intro q hq
    rw [heclosed, hdo]
    rintro ⟨hqD, hqheight⟩
    have hqb : q ∈ D.chart '' sphere (0 : E2) 1 :=
      D.closed_disk_diff_open_disk ▸ ⟨hqD, hq⟩
    change (1/2 : Real) < (inner Real v (g q)-D.center)/D.scale at hqheight
    rw [D.height_eq_on_boundary q hqb, sub_self, zero_div] at hqheight
    norm_num at hqheight
  have hpkeep := hcorekeep hp
  have hpbelow : inner Real v (g p) < b := by dsimp [b]; linarith
  have hheight (q : S1) (t : Real) (ht : t ∈ Ioo (-ε) ε) :
      inner Real v (g (T (q,t))) = D.center+D.scale*(1/2+t) := by
    rw [hformula q t ht]
    simpa only [heightCoordinates_apply] using inner_heightCoordinates D.unit_v
      (D.center+D.scale*(1/2+t), D.planeMap (J.symm (q : E2)))
  have hzero : (0 : Real) ∈ Ioo (-ε) ε := ⟨by linarith, hε⟩
  have hboundary : ∀ x ∈ sphere (0 : E2) 1, inner Real v (g (e x)) = b := by
    intro x hx
    obtain ⟨q, hq⟩ := hecenter.symm ▸ mem_image_of_mem e hx
    rw [← hq, hheight q 0 hzero]
    simp only [b, add_zero]
  have huniq : ∀ q ∈ e '' closedBall (0 : E2) 1,
      mfderiv (𝓡 2) 𝓘(Real, Real) (fun y => inner Real v (g y)) q = 0 → q = p := by
    intro q hq hc
    rw [heclosed, hdo] at hq
    apply hunique q
    · exact D.critical_mem_complement_of_truncated_cap hgEmb (by norm_num : (1/2 : Real) < 1) hq hc
    · exact hc
  have hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ (fun q => inner Real v (g q)) :=
    (innerSL Real v).contMDiff.comp hgEmb.contMDiff
  have hbounds := (height_bounds_on_disk_of_unique_critical hh e hes hpkeep hpbelow
    hboundary huniq).2.1
  have hnormbound : ∀ q ∈ e '' closedBall (0 : E2) 1, H q ≤ 1/2 := by
    intro q hq
    apply (div_le_iff₀ hs).mpr
    have := (hbounds q hq).2
    dsimp [b] at this
    linarith
  obtain ⟨F, hfix, hkeep, hgerm, hFrange⟩ := D.exists_normalization_of_bounded_retained_side
    hgEmb.contMDiff.continuous (a := 1/2) (by norm_num) (by norm_num)
      (fun q hq => hnormbound q (by rw [heclosed, hdo]; exact hq))
  let G : S2 → E3 := fun q => F (g q)
  have hG : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ G := by
    apply Poincare.Geometry.Manifold.isSmoothEmbedding_of_injective_mfderiv
      (F.contMDiff.comp hgEmb.contMDiff) (F.injective.comp hgEmb.isEmbedding.injective)
    intro q
    rw [mfderiv_comp q (F.contMDiff.mdifferentiable (by simp) _)
      (hgEmb.contMDiff.mdifferentiable (by simp) q)]
    exact (F.mfderivToContinuousLinearEquiv (by simp) (g q)).injective.comp
      (injective_mfderiv_sphere_embedding hgEmb q)
  have hGkeep (q : S2) (hq : q ∈ e '' closedBall (0 : E2) 1) : G q = g q :=
    hkeep q (by simpa only [heclosed, hdo, mem_compl_iff] using hq)
  have hGuniq : ∀ q ∈ e '' closedBall (0 : E2) 1,
      mfderiv (𝓡 2) 𝓘(Real, Real) (fun y => inner Real v (G y)) q = 0 → q = p := by
    intro q hq hc
    apply huniq q hq
    have heq : (fun y => inner Real v (G y)) =ᶠ[𝓝 q] (fun y => inner Real v (g y)) := by
      filter_upwards [hgerm q (by simpa only [heclosed, hdo, mem_compl_iff] using hq)] with y hy
      exact congrArg (inner Real v) hy
    exact heq.mfderiv_eq.symm.trans hc
  have hGform : ∀ x ∈ χ.source, inner Real v (G (χ x)) = inner Real v (G p) + ‖x‖ ^ 2 := by
    intro x hx
    rw [hGkeep _ (hcorekeep (hχtarget (χ.map_source hx))),
      hGkeep p hpkeep]
    exact hχform x hx
  let η := D.scale*ε/2
  have hη : 0 < η := by dsimp [η]; positivity
  have htimebound : |(0 : Real)| + |D.scale⁻¹| * η < ε := by
    rw [abs_zero, zero_add, abs_inv, abs_of_pos hs]
    have heq : D.scale⁻¹*η = ε/2 := by dsimp [η]; field_simp
    rw [heq]
    linarith
  obtain ⟨U, hUs, _, _, hUTraw⟩ := exists_reparametrized_sphere_tube T hT hTi hTs
    0 D.scale⁻¹ (inv_ne_zero D.scale_ne_zero) hη htimebound
  have hUT (q : S1) (t : Real) : U (q,t) = T (q,t/D.scale) := by
    simpa only [zero_add, div_eq_mul_inv, mul_comm] using hUTraw q t
  have htime {t : Real} (ht : t ∈ Ioo (-η) η) : t/D.scale ∈ Ioo (-ε) ε := by
    constructor
    · apply (lt_div_iff₀ hs).mpr
      dsimp [η] at ht
      nlinarith [ht.1, mul_pos hs hε]
    · apply (div_lt_iff₀ hs).mpr
      dsimp [η] at ht
      nlinarith [ht.2, mul_pos hs hε]
  let γ : S1 → Hemisphere.Plane v := fun q => D.planeMap (J.symm (q : E2))
  have hGcylinder (q : S1) (t : Real) (ht : t ∈ Ioo (-η) η) :
      G (U (q,t)) = (b+t) • v + (γ q : E3) := by
    change F (g (U (q,t))) = _
    rw [hUT, hfix]
    · rw [hformula q _ (htime ht)]
      congr 2
      dsimp [b]
      field_simp
      ring
    · rw [hheight q _ (htime ht), add_sub_cancel_left,
        mul_div_cancel_left₀ _ D.scale_ne_zero]
      have htdiv : t/D.scale < ε/2 := (div_lt_iff₀ hs).mpr
        (by simpa [η, mul_div_assoc, mul_comm] using ht.2)
      linarith
  have hUcenter : range (fun q : S1 => U (q,0)) = e '' sphere (0 : E2) 1 := by
    have heq : (fun q : S1 => U (q,0)) = fun q : S1 => T (q,0) := by
      funext q
      rw [hUT, zero_div]
    rw [heq, hecenter]
  have hUneg : ∀ q : S1, ∀ t ∈ Ioo (-η) 0, U (q,t) ∈ e '' ball 0 1 := by
    intro q t ht
    rw [hUT]
    exact hTneg q _ ⟨(htime ⟨ht.1, ht.2.trans hη⟩).1, div_neg_of_neg_of_pos ht.2 hs⟩
  have hB : D.planeMap '' sphere (0 : Hemisphere.Plane v) 1 = range γ := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨⟨J x, by simpa only [mem_sphere_zero_iff_norm, J.norm_map] using hx⟩, ?_⟩
      change D.planeMap (J.symm (J x)) = _
      rw [J.symm_apply_apply]
    · rintro ⟨q, rfl⟩
      exact ⟨J.symm (q : E2), by simp only [mem_sphere_zero_iff_norm, J.symm.norm_map,
        norm_eq_of_mem_sphere], rfl⟩
  have hGrange : range G = G '' (e '' closedBall (0 : E2) 1) ∪
      liftPlaneDiffeomorph D.unit_v b D.scale hs.ne' D.planeMap '' boundedCylinderNorthernCap v := by
    rw [heclosed, hdo]
    exact hFrange
  obtain ⟨A, hA⟩ := exists_ambient_filling_of_capped_minimum_disk hG D.unit_v e hes hpkeep
    (by rw [hGkeep p hpkeep]; exact hpbelow)
    (fun x hx => by rw [hGkeep _ (mem_image_of_mem e (sphere_subset_closedBall hx))]; exact hboundary x hx)
    hGuniq χ hχ0 hχp hχ hχi hGform hη U hUs γ hGcylinder hUcenter hUneg hs D.planeMap hB hGrange
  refine ⟨A.trans F.symm, ?_⟩
  change (F.symm ∘ A) '' sphere (0 : E3) 1 = _
  rw [image_comp, hA]
  change F.symm '' range (F ∘ g) = _
  rw [range_comp, image_image]
  simp only [F.symm_apply_apply, image_id']

namespace SphereMorseReduction

variable {f : S2 → E3} (M : SphereMorseReduction f)



theorem exists_filling_of_one_positive_cap {g : S2 → E3} (hg : g ∈ M.tree.leaves)
    (P : SphereSurgeryPath (M.v : E3) (fun p => M.D (f p)) g)
    (hP : P.Protects ((fun p => inner Real (M.v : E3) (M.D (f p))) ''
      {p | mfderiv (𝓡 2) 𝓘(Real, Real)
        (fun q => inner Real (M.v : E3) (M.D (f q))) p = 0}))
    {B : Set Real} (D : SphereSurgeryCoreCap (M.v : E3) g B)
    (hcore : P.core = (D.chart '' ball (0 : E2) 1)ᶜ) (hs : 0 < D.scale) :
    ∃ F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      F '' sphere (0 : E3) 1 = range g := by
  obtain ⟨p, hp, hpheight, _, hunique, χ, hχ0, hχp, hχ, hχi, hχtarget, hχform⟩ :=
    M.exists_minimum_chart_of_one_cap hg P hP D hcore hs
  apply exists_filling_of_positive_cap_complement (M.tree.embedding_of_mem_leaves hg) D hs
    p (by simpa only [hcore, mem_compl_iff] using interior_subset hp) hpheight
    (fun q hq hc => hunique q (by simpa only [hcore, mem_compl_iff] using hq) hc)
    χ hχ0 hχp hχ hχi _ hχform
  intro q hq
  simpa only [hcore] using interior_subset (hχtarget hq)

end SphereMorseReduction

end Poincare.Manifold.Schoenflies
