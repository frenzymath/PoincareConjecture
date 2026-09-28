import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.RegularBand.CapGraph.Belt
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.DomainIdentification



noncomputable section
set_option autoImplicit false

open Set Metric Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

open Poincare.Geometry.Euclidean

private abbrev E3 := EuclideanSpace Real (Fin 3)




theorem open_cylinder_subset_of_frontier
    {V : Type*} [NormedAddCommGroup V] [NormedSpace Real V] [Nontrivial V]
    {Ω : Set (Real × V)} (hΩ : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    {a b : Real} (hab : a < b)
    (hfront : ∀ z ∈ Ioo a b, ∀ x : V, (z, x) ∈ frontier Ω ↔ ‖x‖ = 1) :
    Ioo a b ×ˢ ball (0 : V) 1 ⊆ Ω := by
  obtain ⟨M, hM⟩ := hbounded.exists_norm_le
  have hout (z : Real) (hz : z ∈ Ioo a b) (x : V) (hx : 1 < ‖x‖) : (z, x) ∉ Ω := by
    intro hin
    let T : Real := |M| + 2
    have hT : 1 ≤ T := by dsimp [T]; linarith [abs_nonneg M]
    let c : Real → Real × V := fun t => (z, t • x)
    have hc : Continuous c := continuous_const.prodMk (continuous_id.smul continuous_const)
    have hconn : IsPreconnected (c '' Icc 1 T) := isPreconnected_Icc.image c hc.continuousOn
    have hdis : Disjoint (c '' Icc 1 T) (frontier Ω) := by
      apply disjoint_left.mpr
      rintro y ⟨t, ht, rfl⟩ hfy
      have hn := (hfront z hz (t • x)).mp hfy
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith [ht.1])] at hn
      nlinarith [norm_nonneg x, ht.1]
    have hsub : c '' Icc 1 T ⊆ Ω :=
      Poincare.Topology.subset_of_isPreconnected_of_disjoint_frontier hΩ hconn hdis
        ⟨(z, x), ⟨1, ⟨le_rfl, hT⟩, by simp [c]⟩, hin⟩
    have hb := hM (c T) (hsub (mem_image_of_mem c ⟨hT, le_rfl⟩))
    have hxbound : ‖T • x‖ ≤ M := (norm_snd_le (c T)).trans hb
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith)] at hxbound
    dsimp [T] at hxbound
    nlinarith [le_abs_self M, abs_nonneg M]
  obtain ⟨x, hx⟩ := (NormedSpace.sphere_nonempty (E := V) (x := 0)).mpr
    (show (0 : Real) ≤ 1 by norm_num)
  have hmid : (a + b) / 2 ∈ Ioo a b := ⟨by linarith, by linarith⟩
  have hpfront : ((a + b) / 2, x) ∈ frontier Ω :=
    (hfront _ hmid x).mpr (mem_sphere_zero_iff_norm.mp hx)
  obtain ⟨y, hyW, hyΩ⟩ := mem_closure_iff.mp (frontier_subset_closure hpfront)
    (Ioo a b ×ˢ (univ : Set V)) (isOpen_Ioo.prod isOpen_univ) ⟨hmid, mem_univ _⟩
  have hyball : y.2 ∈ ball (0 : V) 1 := by
    rw [mem_ball_zero_iff]
    rcases lt_trichotomy ‖y.2‖ 1 with hlt | heq | hgt
    · exact hlt
    · have hf := (hfront y.1 hyW.1 y.2).mpr heq
      rw [frontier, hΩ.interior_eq] at hf
      exact False.elim (hf.2 hyΩ)
    · exact False.elim (hout y.1 hyW.1 y.2 hgt hyΩ)
  apply Poincare.Topology.subset_of_isPreconnected_of_disjoint_frontier hΩ
    (isPreconnected_Ioo.prod (convex_ball (0 : V) 1).isPreconnected)
  · apply disjoint_left.mpr
    intro z hz hf
    exact (mem_ball_zero_iff.mp hz.2).ne ((hfront z.1 hz.1 z.2).mp hf)
  · exact ⟨y, ⟨hyW.1, hyball⟩, hyΩ⟩



theorem open_cylinder_subset_ball_image_of_boundary
    {V : Type*} [NormedAddCommGroup V] [NormedSpace Real V] [Nontrivial V]
    (H : (Real × V) ≃ₜ E3) (F : E3 ≃ₜ E3) {a b : Real} (hab : a < b)
    (hboundary : ∀ z ∈ Ioo a b, ∀ x : V,
      H (z, x) ∈ F '' sphere (0 : E3) 1 ↔ ‖x‖ = 1) :
    H '' (Ioo a b ×ˢ ball (0 : V) 1) ⊆ F '' ball (0 : E3) 1 := by
  let Ω := H.symm '' (F '' ball (0 : E3) 1)
  have hΩ : IsOpen Ω := H.symm.isOpenMap _ (F.isOpenMap _ isOpen_ball)
  have hb : Bornology.IsBounded Ω :=
    (((isCompact_closedBall (0 : E3) 1).image F.continuous).image H.symm.continuous).isBounded.subset
      (image_mono (image_mono ball_subset_closedBall))
  have hfront : frontier Ω = H.symm '' (F '' sphere (0 : E3) 1) := by
    rw [show Ω = _ from rfl, ← H.symm.image_frontier, ← F.image_frontier,
      frontier_ball _ one_ne_zero]
  have hsub := open_cylinder_subset_of_frontier hΩ hb hab (by
    intro z hz x
    rw [hfront]
    have heq : (z, x) ∈ H.symm '' (F '' sphere (0 : E3) 1) ↔
        H (z, x) ∈ F '' sphere (0 : E3) 1 := by
      constructor
      · rintro ⟨y, hy, heq⟩
        rw [← heq, H.apply_symm_apply]
        exact hy
      · intro hy
        exact ⟨H (z, x), hy, H.symm_apply_apply _⟩
    exact heq.trans (hboundary z hz x))
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨y, hy, heq⟩ := hsub hz
  rw [← heq, H.apply_symm_apply]
  exact hy




theorem mem_capped_cylinder_ball_of_upper_collar
    {v : E3} (hv : ‖v‖ = 1) {a b u w : Real} (hab : a ≤ b)
    (hu : 0 < u) (hw : 0 < w)
    (A : (Hemisphere.Plane v) ≃ₘ[Real] (Hemisphere.Plane v))
    (F : E3 ≃ₜ E3)
    (hF : F '' sphere (0 : E3) 1 =
      (liftPlaneDiffeomorph hv a (-u) (neg_ne_zero.mpr hu.ne') A '' boundedCylinderNorthernCap v) ∪
      ((fun z : Real × Hemisphere.Plane v => z.1 • v + (A z.2 : E3)) ''
        (Icc a b ×ˢ sphere (0 : Hemisphere.Plane v) 1)) ∪
      (liftPlaneDiffeomorph hv b w hw.ne' A '' boundedCylinderNorthernCap v))
    {y : E3} (hy : inner Real v y ∈ Ioo b (b + w))
    (hp : (Hemisphere.Plane v).orthogonalProjectionOnto y ∈ A '' ball 0 1) :
    y ∈ F '' ball (0 : E3) 1 := by
  let J : Hemisphere.Plane v ≃ₗᵢ[Real] EuclideanSpace Real (Fin 2) :=
    (OrthonormalBasis.fromOrthogonalSpanSingleton 2 (by intro hv0; simp [hv0] at hv)).repr
  let : Nontrivial (Hemisphere.Plane v) := Module.nontrivial_of_finrank_pos
    (R := Real) (by rw [J.toLinearEquiv.finrank_eq]; norm_num)
  let H : (Real × Hemisphere.Plane v) ≃ₜ E3 :=
    ((Homeomorph.refl Real).prodCongr A.toHomeomorph).trans (heightCoordinates hv).toHomeomorph
  have hH (z : Real) (x : Hemisphere.Plane v) : H (z, x) = z • v + (A x : E3) := rfl
  have hHheight (z : Real) (x : Hemisphere.Plane v) : inner Real v (H (z, x)) = z :=
    inner_heightCoordinates hv (z, A x)
  have hboundary (z : Real) (hz : z ∈ Ioo b (b + w)) (x : Hemisphere.Plane v) :
      H (z, x) ∈ F '' sphere (0 : E3) 1 ↔ ‖x‖ = 1 := by
    have ht : (z - b) / w ∈ Ico (0 : Real) 1 :=
      ⟨div_nonneg (by linarith [hz.1]) hw.le, (div_lt_one hw).mpr (by linarith [hz.2])⟩
    have hzt : b + w * ((z - b) / w) = z := by field_simp; ring
    have hslice := lifted_cap_slice_eq_circle hv b w hw.ne' A ht
    rw [hzt] at hslice
    have hupper : H (z, x) ∈ liftPlaneDiffeomorph hv b w hw.ne' A ''
        boundedCylinderNorthernCap v ↔ ‖x‖ = 1 := by
      constructor
      · intro hx
        have hmem : H (z, x) ∈ (fun q : Hemisphere.Plane v => z • v + (A q : E3)) ''
            sphere (0 : Hemisphere.Plane v) 1 := by
          rw [← hslice]
          exact ⟨hx, hHheight z x⟩
        obtain ⟨q, hq, heq⟩ := hmem
        change H (z, q) = H (z, x) at heq
        have hqx : q = x := congrArg Prod.snd (H.injective heq)
        simpa only [hqx] using mem_sphere_zero_iff_norm.mp hq
      · intro hx
        have hmem : H (z, x) ∈ (fun q : Hemisphere.Plane v => z • v + (A q : E3)) ''
            sphere (0 : Hemisphere.Plane v) 1 := ⟨x, mem_sphere_zero_iff_norm.mpr hx, rfl⟩
        rw [← hslice] at hmem
        exact hmem.1
    rw [hF]
    constructor
    · rintro ((hlower | hmiddle) | hcap)
      · obtain ⟨q, hq, heq⟩ := hlower
        have hh := congrArg (inner Real v) heq
        rw [inner_liftPlaneDiffeomorph, hHheight] at hh
        have hq0 := height_nonneg_of_mem_boundedCylinderNorthernCap hq
        nlinarith [hz.1]
      · obtain ⟨⟨t, q⟩, ⟨ht, _⟩, heq⟩ := hmiddle
        change H (t, q) = H (z, x) at heq
        have htq : t = z := congrArg Prod.fst (H.injective heq)
        exact False.elim (hz.1.not_ge (htq ▸ ht.2))
      · exact hupper.mp hcap
    · intro hx
      exact Or.inr (hupper.mpr hx)
  have hsub := open_cylinder_subset_ball_image_of_boundary H F
    (show b < b + w by linarith) hboundary
  obtain ⟨x, hx, heq⟩ := hp
  apply hsub
  refine ⟨(inner Real v y, x), ⟨hy, hx⟩, ?_⟩
  rw [hH, heq]
  exact (heightCoordinates hv).apply_symm_apply y

end Poincare.Manifold.Schoenflies.Saddle.Caps.Closing
