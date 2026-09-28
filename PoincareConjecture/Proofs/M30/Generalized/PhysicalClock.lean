import PoincareConjecture.Definitions.Ch11.BlowupLimits
import PoincareConjecture.Definitions.M13TimeRescaling











set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M30.Cylinder

private noncomputable def sliceDiffeomorph (F : GeneralizedRicciFlowData.{u})
    {s t : ℝ} (h : s = t) :
    (F.slice s).carrier ≃ₘ^∞⟮𝓡 3, 𝓡 3⟯ (F.slice t).carrier := by
  subst t
  exact Diffeomorph.refl (𝓡 3) (F.slice s).carrier ∞

private theorem sliceDiffeomorph_point (F : GeneralizedRicciFlowData.{u})
    {s t : ℝ} (h : s = t) (x : (F.slice s).carrier) :
    (⟨t, sliceDiffeomorph F h x⟩ : F.point) = (⟨s, x⟩ : F.point) := by
  subst t
  rfl

private theorem physicalClock_eq (origin scale : ℝ) (hscale : 0 < scale) (s : ℝ) :
    origin + (scale * s) / scale = origin + s / 1 := by
  rw [mul_div_cancel_left₀ _ hscale.ne', div_one]

variable {F : GeneralizedRicciFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
  {origin scale : ℝ} {I J : Set ℝ} {U : Set C.carrier}




noncomputable def physicalTime
    (e : GeneralizedFlowCylinder F C origin scale I U)
    (hJ : J ⊆ (fun s : ℝ => scale * s) ⁻¹' I) :
    GeneralizedFlowCylinder F C origin 1 J U where
  scale_pos := zero_lt_one
  forward s hs := sliceDiffeomorph F (physicalClock_eq origin scale e.scale_pos s) ∘
    e.forward (scale * s) (hJ hs)
  inverse s hs := e.inverse (scale * s) (hJ hs) ∘
    (sliceDiffeomorph F (physicalClock_eq origin scale e.scale_pos s)).symm
  forward_smooth s hs :=
    (sliceDiffeomorph F (physicalClock_eq origin scale e.scale_pos s)).contMDiff.comp_contMDiffOn
      (e.forward_smooth (scale * s) (hJ hs))
  inverse_smooth s hs := by
    apply (e.inverse_smooth (scale * s) (hJ hs)).comp
      (sliceDiffeomorph F (physicalClock_eq origin scale e.scale_pos s)).symm.contMDiff.contMDiffOn
    rintro y ⟨x, hx, rfl⟩
    simpa only [mem_preimage, Function.comp_apply, Diffeomorph.symm_apply_apply] using
      (mem_image_of_mem (e.forward (scale * s) (hJ hs)) hx)
  left_inverse s hs x hx := by
    simpa only [Function.comp_apply, Diffeomorph.symm_apply_apply] using
      e.left_inverse (scale * s) (hJ hs) hx
  right_inverse s hs y hy := by
    obtain ⟨x, hx, rfl⟩ := hy
    simp only [Function.comp_apply, Diffeomorph.symm_apply_apply,
      e.left_inverse (scale * s) (hJ hs) hx]
  embedding := by
    have hclock : Topology.IsEmbedding (fun s : J => scale * s.val) := by
      convert (parabolicTimeOrderIso scale e.scale_pos 0).toHomeomorph.isEmbedding.comp
        (Topology.IsEmbedding.subtypeVal :
          Topology.IsEmbedding (Subtype.val : J → ℝ)) using 1
      funext s
      change scale * s.val = scale * (s.val - 0)
      rw [sub_zero]
    have h := e.embedding.comp
      ((hclock.codRestrict I (fun s => hJ s.property)).prodMap Topology.IsEmbedding.id)
    convert h using 1
    funext p
    exact sliceDiffeomorph_point F (physicalClock_eq origin scale e.scale_pos p.1.val) _
  vertical_compatibility s hs x hx := by
    obtain ⟨b, y, δ, hδ, hbox⟩ := e.vertical_compatibility (scale * s) (hJ hs) x hx
    refine ⟨b, y, δ / scale, div_pos hδ e.scale_pos, ?_⟩
    intro s' hs' hnear
    have hnear' : |scale * s' - scale * s| < δ := by
      rw [← mul_sub, abs_mul, abs_of_pos e.scale_pos]
      simpa only [mul_comm] using (lt_div_iff₀ e.scale_pos).mp hnear
    obtain ⟨hb, hforward⟩ := hbox (scale * s') (hJ hs') hnear'
    have ht := physicalClock_eq origin scale e.scale_pos s'
    have hb' : origin + s' / 1 ∈ (F.box b).interval := ht ▸ hb
    refine ⟨hb', ?_⟩
    have hpoints :
        (⟨origin + s' / 1,
          sliceDiffeomorph F ht (e.forward (scale * s') (hJ hs') x)⟩ : F.point) =
        (⟨origin + s' / 1, (F.box b).forward _ hb' y⟩ : F.point) := by
      calc
        _ = (⟨origin + (scale * s') / scale,
          e.forward (scale * s') (hJ hs') x⟩ : F.point) :=
            sliceDiffeomorph_point F ht _
        _ = (⟨origin + (scale * s') / scale, (F.box b).forward _ hb y⟩ : F.point) :=
          congrArg (Sigma.mk _) hforward
        _ = _ := congrArg
          (fun t : (F.box b).interval =>
            (⟨t.val, (F.box b).forward t.val t.property y⟩ : F.point))
          (show (⟨origin + (scale * s') / scale, hb⟩ : (F.box b).interval) =
            ⟨origin + s' / 1, hb'⟩ from Subtype.ext ht)
    exact eq_of_heq (Sigma.mk.inj_iff.mp hpoints).2




@[simp] theorem physicalTime_pointMap
    (e : GeneralizedFlowCylinder F C origin scale I U)
    (hJ : J ⊆ (fun s : ℝ => scale * s) ⁻¹' I)
    (s : ℝ) (hs : s ∈ J) (x : C.carrier) :
    (physicalTime e hJ).pointMap s hs x = e.pointMap (scale * s) (hJ hs) x :=
  sliceDiffeomorph_point F (physicalClock_eq origin scale e.scale_pos s) _

end PoincareConjecture.M30.Cylinder
