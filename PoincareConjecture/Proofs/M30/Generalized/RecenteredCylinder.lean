import PoincareConjecture.Proofs.M30.Generalized.CylinderSpatialHomeomorph
import PoincareConjecture.Proofs.M12.GeneralizedCylinderRestriction
import Mathlib.Topology.Algebra.Group.Basic

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M30.Cylinder

private noncomputable def recenterSliceDiffeomorph (F : GeneralizedRicciFlowData.{u})
    {s t : ℝ} (h : s = t) :
    (F.slice s).carrier ≃ₘ^∞⟮𝓡 3, 𝓡 3⟯ (F.slice t).carrier := by
  subst t
  exact Diffeomorph.refl (𝓡 3) (F.slice s).carrier ∞

private theorem recenterSliceDiffeomorph_point (F : GeneralizedRicciFlowData.{u})
    {s t : ℝ} (h : s = t) (x : (F.slice s).carrier) :
    (⟨t, recenterSliceDiffeomorph F h x⟩ : F.point) = (⟨s, x⟩ : F.point) := by
  subst t
  rfl

private theorem recenterClock_eq (a q t0 s : ℝ) :
    a + (t0 + s) / q = (a + t0 / q) + s / q := by
  simp only [add_div, add_assoc]

variable {F : GeneralizedRicciFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
  {a q : ℝ} {J : SpacetimeInterval} {U : TopologicalSpace.Opens C.carrier}
  (e : GeneralizedFlowCylinder F C a q J.domain U)
  (t0 : J.domain)
  (V : TopologicalSpace.Opens (F.slice (a + t0.val / q)).carrier)
  (hV : (V : Set (F.slice (a + t0.val / q)).carrier) ⊆
    e.forward t0.val t0.property '' (U : Set C.carrier))
  {I : Set ℝ}
  (hI : I ⊆ (fun s : ℝ => t0.val + s) ⁻¹' J.domain)

noncomputable def recenter :
    GeneralizedFlowCylinder F (F.slice (a + t0.val / q))
      (a + t0.val / q) q I V := by
  let H0 := spatialHomeomorph e t0
  let D (s : ℝ) := recenterSliceDiffeomorph F (recenterClock_eq a q t0.val s)
  have hinto (y : (F.slice (a + t0.val / q)).carrier) (hy : y ∈ H0.target) :
      e.inverse t0.val t0.property y ∈ U := H0.map_target hy
  let R : GeneralizedFlowCylinder F (F.slice (a + t0.val / q))
      (a + t0.val / q) q I H0.target := {
    scale_pos := e.scale_pos
    forward := fun s hs => D s ∘ e.forward (t0.val + s) (hI hs) ∘
      e.inverse t0.val t0.property
    inverse := fun s hs => e.forward t0.val t0.property ∘
      e.inverse (t0.val + s) (hI hs) ∘ (D s).symm
    forward_smooth := fun s hs => (D s).contMDiff.comp_contMDiffOn
      ((e.forward_smooth (t0.val + s) (hI hs)).comp
        (e.inverse_smooth t0.val t0.property) hinto)
    inverse_smooth := by
      intro s hs
      apply (e.forward_smooth t0.val t0.property).comp
      · apply (e.inverse_smooth (t0.val + s) (hI hs)).comp
          (D s).symm.contMDiff.contMDiffOn
        rintro y ⟨x, hx, rfl⟩
        change (D s).symm (D s (e.forward (t0.val + s) (hI hs)
          (e.inverse t0.val t0.property x))) ∈
            e.forward (t0.val + s) (hI hs) '' (U : Set C.carrier)
        rw [Diffeomorph.symm_apply_apply]
        exact mem_image_of_mem (e.forward (t0.val + s) (hI hs)) (hinto x hx)
      · rintro y ⟨x, hx, rfl⟩
        change e.inverse (t0.val + s) (hI hs)
          ((D s).symm (D s (e.forward (t0.val + s) (hI hs)
            (e.inverse t0.val t0.property x)))) ∈ U
        rw [Diffeomorph.symm_apply_apply,
          e.left_inverse (t0.val + s) (hI hs) (hinto x hx)]
        exact hinto x hx
    left_inverse := by
      intro s hs x hx
      simpa only [Function.comp_apply, Diffeomorph.symm_apply_apply,
        e.left_inverse (t0.val + s) (hI hs) (hinto x hx)] using
          e.right_inverse t0.val t0.property hx
    right_inverse := by
      intro s hs y hy
      obtain ⟨x, hx, rfl⟩ := hy
      simp only [Function.comp_apply, Diffeomorph.symm_apply_apply,
        e.left_inverse (t0.val + s) (hI hs) (hinto x hx),
        e.right_inverse t0.val t0.property hx]
    embedding := by
      have hclock : Topology.IsEmbedding (fun s : I => t0.val + s.val) :=
        (Homeomorph.addLeft t0.val).isEmbedding.comp
          (Topology.IsEmbedding.subtypeVal :
            Topology.IsEmbedding (Subtype.val : I → ℝ))
      have hspace : Topology.IsEmbedding
          (fun y : H0.target =>
            (⟨e.inverse t0.val t0.property y.val, hinto y.val y.property⟩ : U)) :=
        H0.symm.toHomeomorphSourceTarget.isEmbedding
      have h := e.embedding.comp
        ((hclock.codRestrict J.domain (fun s => hI s.property)).prodMap hspace)
      convert h using 1
      funext p
      exact recenterSliceDiffeomorph_point F (recenterClock_eq a q t0.val p.1.val) _
    vertical_compatibility := by
      intro s hs x hx
      obtain ⟨b, y, δ, hδ, hbox⟩ := e.vertical_compatibility
        (t0.val + s) (hI hs) (e.inverse t0.val t0.property x) (hinto x hx)
      refine ⟨b, y, δ, hδ, ?_⟩
      intro s' hs' hnear
      have hnear' : |(t0.val + s') - (t0.val + s)| < δ := by
        rw [show (t0.val + s') - (t0.val + s) = s' - s by ring]
        exact hnear
      obtain ⟨hb, hforward⟩ := hbox (t0.val + s') (hI hs') hnear'
      have ht := recenterClock_eq a q t0.val s'
      have hb' : (a + t0.val / q) + s' / q ∈ (F.box b).interval := ht ▸ hb
      refine ⟨hb', ?_⟩
      have hpoints :
          (⟨(a + t0.val / q) + s' / q,
            D s' (e.forward (t0.val + s') (hI hs')
              (e.inverse t0.val t0.property x))⟩ : F.point) =
          (⟨(a + t0.val / q) + s' / q,
            (F.box b).forward _ hb' y⟩ : F.point) := by
        calc
          _ = (⟨a + (t0.val + s') / q,
            e.forward (t0.val + s') (hI hs')
              (e.inverse t0.val t0.property x)⟩ : F.point) :=
                recenterSliceDiffeomorph_point F ht _
          _ = (⟨a + (t0.val + s') / q, (F.box b).forward _ hb y⟩ : F.point) :=
            congrArg (Sigma.mk _) hforward
          _ = _ := congrArg
            (fun t : (F.box b).interval =>
              (⟨t.val, (F.box b).forward t.val t.property y⟩ : F.point))
            (show (⟨a + (t0.val + s') / q, hb⟩ : (F.box b).interval) =
              ⟨(a + t0.val / q) + s' / q, hb'⟩ from Subtype.ext ht)
      exact eq_of_heq (Sigma.mk.inj_iff.mp hpoints).2 }
  exact R.restrict Subset.rfl hV

@[simp] theorem recenter_pointMap (s : ℝ) (hs : s ∈ I)
    (y : (F.slice (a + t0.val / q)).carrier) :
    (recenter e t0 V hV hI).pointMap s hs y =
      e.pointMap (t0.val + s) (hI hs)
        (e.inverse t0.val t0.property y) :=
  recenterSliceDiffeomorph_point F (recenterClock_eq a q t0.val s) _

theorem recenter_zero_identity (hzero : (0 : ℝ) ∈ I)
    (y : (F.slice (a + t0.val / q)).carrier) (hy : y ∈ V) :
    (recenter e t0 V hV hI).pointMap 0 hzero y =
      (⟨a + t0.val / q, y⟩ : F.point) := by
  rw [recenter_pointMap]
  calc
    _ = e.pointMap t0.val t0.property (e.inverse t0.val t0.property y) :=
      congrArg (fun s : J.domain =>
        e.pointMap s.val s.property (e.inverse t0.val t0.property y))
        (show (⟨t0.val + 0, hI hzero⟩ : J.domain) = t0 from
          Subtype.ext (add_zero t0.val))
    _ = _ := congrArg (fun x : (F.slice (a + t0.val / q)).carrier =>
      (⟨a + t0.val / q, x⟩ : F.point))
      (e.right_inverse t0.val t0.property (hV hy))

end PoincareConjecture.M30.Cylinder
