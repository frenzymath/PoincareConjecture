import PoincareConjecture.Proofs.M76.Mathlib.ZeroChargeSignedLinks
import PoincareConjecture.Proofs.M76.Mathlib.AffineCurvePresentation
import PoincareConjecture.Proofs.M76.Mathlib.EmbeddedVertexIncidence

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

theorem zero_charge_vertex_link_sign_data
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hcofaces : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    {p : E} (hp : p ∈ K.vertices) (hconn : IsConnected (K.link p).space)
    (A : E →ᵃ[ℝ] ℝ)
    (hpres : HasAlexanderCurvePresentation (K.space ∩ {x | A x = A p}) 0)
    (hsigns : p ∈ closure ((K.space ∩ {x | A x = A p}) \ {p}) →
      p ∈ closure (K.space ∩ {x | A x < A p}) ∧
        p ∈ closure (K.space ∩ {x | A p < A x})) :
    IsPreconnected ((K.link p).space ∩ {x | A x < A p}) ∧
      IsPreconnected ((K.link p).space ∩ {x | A p < A x}) ∧
      ∀ x ∈ (K.link p).space, A x = A p →
        x ∈ closure ((K.link p).space ∩ {y | A y < A p}) ∧
          x ∈ closure ((K.link p).space ∩ {y | A p < A y}) := by
  classical
  let e : E ≃ᴬ[ℝ] E := ContinuousAffineEquiv.constVAdd ℝ E (-p)
  have hep : e p = 0 := by change -p + p = 0; exact neg_add_cancel p
  have hheight (x : E) : A.linear (e x) = A x - A p := by
    change A.linear (-p + x) = A x - A p
    simpa only [vsub_eq_sub, sub_eq_add_neg, add_comm] using A.linearMap_vsub x p
  let hf := K.affineOnFaces_affine e.toContinuousAffineMap
  let J := hf.embeddedImage e.injective.injOn
  have hJ : J.faces.Finite := hf.embeddedImage_finite e.injective.injOn hK
  have hJspace : J.space = e '' K.space := hf.embeddedImage_space e.injective.injOn
  have hpJ : (0 : E) ∈ J.vertices := by
    rw [hf.embeddedImage_vertices e.injective.injOn]
    exact ⟨p, hp, hep⟩
  have hJpure : ∀ s ∈ J.faces, ∃ t ∈ J.faces, t.card = 3 ∧ s ⊆ t := by
    have h := hf.embeddedImage_pure e.injective.injOn (fun s hs => by
      obtain ⟨t, ht, htc, hst⟩ := hpure s hs
      exact ⟨t, ht, hst, htc⟩)
    intro s hs
    obtain ⟨t, ht, hst, htc⟩ := h s hs
    exact ⟨t, ht, htc, hst⟩
  have hJcofaces : ∀ s ∈ J.faces, s.card = 2 →
      {t : Finset E | t ∈ J.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2 :=
    hf.embeddedImage_coface_count e.injective.injOn hcofaces
  have hJlink : (J.link 0).space = e '' (K.link p).space := by
    have h := hf.embeddedImage_link_space e.injective.injOn hp
    change (J.link (e p)).space = e '' (K.link p).space at h
    simpa only [hep] using h
  have hJconn : IsConnected (J.link 0).space := by
    rw [hJlink]
    exact hconn.image e e.continuous.continuousOn
  have hJgraph := (J.link 0).connected_edgeGraph_of_isConnected
    (finite_link_faces hJ 0) hJconn
  have himage (s : Set E) (V : Set ℝ) :
      e '' (s ∩ (fun x => A x - A p) ⁻¹' V) = (e '' s) ∩ A.linear ⁻¹' V := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx.1, rfl⟩, by simpa only [mem_preimage, hheight] using hx.2⟩
    · rintro ⟨⟨x, hx, rfl⟩, hy⟩
      exact ⟨x, ⟨hx, by simpa only [mem_preimage, hheight] using hy⟩, rfl⟩
  have hzeroImage : e '' (K.space ∩ {x | A x = A p}) =
      J.space ∩ {x | A.linear x = 0} := by
    have h := himage K.space {0}
    rw [← hJspace] at h
    change e '' (K.space ∩ {x | A x - A p = 0}) = J.space ∩ {x | A.linear x = 0} at h
    simpa only [sub_eq_zero] using h
  have hpunct : e '' ((K.space ∩ {x | A x = A p}) \ {p}) =
      (J.space ∩ {x | A.linear x = 0}) \ {0} := by
    rw [image_sdiff e.injective, hzeroImage, image_singleton, hep]
  have hJpres : HasAlexanderCurvePresentation (J.space ∩ {x | A.linear x = 0}) 0 := by
    rw [← hzeroImage]
    exact hpres.affine_image e.toContinuousAffineMap.toAffineMap e.injective
  have hJsigns : (0 : E) ∈ closure ((J.space ∩ {x | A.linear x = 0}) \ {0}) →
      (0 : E) ∈ closure (J.space ∩ {x | A.linear x < 0}) ∧
        (0 : E) ∈ closure (J.space ∩ {x | 0 < A.linear x}) := by
    intro haccJ
    have haccImage : e p ∈ e '' closure ((K.space ∩ {x | A x = A p}) \ {p}) := by
      change e p ∈ e.toHomeomorph '' closure ((K.space ∩ {x | A x = A p}) \ {p})
      rw [e.toHomeomorph.image_closure]
      change e p ∈ closure (e '' ((K.space ∩ {x | A x = A p}) \ {p}))
      rw [hpunct, hep]
      exact haccJ
    obtain ⟨x, hx, hxp⟩ := haccImage
    obtain ⟨hneg, hpos⟩ := hsigns (e.injective hxp ▸ hx)
    constructor
    · change (0 : E) ∈ closure (J.space ∩ A.linear ⁻¹' Iio 0)
      rw [hJspace, ← himage K.space (Iio 0)]
      apply image_closure_subset_closure_image e.continuous
      refine ⟨p, ?_, hep⟩
      change p ∈ closure (K.space ∩ {x | A x - A p < 0})
      simpa only [sub_neg] using hneg
    · change (0 : E) ∈ closure (J.space ∩ A.linear ⁻¹' Ioi 0)
      rw [hJspace, ← himage K.space (Ioi 0)]
      apply image_closure_subset_closure_image e.continuous
      refine ⟨p, ?_, hep⟩
      change p ∈ closure (K.space ∩ {x | 0 < A x - A p})
      simpa only [sub_pos] using hpos
  obtain ⟨hn, hpos, hz⟩ := J.zero_charge_link_sign_data hJ hJpure hJcofaces hpJ hJgraph
    A.linear hJpres hJsigns
  have hnimage : e '' ((K.link p).space ∩ {x | A x < A p}) =
      (J.link 0).space ∩ {x | A.linear x < 0} := by
    have h := himage (K.link p).space (Iio 0)
    rw [← hJlink] at h
    change e '' ((K.link p).space ∩ {x | A x - A p < 0}) =
      (J.link 0).space ∩ {x | A.linear x < 0} at h
    simpa only [sub_neg] using h
  have hpimage : e '' ((K.link p).space ∩ {x | A p < A x}) =
      (J.link 0).space ∩ {x | 0 < A.linear x} := by
    have h := himage (K.link p).space (Ioi 0)
    rw [← hJlink] at h
    change e '' ((K.link p).space ∩ {x | 0 < A x - A p}) =
      (J.link 0).space ∩ {x | 0 < A.linear x} at h
    simpa only [sub_pos] using h
  have hback (T : Set E) : e.symm '' (e '' T) = T := by
    rw [image_image]
    exact (image_congr (fun x _ => e.symm_apply_apply x)).trans (image_id T)
  have hnback := hn.image e.symm e.symm.continuous.continuousOn
  have hpback := hpos.image e.symm e.symm.continuous.continuousOn
  rw [← hnimage, hback] at hnback
  rw [← hpimage, hback] at hpback
  refine ⟨hnback, hpback, ?_⟩
  intro x hx hxA
  have hex : e x ∈ (J.link 0).space := hJlink.symm.subset ⟨x, hx, rfl⟩
  have hexA : A.linear (e x) = 0 := by rw [hheight, hxA, sub_self]
  obtain ⟨hxneg, hxpos⟩ := hz (e x) hex hexA
  constructor
  · have h : x ∈ closure (e.symm '' ((J.link 0).space ∩ {y | A.linear y < 0})) :=
      image_closure_subset_closure_image e.symm.continuous
        ⟨e x, hxneg, e.symm_apply_apply x⟩
    rwa [← hnimage, hback] at h
  · have h : x ∈ closure (e.symm '' ((J.link 0).space ∩ {y | 0 < A.linear y})) :=
      image_closure_subset_closure_image e.symm.continuous
        ⟨e x, hxpos, e.symm_apply_apply x⟩
    rwa [← hpimage, hback] at h

end Geometry.SimplicialComplex
