import PoincareConjecture.Proofs.M76.Mathlib.IntrinsicIsolatedStarSign
import PoincareConjecture.Proofs.M76.Mathlib.EmbeddedVertexIncidence











set_option autoImplicit false

open Set Filter
open scoped Topology

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]





theorem mem_closure_punctured_zero_section_of_both_signs
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hzero : (0 : E) ∈ K.vertices) (L : E →ₗ[ℝ] ℝ)
    (hconn : IsConnected (K.link 0).space)
    (hpos : (0 : E) ∈ closure (K.space ∩ {y | 0 < L y}))
    (hneg : (0 : E) ∈ closure (K.space ∩ {y | L y < 0})) :
    (0 : E) ∈ closure ((K.space ∩ {y | L y = 0}) \ {0}) := by
  by_contra hnot
  have hlocal : ∀ᶠ x in 𝓝 (0 : E), x ∈ K.space ∩ {y | L y = 0} → x = 0 := by
    filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hnot] with x hx hxS
    by_contra hxzero
    exact hx (subset_closure ⟨hxS, hxzero⟩)
  have hgraph := (K.link 0).connected_edgeGraph_of_isConnected (finite_link_faces hK 0)
    hconn
  obtain ⟨ε, hε, hmin | hmax⟩ :=
    K.exists_ball_strict_extremum_of_isolated_section hK hzero L hgraph hlocal
  · obtain ⟨x, hxball, hxS, hxL⟩ := mem_closure_iff.mp hneg
      (Metric.ball 0 ε) Metric.isOpen_ball (Metric.mem_ball_self hε)
    change L x < 0 at hxL
    have hxzero : x ≠ 0 := by
      intro heq
      simp only [heq, map_zero, lt_self_iff_false] at hxL
    exact lt_asymm (hmin x ⟨hxS, hxball⟩ hxzero) hxL
  · obtain ⟨x, hxball, hxS, hxL⟩ := mem_closure_iff.mp hpos
      (Metric.ball 0 ε) Metric.isOpen_ball (Metric.mem_ball_self hε)
    change 0 < L x at hxL
    have hxzero : x ≠ 0 := by
      intro heq
      simp only [heq, map_zero, lt_self_iff_false] at hxL
    exact lt_asymm hxL (hmax x ⟨hxS, hxball⟩ hxzero)






theorem mem_closure_punctured_level_of_both_signs
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {p : E} (hp : p ∈ K.vertices) (A : E →ᵃ[ℝ] ℝ)
    (hconn : IsConnected (K.link p).space)
    (hpos : p ∈ closure (K.space ∩ {y | A p < A y}))
    (hneg : p ∈ closure (K.space ∩ {y | A y < A p})) :
    p ∈ closure ((K.space ∩ {y | A y = A p}) \ {p}) := by
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
  have hJlink : (J.link 0).space = e '' (K.link p).space := by
    have h := hf.embeddedImage_link_space e.injective.injOn hp
    change (J.link (e p)).space = e '' (K.link p).space at h
    simpa only [hep] using h
  have hconnJ : IsConnected (J.link 0).space := by
    rw [hJlink]
    exact hconn.image e e.continuous.continuousOn
  have himage (U : Set ℝ) :
      e '' (K.space ∩ (fun x => A x - A p) ⁻¹' U) =
        J.space ∩ A.linear ⁻¹' U := by
    rw [hJspace]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx.1, rfl⟩, by simpa only [mem_preimage, hheight] using hx.2⟩
    · rintro ⟨⟨x, hx, rfl⟩, hy⟩
      exact ⟨x, ⟨hx, by simpa only [mem_preimage, hheight] using hy⟩, rfl⟩
  have hposJ : (0 : E) ∈ closure (J.space ∩ {y | 0 < A.linear y}) := by
    change (0 : E) ∈ closure (J.space ∩ A.linear ⁻¹' Ioi 0)
    rw [← himage (Ioi 0)]
    apply image_closure_subset_closure_image e.continuous
    refine ⟨p, ?_, hep⟩
    change p ∈ closure (K.space ∩ {x | 0 < A x - A p})
    simpa only [sub_pos] using hpos
  have hnegJ : (0 : E) ∈ closure (J.space ∩ {y | A.linear y < 0}) := by
    change (0 : E) ∈ closure (J.space ∩ A.linear ⁻¹' Iio 0)
    rw [← himage (Iio 0)]
    apply image_closure_subset_closure_image e.continuous
    refine ⟨p, ?_, hep⟩
    change p ∈ closure (K.space ∩ {x | A x - A p < 0})
    simpa only [sub_neg] using hneg
  have hzeroImage : e '' (K.space ∩ {y | A y = A p}) =
      J.space ∩ {y | A.linear y = 0} := by
    have h := himage {0}
    change e '' (K.space ∩ {x | A x - A p = 0}) = J.space ∩ {x | A.linear x = 0} at h
    simpa only [sub_eq_zero] using h
  have hpunct : e '' ((K.space ∩ {y | A y = A p}) \ {p}) =
      (J.space ∩ {y | A.linear y = 0}) \ {0} := by
    rw [image_sdiff e.injective, hzeroImage, image_singleton, hep]
  have haccJ := J.mem_closure_punctured_zero_section_of_both_signs hJ hpJ A.linear
    hconnJ hposJ hnegJ
  have haccImage : e p ∈ e '' closure ((K.space ∩ {y | A y = A p}) \ {p}) := by
    change e p ∈ e.toHomeomorph '' closure ((K.space ∩ {y | A y = A p}) \ {p})
    rw [e.toHomeomorph.image_closure]
    change e p ∈ closure (e '' ((K.space ∩ {y | A y = A p}) \ {p}))
    rw [hpunct, hep]
    exact haccJ
  obtain ⟨x, hx, hxp⟩ := haccImage
  exact e.injective hxp ▸ hx

end Geometry.SimplicialComplex
