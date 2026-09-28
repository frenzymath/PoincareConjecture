import PoincareConjecture.Proofs.M76.Mathlib.ConvexAffineHeightSigns
import PoincareConjecture.Proofs.M76.Mathlib.AffineHyperplaneCoordinates
import PoincareConjecture.Proofs.M76.Mathlib.AffineIntrinsicFrontier
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Topology.Connected.Basic

set_option autoImplicit false

open Set
open Metric (ball mem_ball_self isOpen_ball)

namespace OpenPartialHomeomorph

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

private theorem mem_closure_negative_of_plane_germ
    (f : OpenPartialHomeomorph E F) (A : E →ᵃ[ℝ] ℝ) (B : F →ᵃ[ℝ] ℝ)
    (hB : B.linear ≠ 0) {p : E} (hp : p ∈ f.source) (hpB : B (f p) = 0)
    {U S : Set E} (hU : IsOpen U) (hpU : p ∈ U)
    (hzero : ∀ x ∈ U ∩ f.source, A x = 0 ↔ B (f x) = 0)
    (hn : p ∈ closure (S ∩ {x | A x < 0}))
    (hs : p ∈ closure (S ∩ {x | 0 < A x})) :
    f p ∈ closure ((f '' (S ∩ f.source)) ∩ {x | B x < 0}) := by
  apply mem_closure_iff.mpr
  intro V hV hpV
  have hO : IsOpen (U ∩ (f.source ∩ f ⁻¹' V)) :=
    hU.inter (f.isOpen_inter_preimage hV)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hO p ⟨hpU, hp, hpV⟩
  have hballsource : ball p r ⊆ f.source := fun x hx => (hball hx).2.1
  have himage : IsOpen (f '' ball p r) :=
    f.isOpen_image_of_subset_source isOpen_ball hballsource
  obtain ⟨q, hq⟩ := (B.linear_surjective_iff.mp (LinearMap.surjective hB)) (-1)
  have htarget : f p ∈ closure {x | B x < 0} := by
    have h := (convex_univ : Convex ℝ (univ : Set F)).mem_closure_lower_affine_height
      B (mem_univ (f p)) (mem_univ q) (by rw [hq, hpB]; norm_num)
    simpa only [hpB, univ_inter] using h
  obtain ⟨z, ⟨v, hv, rfl⟩, hz⟩ := mem_closure_iff.mp htarget (f '' ball p r)
    himage (mem_image_of_mem f (mem_ball_self hr))
  have hnonzero {x : E} (hx : x ∈ ball p r) (hxA : A x ≠ 0) : B (f x) ≠ 0 :=
    fun h => hxA ((hzero x ⟨(hball hx).1, hballsource hx⟩).mpr h)
  have hcont : ContinuousOn (B ∘ f) (ball p r) :=
    B.continuous_of_finiteDimensional.comp_continuousOn (f.continuousOn.mono hballsource)
  have hvne : A v ≠ 0 := fun h => hz.ne ((hzero v ⟨(hball hv).1, hballsource hv⟩).mp h)
  rcases lt_or_gt_of_ne hvne with hvn | hvp
  · obtain ⟨y, hyball, hyS, hyA⟩ := mem_closure_iff.mp hn (ball p r)
      isOpen_ball (mem_ball_self hr)
    have hconv : Convex ℝ (ball p r ∩ {x | A x < 0}) :=
      (convex_ball p r).inter ((convex_Iio (0 : ℝ)).affine_preimage A)
    have hyB : B (f y) < 0 := hconv.isPreconnected.gt_of_ne
      (hcont.mono inter_subset_left)
      (fun x hx => hnonzero hx.1 hx.2.ne) ⟨v, ⟨hv, hvn⟩, hz⟩ ⟨hyball, hyA⟩
    exact ⟨f y, (hball hyball).2.2, ⟨y, ⟨hyS, hballsource hyball⟩, rfl⟩, hyB⟩
  · obtain ⟨y, hyball, hyS, hyA⟩ := mem_closure_iff.mp hs (ball p r)
      isOpen_ball (mem_ball_self hr)
    have hconv : Convex ℝ (ball p r ∩ {x | 0 < A x}) :=
      (convex_ball p r).inter ((convex_Ioi (0 : ℝ)).affine_preimage A)
    have hyB : B (f y) < 0 := hconv.isPreconnected.gt_of_ne
      (hcont.mono inter_subset_left)
      (fun x hx => hnonzero hx.1 hx.2.ne') ⟨v, ⟨hv, hvp⟩, hz⟩ ⟨hyball, hyA⟩
    exact ⟨f y, (hball hyball).2.2, ⟨y, ⟨hyS, hballsource hyball⟩, rfl⟩, hyB⟩

theorem mem_closure_both_signs_of_plane_germ
    (f : OpenPartialHomeomorph E F) (A : E →ᵃ[ℝ] ℝ) (B : F →ᵃ[ℝ] ℝ)
    (hB : B.linear ≠ 0) {p : E} (hp : p ∈ f.source) (hpB : B (f p) = 0)
    {U S : Set E} (hU : IsOpen U) (hpU : p ∈ U)
    (hzero : ∀ x ∈ U ∩ f.source, A x = 0 ↔ B (f x) = 0)
    (hn : p ∈ closure (S ∩ {x | A x < 0}))
    (hs : p ∈ closure (S ∩ {x | 0 < A x})) :
    f p ∈ closure ((f '' (S ∩ f.source)) ∩ {x | B x < 0}) ∧
      f p ∈ closure ((f '' (S ∩ f.source)) ∩ {x | 0 < B x}) := by
  refine ⟨f.mem_closure_negative_of_plane_germ A B hB hp hpB hU hpU hzero hn hs, ?_⟩
  have hnB : (-B).linear ≠ 0 := by simpa only [AffineMap.neg_linear, neg_ne_zero] using hB
  have hpneg : (-B) (f p) = 0 := by simp only [AffineMap.coe_neg, Pi.neg_apply, hpB, neg_zero]
  have hzeroneg : ∀ x ∈ U ∩ f.source, A x = 0 ↔ (-B) (f x) = 0 := by
    intro x hx
    simpa only [AffineMap.coe_neg, Pi.neg_apply, neg_eq_zero] using hzero x hx
  simpa only [AffineMap.coe_neg, Pi.neg_apply, neg_lt_zero] using
    f.mem_closure_negative_of_plane_germ A (-B) hnB hp hpneg hU hpU hzeroneg hn hs

end OpenPartialHomeomorph

namespace AffineMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem mem_closure_both_signs_on_zero_plane
    (A C : E →ᵃ[ℝ] ℝ) (hA : A.linear ≠ 0)
    {p u : E} (hpA : A p = 0) (hpC : C p = 0)
    (huA : A u = 0) (huC : C u ≠ 0) :
    p ∈ closure ({x | C x = 0} ∩ {x | A x < 0}) ∧
      p ∈ closure ({x | C x = 0} ∩ {x | 0 < A x}) := by
  have hdiff (B : E →ᵃ[ℝ] ℝ) (x y : E) : B.linear (x - y) = B x - B y := by
    simpa only [vsub_eq_sub] using B.linearMap_vsub x y
  let z := u - p
  have hzA : A.linear z = 0 := by rw [hdiff, huA, hpA, sub_self]
  have hzC : C.linear z ≠ 0 := by simpa only [z, hdiff, hpC, sub_zero] using huC
  obtain ⟨v, hv⟩ := LinearMap.surjective hA (1 : ℝ)
  let w := v - (C.linear v / C.linear z) • z
  have hwA : A.linear w = 1 := by
    simp only [w, map_sub, map_smul, hzA, smul_eq_mul, mul_zero, sub_zero, hv]
  have hwC : C.linear w = 0 := by
    simp only [w, map_sub, map_smul, smul_eq_mul]
    rw [div_mul_cancel₀ _ hzC, sub_self]
  have hadd (B : E →ᵃ[ℝ] ℝ) (v : E) : B (p + v) = B p + B.linear v := by
    simpa only [vadd_eq_add, add_comm] using B.map_vadd p v
  have hminusA : A (p + -w) = -1 := by rw [hadd, map_neg, hwA, hpA, zero_add]
  have hplusA : A (p + w) = 1 := by rw [hadd, hwA, hpA, zero_add]
  have hminusC : C (p + -w) = 0 := by rw [hadd, map_neg, hwC, hpC, neg_zero, zero_add]
  have hplusC : C (p + w) = 0 := by rw [hadd, hwC, hpC, zero_add]
  have hcv : Convex ℝ {x | C x = 0} := (convex_singleton (0 : ℝ)).affine_preimage C
  have hn := hcv.mem_closure_lower_affine_height A hpC hminusC
    (by rw [hminusA, hpA]; norm_num)
  have hp := hcv.mem_closure_upper_affine_height A hpC hplusC
    (by rw [hplusA, hpA]; norm_num)
  simpa only [hpA] using And.intro hn hp

end AffineMap

namespace AffineMap

theorem intrinsicInterior_image_of_injOn_span
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E →ᵃ[ℝ] F) (s : Set E) (hf : InjOn f (affineSpan ℝ s)) :
    intrinsicInterior ℝ (f '' s) = f '' intrinsicInterior ℝ s := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  let A := affineSpan ℝ s
  let B := affineSpan ℝ (f '' s)
  let : Nonempty A := ⟨⟨hs.choose, subset_affineSpan ℝ s hs.choose_spec⟩⟩
  let : Nonempty B := ⟨⟨f hs.choose,
    subset_affineSpan ℝ (f '' s) (mem_image_of_mem f hs.choose_spec)⟩⟩
  have hmap : A.map f = B := AffineSubspace.map_span f s
  let g : A →ᵃ[ℝ] B := f.restrict hmap.le
  have hginj : Function.Injective g := by
    intro x y hxy
    exact Subtype.ext (hf x.property y.property (congrArg Subtype.val hxy))
  let e : A ≃ᵃ[ℝ] B := AffineEquiv.ofBijective
    ⟨hginj, AffineMap.restrict.surjective f hmap⟩
  let h := e.toContinuousAffineEquiv.toHomeomorph
  have hpre : h '' (Subtype.val ⁻¹' s : Set A) =
      (Subtype.val ⁻¹' (f '' s) : Set B) := by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
    · intro y hy
      obtain ⟨x, hx, hxy⟩ := hy
      refine ⟨⟨x, subset_affineSpan ℝ s hx⟩, hx, ?_⟩
      exact Subtype.ext hxy
  change Subtype.val '' interior (Subtype.val ⁻¹' (f '' s) : Set B) =
    f '' (Subtype.val '' interior (Subtype.val ⁻¹' s : Set A))
  rw [← hpre, ← h.image_interior, image_image, image_image]
  rfl

end AffineMap
