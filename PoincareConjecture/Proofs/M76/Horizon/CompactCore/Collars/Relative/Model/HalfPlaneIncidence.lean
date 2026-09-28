import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Simplicial.FullSubcomplexStars
import PoincareConjecture.Proofs.M76.PrimeReduction.BoundaryFacetLinks
import PoincareConjecture.Proofs.M76.Mathlib.InteriorFullCofaces
import PoincareConjecture.Proofs.M76.Mathlib.EmbeddedVertexIncidence
import PoincareConjecture.Proofs.M76.Mathlib.AffineStarFacetLinks
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.EmbeddedFaceDimension

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

local notation "P2" => (ℝ × ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)

omit [FiniteDimensional ℝ E] in

theorem exists_halfPlane_star_of_quadrant_ambient_star
    (K N : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hNK : N ≤ K)
    (hfull : ∀ s ∈ K.faces, (∀ v ∈ s, v ∈ N.vertices) → s ∈ N.faces)
    {p : E} (hp : p ∈ N.vertices) (f : E → C3)
    (hf : (K.closedStar p).AffineOnFaces f)
    (hfi : InjOn f (K.closedStar p).space)
    (hint : f p ∈ interior (f '' (K.closedStar p).space))
    (hsection : ∀ x ∈ (K.closedStar p).space,
      x ∈ N.space ↔ 0 ≤ (f x).1.1 ∧ (f x).2 = 0) :
    ∃ (a : E → P2) (U : Set P2),
      (N.closedStar p).AffineOnFaces a ∧ InjOn a (N.closedStar p).space ∧
      IsOpen U ∧ a p ∈ U ∧
      a '' (N.closedStar p).space ⊆ {z | 0 ≤ z.1} ∧
      U ∩ {z | 0 ≤ z.1} ⊆ a '' (N.closedStar p).space ∧
      ∀ x, a x = (f x).1 := by
  let pi : C3 →ᴬ[ℝ] P2 := (ContinuousLinearMap.fst ℝ P2 ℝ).toContinuousAffineMap
  let a : E → P2 := pi ∘ f
  let j : P2 → C3 := fun z => (z, 0)
  let U : Set P2 := j ⁻¹' interior (f '' (K.closedStar p).space)
  have hj : Continuous j := continuous_id.prodMk continuous_const
  have hstar := K.closedStar_space_eq_inter_of_full N hK hNK hfull hp
  have hNKstar : N.closedStar p ≤ K.closedStar p :=
    fun _ hs => ⟨hNK hs.1, hNK hs.2⟩
  have hplane {x : E} (hx : x ∈ (N.closedStar p).space) : j (a x) = f x := by
    have hz := ((hsection x (hstar.subset hx).1).mp (hstar.subset hx).2).2
    exact Prod.ext rfl hz.symm
  have hpstar : p ∈ (N.closedStar p).space := by
    apply (N.closedStar p).vertices_subset_space
    have hpface : {p} ∈ N.faces := hp
    exact ⟨hpface, by simpa using hpface⟩
  have hfN : (N.closedStar p).AffineOnFaces f := fun s hs => hf s (hNKstar hs)
  refine ⟨a, U, hfN.postcomp pi, ?_,
    isOpen_interior.preimage hj, ?_, ?_, ?_, fun _ => rfl⟩
  · intro x hx y hy he
    exact hfi (hstar.subset hx).1 (hstar.subset hy).1
      ((hplane hx).symm.trans ((congrArg j he).trans (hplane hy)))
  · change j (a p) ∈ interior (f '' (K.closedStar p).space)
    rwa [hplane hpstar]
  · rintro z ⟨x, hx, rfl⟩
    exact ((hsection x (hstar.subset hx).1).mp (hstar.subset hx).2).1
  · rintro z ⟨hzU, hzpos⟩
    obtain ⟨x, hx, hfx⟩ := interior_subset hzU
    have hxN : x ∈ N.space := (hsection x hx).mpr (by
      rw [hfx]
      exact ⟨hzpos, rfl⟩)
    refine ⟨x, hstar.symm.subset ⟨hx, hxN⟩, ?_⟩
    exact congrArg Prod.fst hfx

theorem face_card_le_three_of_planar_star
    (K : SimplicialComplex ℝ E) {s : Finset E} (hs : s ∈ K.faces)
    {p : E} (hps : p ∈ s) (a : E → P2)
    (ha : (K.closedStar p).AffineOnFaces a) (hai : InjOn a (K.closedStar p).space) :
    s.card ≤ 3 := by
  have hsS : s ∈ (K.closedStar p).faces :=
    ⟨hs, by simpa [Finset.insert_eq_of_mem hps] using hs⟩
  simpa using ha.face_card_le_of_injOn hai hsS

theorem face_card_le_two_of_planar_line_star
    (K : SimplicialComplex ℝ E) {s : Finset E} (hs : s ∈ K.faces)
    {p : E} (hps : p ∈ s) (a : E → P2)
    (ha : (K.closedStar p).AffineOnFaces a) (hai : InjOn a (K.closedStar p).space)
    (hzero : ∀ x ∈ (K.closedStar p).space, (a x).1 = 0) : s.card ≤ 2 := by
  let pi : P2 →ᴬ[ℝ] ℝ := (ContinuousLinearMap.snd ℝ ℝ ℝ).toContinuousAffineMap
  have hb : (K.closedStar p).AffineOnFaces (pi ∘ a) := ha.postcomp pi
  have hbi : InjOn (pi ∘ a) (K.closedStar p).space := by
    intro x hx y hy hxy
    exact hai hx hy (Prod.ext ((hzero x hx).trans (hzero y hy).symm) hxy)
  have hsS : s ∈ (K.closedStar p).faces :=
    ⟨hs, by simpa [Finset.insert_eq_of_mem hps] using hs⟩
  simpa using hb.face_card_le_of_injOn hbi hsS

theorem mem_closure_interior_of_halfPlane_germ {S U : Set P2}
    (hU : IsOpen U) (hUS : U ∩ {z | 0 ≤ z.1} ⊆ S)
    {x : P2} (hxU : x ∈ U) (hx : 0 ≤ x.1) : x ∈ closure (interior S) := by
  have hxcl : x ∈ closure ({z : P2 | 0 < z.1}) := by
    rw [show {z : P2 | 0 < z.1} = Ioi (0 : ℝ) ×ˢ (univ : Set ℝ) by ext z; simp]
    rw [closure_prod_eq, closure_Ioi, closure_univ]
    exact ⟨hx, mem_univ _⟩
  apply closure_mono (s := U ∩ {z : P2 | 0 < z.1}) ?_ (hU.inter_closure ⟨hxU, hxcl⟩)
  exact interior_maximal (fun z hz => hUS ⟨hz.1, (show 0 < z.1 from hz.2).le⟩)
    (hU.inter (isOpen_lt continuous_const continuous_fst))

theorem exists_triangle_coface_of_halfPlane_germ
    (K : SimplicialComplex ℝ P2) (hK : K.faces.Finite)
    {s : Finset P2} (hs : s ∈ K.faces) {U : Set P2} (hU : IsOpen U)
    (hhalf : K.space ⊆ {z | 0 ≤ z.1})
    (hUS : U ∩ {z | 0 ≤ z.1} ⊆ K.space)
    (hmeet : (convexHull ℝ (s : Set P2) ∩ U).Nonempty) :
    ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 3 := by
  obtain ⟨x, hxs, hxU⟩ :=
    (convex_convexHull ℝ (s : Set P2)).intrinsicInterior_inter_open_nonempty hU hmeet
  have hxhalf := hhalf (K.convexHull_subset_space hs (intrinsicInterior_subset hxs))
  obtain ⟨t, ht, htc, hxt⟩ := K.exists_full_face_of_mem_closure_interior hK
    (mem_closure_interior_of_halfPlane_germ hU hUS hxU hxhalf)
  refine ⟨t, ht, K.subset_of_mem_intrinsicInterior_face hs ht hxs hxt, ?_⟩
  simpa using htc

theorem exists_triangle_coface_of_halfPlane_star
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {s : Finset E} (hs : s ∈ K.faces) {p : E} (hps : p ∈ s)
    (a : E → P2) (ha : (K.closedStar p).AffineOnFaces a)
    (hai : InjOn a (K.closedStar p).space)
    {U : Set P2} (hU : IsOpen U) (hpU : a p ∈ U)
    (hhalf : a '' (K.closedStar p).space ⊆ {z | 0 ≤ z.1})
    (hUS : U ∩ {z | 0 ≤ z.1} ⊆ a '' (K.closedStar p).space) :
    ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 3 := by
  classical
  let S := K.closedStar p
  have hsS : s ∈ S.faces := ⟨hs, by simpa [Finset.insert_eq_of_mem hps] using hs⟩
  let J := ha.embeddedImage hai
  have hJ := ha.embeddedImage_finite hai (finite_closedStar_faces hK p)
  have hsJ : s.image a ∈ J.faces :=
    (ha.image_mem_embeddedImage_iff hai (S.subset_space hsS)).mpr hsS
  have hJs : J.space = a '' S.space := ha.embeddedImage_space hai
  obtain ⟨t, ht, hst, htc⟩ := J.exists_triangle_coface_of_halfPlane_germ hJ hsJ hU
    (hJs.symm ▸ hhalf) (hJs.symm ▸ hUS)
    ⟨a p, subset_convexHull ℝ _ (Finset.mem_image.mpr ⟨p, hps, rfl⟩), hpU⟩
  rw [ha.embeddedImage_faces hai] at ht
  obtain ⟨t, ht, rfl⟩ := ht
  refine ⟨t, ht.1, ?_, ?_⟩
  · intro x hxs
    obtain ⟨y, hyt, hyx⟩ := Finset.mem_image.mp (hst (Finset.mem_image.mpr ⟨x, hxs, rfl⟩))
    exact hai (S.subset_space ht hyt) (S.subset_space hsS hxs) hyx ▸ hyt
  · exact (Finset.card_image_iff.mpr (hai.mono (S.subset_space ht))).symm.trans htc

theorem faceLink_ncard_eq_one_of_halfPlane_star
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {s : Finset E} (hs : s ∈ K.faces) (hs2 : s.card = 2)
    {p : E} (hps : p ∈ s) (a : E → P2)
    (ha : (K.closedStar p).AffineOnFaces a) (hai : InjOn a (K.closedStar p).space)
    {U : Set P2} (hU : IsOpen U) (hpU : a p ∈ U)
    (hhalf : a '' (K.closedStar p).space ⊆ {z | 0 ≤ z.1})
    (hUS : U ∩ {z | 0 ≤ z.1} ⊆ a '' (K.closedStar p).space)
    (hzero : ∀ x ∈ s, (a x).1 = 0) :
    (K.faceLink s).vertices.ncard = 1 := by
  classical
  let S := K.closedStar p
  have hsS : s ∈ S.faces := ⟨hs, by simpa [Finset.insert_eq_of_mem hps] using hs⟩
  obtain ⟨t, ht, hst, htc⟩ := K.exists_triangle_coface_of_halfPlane_star hK hs hps
    a ha hai hU hpU hhalf hUS
  have htS : t ∈ S.faces := ⟨ht, by simpa [Finset.insert_eq_of_mem (hst hps)] using ht⟩
  let J := ha.embeddedImage hai
  have hsJ : s.image a ∈ J.faces :=
    (ha.image_mem_embeddedImage_iff hai (S.subset_space hsS)).mpr hsS
  have htJ : t.image a ∈ J.faces :=
    (ha.image_mem_embeddedImage_iff hai (S.subset_space htS)).mpr htS
  have hscJ : (s.image a).card = Module.finrank ℝ P2 := by
    rw [Finset.card_image_iff.mpr (hai.mono (S.subset_space hsS)), hs2]
    simp
  have htcJ : (t.image a).card = Module.finrank ℝ P2 + 1 := by
    rw [Finset.card_image_iff.mpr (hai.mono (S.subset_space htS)), htc]
    simp
  let ell : P2 →ᴬ[ℝ] ℝ := (ContinuousLinearMap.fst ℝ ℝ ℝ).toContinuousAffineMap
  have hJhalf : J.space ⊆ {z | 0 ≤ ell z} := by
    rw [ha.embeddedImage_space hai]
    exact hhalf
  have hJzero : ∀ x ∈ convexHull ℝ (s.image a : Set P2), ell x = 0 := by
    have hv : EqOn ell.toAffineMap (AffineMap.const ℝ P2 0) (s.image a : Set P2) := by
      intro z hz
      obtain ⟨x, hxs, rfl⟩ := Finset.mem_image.mp hz
      exact hzero x hxs
    exact fun x hx => AffineMap.eqOn_affineSpan hv (convexHull_subset_affineSpan _ hx)
  have hc := J.faceLink_ncard_eq_one_of_halfspace hsJ hscJ htJ
    (Finset.image_subset_image hst) htcJ ell (1, 0) rfl hJhalf hJzero
  rw [ha.ncard_embeddedImage_faceLink hai hsS] at hc
  have hlink : S.faceLink s = K.faceLink s := by
    rw [show S = K.closedFaceStar {p} from (K.closedFaceStar_singleton_eq_closedStar p).symm]
    exact K.closedFaceStar_faceLink_of_subset (Finset.singleton_subset_iff.mpr hps)
  rwa [hlink] at hc

theorem faceLink_ncard_eq_two_of_halfPlane_star
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {s : Finset E} (hs : s ∈ K.faces) (hs2 : s.card = 2)
    {p : E} (hps : p ∈ s) (a : E → P2)
    (ha : (K.closedStar p).AffineOnFaces a) (hai : InjOn a (K.closedStar p).space)
    {U : Set P2} (hU : IsOpen U) (hpU : a p ∈ U)
    (hUS : U ∩ {z | 0 ≤ z.1} ⊆ a '' (K.closedStar p).space)
    (hppos : 0 < (a p).1) :
    (K.faceLink s).vertices.ncard = 2 := by
  classical
  let S := K.closedStar p
  have hsS : s ∈ S.faces := ⟨hs, by simpa [Finset.insert_eq_of_mem hps] using hs⟩
  let J := ha.embeddedImage hai
  have hJ := ha.embeddedImage_finite hai (finite_closedStar_faces hK p)
  have hsJ : s.image a ∈ J.faces :=
    (ha.image_mem_embeddedImage_iff hai (S.subset_space hsS)).mpr hsS
  have hscJ : (s.image a).card = Module.finrank ℝ P2 := by
    rw [Finset.card_image_iff.mpr (hai.mono (S.subset_space hsS)), hs2]
    simp
  have hpint : a p ∈ interior J.space := by
    rw [ha.embeddedImage_space hai]
    exact interior_maximal (fun z hz => hUS ⟨hz.1, (show 0 < z.1 from hz.2).le⟩)
      (hU.inter (isOpen_lt continuous_const continuous_fst)) ⟨hpU, hppos⟩
  have hc := J.faceLink_ncard_eq_two_of_hull_meets_interior hJ hsJ hscJ
    ⟨a p, subset_convexHull ℝ _ (Finset.mem_image.mpr ⟨p, hps, rfl⟩), hpint⟩
  rw [ha.ncard_embeddedImage_faceLink hai hsS] at hc
  have hlink : S.faceLink s = K.faceLink s := by
    rw [show S = K.closedFaceStar {p} from (K.closedFaceStar_singleton_eq_closedStar p).symm]
    exact K.closedFaceStar_faceLink_of_subset (Finset.singleton_subset_iff.mpr hps)
  rwa [hlink] at hc

end Geometry.SimplicialComplex
