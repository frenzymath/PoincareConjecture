import PoincareConjecture.Proofs.M76.Triangulation.ZeroChargeSphereCollarsData
import PoincareConjecture.Proofs.M76.Triangulation.AuxiliaryOriginalPolygonCutBox
import PoincareConjecture.Proofs.M76.Mathlib.PolygonAffineImage

set_option autoImplicit false

open Set Geometry CoordinateHalfBoxes

namespace PoincareConjecture.M76.ZeroChargeJoint

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E] {n : ℕ}

theorem exists_sphere_collar_event_box
    (K : SimplicialComplex ℝ E) (hdim : Module.finrank ℝ E = 3)
    (A : E →ᵃ[ℝ] ℝ) (c : ℝ) (P : Polygon E (n + 3))
    (hP : P.HasSimplicialEdges) (hPinj : Function.Injective P)
    (hsection : P.boundary ℝ = K.space ∩ {x | A x = c})
    (t : Fin (n + 3) → ℝ) (ht : ∀ i, t i ∈ Ioo (0 : ℝ) 1)
    (i : Fin (n + 3)) (b : SphereCollarBody K (P (finRotate (n + 3) i)))
    (hpos : P (finRotate (n + 3) i) ∈ closure (K.space ∩ {x | c < A x}))
    (hneg : P (finRotate (n + 3) i) ∈ closure (K.space ∩ {x | A x < c}))
    (s : Bool → Finset E) (hs : ∀ j, s j ∈ K.faces) (hcard : ∀ j, (s j).card = 3)
    (ha : ∀ j, P.edgeCut t (if j then finRotate (n + 3) i else i) ∈
      intrinsicInterior ℝ (convexHull ℝ (s j : Set E)))
    (haC : ∀ j : Bool, sphereCollarCenter (P (finRotate (n + 3) i))
      (P.edgeCut t (if j then finRotate (n + 3) i else i)) ∈ interior b.carrier)
    (f : Bool → ((ℝ × ℝ) × ℝ) ≃ᴬ[ℝ] E)
    (hfzero : ∀ j, f j 0 = P.edgeCut t (if j then finRotate (n + 3) i else i))
    {R : ℝ} (hR : 0 < R)
    (harc : ∀ j x, x ∈ box R →
      (f j x ∈ P.cutArc t (if j then finRotate (n + 3) i else i) ↔
        x.1.1 = 0 ∧ x.2 = 0 ∧ 0 ≤ x.1.2))
    (hfheight : ∀ j x, A (f j x) = c + x.1.1)
    (hsurface : ∀ j x, x ∈ box R → (f j x ∈ K.space ↔ x.2 = 0))
    {d : Set E} (hd : IsFinitePLBallPair (ℝ × ℝ) d (K.space ∩ {x | A x = c}))
    (hdplane : d ⊆ {x | A x = c})
    (hinward : ∀ j x, x ∈ box R → x.1.1 = 0 → (f j x ∈ d ↔ 0 ≤ x.2))
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ (delta : ℝ) (H : OpenPartialHomeomorph E ((ℝ × ℝ) × ℝ))
      (F : ((ℝ × ℝ) × ℝ) → E) (k : Bool → ℝ),
      delta ∈ Ioo 0 epsilon ∧ delta < R ∧ (∀ j, 0 < k j) ∧
      H.source = (sphereCollarCenter (P (finRotate (n + 3) i))) ⁻¹' interior b.carrier ∧
      F = H.symm ∘ longitudinalPrismCoordinates delta (-1) 1 ∧
      F '' box delta ⊆ H.source ∧
      FinitePiecewiseAffineOn F (box delta) ∧ InjOn F (box delta) ∧
      IsFinitePLBallPair ((ℝ × ℝ) × ℝ) (F '' box delta) (F '' boxBoundary delta) ∧
      (∀ x ∈ box delta, A (F x) = c + x.1.1) ∧
      (∀ x ∈ box delta, F x ∈ K.space ↔ x.2 = 0) ∧
      (∀ j u z, u ∈ Icc (-delta) delta → z ∈ Icc (-delta) delta →
        F ((u, if j then delta else -delta), z) = f j ((u, 0), z)) ∧
      (∀ j, f j '' box delta ⊆ H.source) ∧
      (∀ j x, x ∈ box delta →
        H (f j x) = ((x.1.1, (if j then 1 else -1) + k j * x.1.2), x.2)) ∧
      (∀ x ∈ box delta, H (F x) = longitudinalPrismCoordinates delta (-1) 1 x) ∧
      F '' (({0} ×ˢ Icc (-delta) delta) ×ˢ {0}) = P.cutArc t i := by
  classical
  let q := P (finRotate (n + 3) i)
  let tau := sphereCollarCenter q
  let K0 := sphereCollarOriginal K q
  let Q := P.affineImage tau.toAffineEquiv.toAffineMap
  have htclosed (j : Fin (n + 3)) : t j ∈ Icc (0 : ℝ) 1 :=
    ⟨(ht j).1.le, (ht j).2.le⟩
  have hqA : A q = c := (hsection.subset (P.vertex_mem_boundary _)).2
  have htau (x : E) : tau x = x - q := by
    change -q + x = x - q
    abel
  have htauq : tau q = 0 := by rw [htau, sub_self]
  have hheight (x : E) : A.linear (tau x) = A x - c := by
    rw [htau]
    simpa only [vsub_eq_sub, hqA] using A.linearMap_vsub x q
  have hback (y : E) : A (tau.symm y) = c + A.linear y := by
    have h := hheight (tau.symm y)
    rw [tau.apply_symm_apply] at h
    linarith
  have hKmem (x : E) : tau x ∈ K0.space ↔ x ∈ K.space := by
    rw [b.original_space]
    exact tau.injective.mem_set_image
  have hlevel : tau '' (K.space ∩ {x | A x = c}) = K0.space ∩ {x | A.linear x = 0} := by
    ext y
    obtain ⟨x, rfl⟩ := tau.surjective y
    rw [tau.injective.mem_set_image]
    simp only [mem_inter_iff, mem_ofPred_eq, hKmem, hheight, sub_eq_zero]
  have hpositive : tau '' (K.space ∩ {x | c < A x}) =
      K0.space ∩ {x | 0 < A.linear x} := by
    ext y
    obtain ⟨x, rfl⟩ := tau.surjective y
    rw [tau.injective.mem_set_image]
    simp only [mem_inter_iff, mem_ofPred_eq, hKmem, hheight, sub_pos]
  have hnegative : tau '' (K.space ∩ {x | A x < c}) =
      K0.space ∩ {x | A.linear x < 0} := by
    ext y
    obtain ⟨x, rfl⟩ := tau.surjective y
    rw [tau.injective.mem_set_image]
    simp only [mem_inter_iff, mem_ofPred_eq, hKmem, hheight, sub_neg]
  have hpos0 : (0 : E) ∈ closure (K0.space ∩ {x | 0 < A.linear x}) := by
    rw [← hpositive]
    change (0 : E) ∈ closure (tau.toHomeomorph '' (K.space ∩ {x | c < A x}))
    rw [← tau.toHomeomorph.image_closure]
    exact ⟨q, hpos, htauq⟩
  have hneg0 : (0 : E) ∈ closure (K0.space ∩ {x | A.linear x < 0}) := by
    rw [← hnegative]
    change (0 : E) ∈ closure (tau.toHomeomorph '' (K.space ∩ {x | A x < c}))
    rw [← tau.toHomeomorph.image_closure]
    exact ⟨q, hneg, htauq⟩
  have hQ : Q.HasSimplicialEdges :=
    P.hasSimplicialEdges_affineImage hP tau.toAffineEquiv.toAffineMap tau.injective
  have hQinj : Function.Injective Q := tau.injective.comp hPinj
  have hQsection : Q.boundary ℝ = K0.space ∩ {x | A.linear x = 0} := by
    rw [Polygon.affineImage_boundary, hsection]
    exact hlevel
  have hQzero : Q (finRotate (n + 3) i) = 0 := htauq
  have hcut (j : Fin (n + 3)) : Q.edgeCut t j = tau (P.edgeCut t j) := by
    change AffineMap.lineMap (tau (P j)) (tau (P (finRotate (n + 3) j))) (t j) =
      tau (AffineMap.lineMap (P j) (P (finRotate (n + 3) j)) (t j))
    exact (tau.toAffineEquiv.toAffineMap.apply_lineMap _ _ _).symm
  have hsegment (a b : E) : tau '' segment ℝ a b = segment ℝ (tau a) (tau b) :=
    image_segment ℝ tau.toAffineEquiv.toAffineMap a b
  have hcutArc (j : Fin (n + 3)) : Q.cutArc t j = tau '' P.cutArc t j := by
    rw [Q.cutArc_eq_segments t htclosed j, P.cutArc_eq_segments t htclosed j,
      image_union, hsegment, hsegment, hcut, hcut]
    rfl
  let s0 (j : Bool) := (s j).image tau
  have hs0 (j : Bool) : s0 j ∈ K0.faces := by
    change (s j).image tau ∈
      ((K.affineOnFaces_affine tau.toContinuousAffineMap).embeddedImage tau.injective.injOn).faces
    rw [(K.affineOnFaces_affine tau.toContinuousAffineMap).embeddedImage_faces tau.injective.injOn]
    exact mem_image_of_mem _ (hs j)
  have hcard0 (j : Bool) : (s0 j).card = 3 :=
    (Finset.card_image_iff.mpr tau.injective.injOn).trans (hcard j)
  have hhull (j : Bool) : convexHull ℝ (s0 j : Set E) =
      tau '' convexHull ℝ (s j : Set E) := by
    dsimp only [s0]
    rw [Finset.coe_image]
    exact ((K.affineOnFaces_affine tau.toContinuousAffineMap).image_convexHull (hs j)).symm
  have ha0 (j : Bool) : Q.edgeCut t (if j then finRotate (n + 3) i else i) ∈
      intrinsicInterior ℝ (convexHull ℝ (s0 j : Set E)) := by
    rw [hcut, hhull, tau.intrinsicInterior_image]
    exact mem_image_of_mem tau (ha j)
  have haC0 (j : Bool) : Q.edgeCut t (if j then finRotate (n + 3) i else i) ∈
      interior b.carrier := by rw [hcut]; exact haC j
  let f0 (j : Bool) := (f j).trans tau
  have hf0zero (j : Bool) : f0 j 0 = Q.edgeCut t (if j then finRotate (n + 3) i else i) := by
    change tau (f j 0) = _
    rw [hfzero, hcut]
  have harc0 (j : Bool) (x : (ℝ × ℝ) × ℝ) (hx : x ∈ box R) :
      f0 j x ∈ Q.cutArc t (if j then finRotate (n + 3) i else i) ↔
        x.1.1 = 0 ∧ x.2 = 0 ∧ 0 ≤ x.1.2 := by
    change tau (f j x) ∈ Q.cutArc t _ ↔ _
    rw [hcutArc, tau.injective.mem_set_image]
    exact harc j x hx
  have hf0height (j : Bool) (x : (ℝ × ℝ) × ℝ) : A.linear (f0 j x) = x.1.1 := by
    change A.linear (tau (f j x)) = _
    rw [hheight, hfheight, add_sub_cancel_left]
  have hsurface0 (j : Bool) (x : (ℝ × ℝ) × ℝ) (hx : x ∈ box R) :
      f0 j x ∈ K0.space ↔ x.2 = 0 :=
    (hKmem (f j x)).trans (hsurface j x hx)
  have hd0 : IsFinitePLBallPair (ℝ × ℝ) (tau '' d) (K0.space ∩ {x | A.linear x = 0}) := by
    have h := hd.affine_image tau.toContinuousAffineMap tau.injective.injOn
    change IsFinitePLBallPair (ℝ × ℝ) (tau '' d)
      (tau '' (K.space ∩ {x | A x = c})) at h
    rwa [hlevel] at h
  have hd0plane : tau '' d ⊆ {x | A.linear x = 0} := by
    rintro _ ⟨x, hx, rfl⟩
    change A.linear (tau x) = 0
    rw [hheight, hdplane hx, sub_self]
  have hinward0 (j : Bool) (x : (ℝ × ℝ) × ℝ) (hx : x ∈ box R) (hx0 : x.1.1 = 0) :
      f0 j x ∈ tau '' d ↔ 0 ≤ x.2 := by
    change tau (f j x) ∈ tau '' d ↔ _
    rw [tau.injective.mem_set_image]
    exact hinward j x hx hx0
  let ι := ↥b.halfspaces
  let : Nonempty ι := by
    obtain ⟨Z, hZ⟩ := b.halfspaces_nonempty
    exact ⟨⟨Z, hZ⟩⟩
  let Z : ι → E →ₗ[ℝ] ℝ := fun j => j.val
  have hZ (j : ι) : Z j ≠ 0 := b.halfspaces_nonzero j.val j.property
  have hrep : b.carrier = {x | ∀ j, Z j x ≤ 1} := by
    rw [b.halfspaces_carrier]
    ext x
    constructor
    · intro hx j
      exact hx j.val j.property
    · intro hx L hL
      exact hx ⟨L, hL⟩
  obtain ⟨delta, H0, F0, k, hdelta, hdeltaR, hk, hsource0, hform0, hFsource0,
      hFPL0, hFinj0, hball0, hFheight0, hFsurface0, hlateral0, hcutSource0,
      hcutForward0, hforward0, hcore0⟩ :=
    K0.exists_auxiliary_original_polygon_cut_box b.original_finite b.original_bound
      b.auxiliary b.auxiliary_finite b.auxiliary_space b.pure b.cofaces b.zero_vertex
      b.connected_link hdim A.linear hpos0 hneg0 Q hQ hQinj hQsection t ht i hQzero
      b.compact b.convex b.zero_interior b.disjoint_link b.local_star b.original_incidence
      Z hZ hrep b.frontierComplex b.frontier_finite b.frontier_space
      s0 hs0 hcard0 ha0 haC0 f0 hf0zero hR harc0 hf0height hsurface0 hd0 hd0plane hinward0 hepsilon
  let H := tau.toHomeomorph.transOpenPartialHomeomorph H0
  let F : ((ℝ × ℝ) × ℝ) → E := tau.symm ∘ F0
  have hsource : H.source = tau ⁻¹' interior b.carrier := by
    change tau ⁻¹' H0.source = tau ⁻¹' interior b.carrier
    rw [hsource0]
  refine ⟨delta, H, F, k, hdelta, hdeltaR, hk, hsource, ?_, ?_,
    hFPL0.postcomp tau.symm.toContinuousAffineMap, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · funext x
    change tau.symm (F0 x) = tau.symm (H0.symm (longitudinalPrismCoordinates delta (-1) 1 x))
    exact congrArg (fun g : ((ℝ × ℝ) × ℝ) → E => tau.symm (g x)) hform0
  · rintro _ ⟨x, hx, rfl⟩
    change tau (tau.symm (F0 x)) ∈ H0.source
    rw [tau.apply_symm_apply]
    exact hFsource0 (mem_image_of_mem _ hx)
  · intro x hx y hy heq
    exact hFinj0 hx hy (tau.symm.injective heq)
  · have h := hball0.affine_image tau.symm.toContinuousAffineMap tau.symm.injective.injOn
    change IsFinitePLBallPair ((ℝ × ℝ) × ℝ) (tau.symm '' (F0 '' box delta))
      (tau.symm '' (F0 '' boxBoundary delta)) at h
    rw [image_image, image_image] at h
    exact h
  · intro x hx
    change A (tau.symm (F0 x)) = c + x.1.1
    rw [hback, hFheight0 x hx]
  · intro x hx
    have h := (hKmem (tau.symm (F0 x))).symm
    rw [tau.apply_symm_apply] at h
    exact h.trans (hFsurface0 x hx)
  · intro j u z hu hz
    change tau.symm (F0 ((u, if j then delta else -delta), z)) = _
    rw [hlateral0 j u z hu hz]
    exact tau.symm_apply_apply _
  · intro j
    rintro _ ⟨x, hx, rfl⟩
    change tau (f j x) ∈ H0.source
    exact hcutSource0 j (mem_image_of_mem _ hx)
  · intro j x hx
    change H0 (tau (f j x)) = _
    exact hcutForward0 j x hx
  · intro x hx
    change H0 (tau (tau.symm (F0 x))) = _
    rw [tau.apply_symm_apply]
    exact hforward0 x hx
  · calc
      F '' (({0} ×ˢ Icc (-delta) delta) ×ˢ {0}) =
          tau.symm '' (F0 '' (({0} ×ˢ Icc (-delta) delta) ×ˢ {0})) :=
        (image_image tau.symm F0 _).symm
      _ = tau.symm '' (tau '' P.cutArc t i) := by rw [hcore0, hcutArc]
      _ = P.cutArc t i := by simp only [image_image, tau.symm_apply_apply, image_id']

end PoincareConjecture.M76.ZeroChargeJoint
