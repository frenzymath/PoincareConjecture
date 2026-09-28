import PoincareConjecture.Proofs.M76.Dehn.OriginalDoubleArcSurgeryStep
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.TwoCofaceCarrierGerm
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.VerticalTrianglePairCrossing
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.IntrinsicAffineGerms
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.EmbeddedFaceDimension
import PoincareConjecture.Proofs.M76.Mathlib.EmbeddedManifoldConditions
import PoincareConjecture.Proofs.M76.Mathlib.FaceLinkCofaceCount
import PoincareConjecture.Proofs.M76.Mathlib.InteriorFacetLinks
import PoincareConjecture.Proofs.M76.Mathlib.FiniteCarrierFaceInteriors
import PoincareConjecture.Proofs.M76.Mathlib.PositiveFaceCenterAtPoint
import PoincareConjecture.Proofs.M76.Mathlib.HeightPlaneAffineCoordinates
import Mathlib.LinearAlgebra.Dual.Lemmas












set_option autoImplicit false

open Set Metric Geometry Topology unitInterval
open scoped BigOperators

namespace PoincareConjecture.M76.Dehn

local notation "V3" => (Fin 3 → ℝ)
local notation "V2" => (ℝ × ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)

private theorem actual_edge_cofaces
    (K : SimplicialComplex ℝ V3) (hK : K.faces.Finite)
    {q : V3 → V2} (hq : K.AffineOnFaces q) (hi : InjOn q K.space)
    {s : Finset V3} (hs : s ∈ K.faces) (hs2 : s.card = 2)
    {p : V3} (hps : p ∈ convexHull ℝ (s : Set V3))
    (hint : q p ∈ interior (q '' K.space)) :
    ∃ a b : Finset V3, a ∈ K.faces ∧ b ∈ K.faces ∧
      a.card = 3 ∧ b.card = 3 ∧ s ⊆ a ∧ s ⊆ b ∧ a ≠ b ∧
      ∀ t ∈ K.faces, s ⊆ t → t ⊆ a ∨ t ⊆ b := by
  classical
  let N := hq.embeddedImage hi
  have hN : N.faces.Finite := hq.embeddedImage_finite hi hK
  have hsN : s.image q ∈ N.faces :=
    (hq.image_mem_embeddedImage_iff hi (K.subset_space hs)).mpr hs
  have hcard : (s.image q).card = Module.finrank ℝ V2 := by
    rw [Finset.card_image_iff.mpr (hi.mono (K.subset_space hs)), hs2]
    simp [Module.finrank_prod]
  have hqp : q p ∈ convexHull ℝ (s.image q : Set V2) := by
    rw [Finset.coe_image, ← hq.image_convexHull hs]
    exact mem_image_of_mem q hps
  have hqpint : q p ∈ interior N.space := by
    rw [hq.embeddedImage_space hi]
    exact hint
  have hcount := N.faceLink_ncard_eq_two_of_hull_meets_interior
    hN hsN hcard ⟨q p, hqp, hqpint⟩
  rw [hq.ncard_embeddedImage_faceLink hi hs,
    K.ncard_faceLink_vertices_eq_cofaces, hs2] at hcount
  obtain ⟨a, b, hab, hset⟩ := ncard_eq_two.mp hcount
  have ha : a ∈ K.faces ∧ a.card = 3 ∧ s ⊆ a := by
    change a ∈ {t | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}
    rw [hset]
    exact Or.inl rfl
  have hb : b ∈ K.faces ∧ b.card = 3 ∧ s ⊆ b := by
    change b ∈ {t | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}
    rw [hset]
    exact Or.inr rfl
  refine ⟨a, b, ha.1, hb.1, ha.2.1, hb.2.1, ha.2.2, hb.2.2, hab, ?_⟩
  intro t ht hst
  have ht3 : t.card ≤ 3 := by
    simpa [Module.finrank_prod] using hq.face_card_le_of_injOn hi ht
  have ht2 := Finset.card_le_card hst
  by_cases he : t.card = 2
  · have hst' : s = t := Finset.eq_of_subset_of_card_le hst (by omega)
    exact Or.inl (hst' ▸ ha.2.2)
  · have hmem : t ∈ {u | u ∈ K.faces ∧ u.card = 3 ∧ s ⊆ u} := ⟨ht, by omega, hst⟩
    rw [hset] at hmem
    exact hmem.elim (fun h => Or.inl (h ▸ Finset.Subset.rfl))
      (fun h => Or.inr (h ▸ Finset.Subset.rfl))

private theorem signed_edge_vertices
    (K : SimplicialComplex ℝ V3) {s : Finset V3} (hs : s ∈ K.faces)
    (hs2 : s.card = 2) (ell : V3 →L[ℝ] ℝ) {p : V3}
    (hp : p ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set V3)))
    (hpzero : ell p = 0) (hne : ∃ v ∈ s, ell v ≠ 0) :
    ∃ u v : V3, u ≠ v ∧ s = {u, v} ∧ ell u < 0 ∧ 0 < ell v ∧
      p ∈ segment ℝ u v := by
  classical
  obtain ⟨u, v, huv, hsuv⟩ := Finset.card_eq_two.mp hs2
  obtain ⟨w, hw, _hsum, hval⟩ :=
    (K.indep hs).exists_positive_weights_of_mem_intrinsicInterior hp
  have hwu := hw u (hsuv.symm ▸ Finset.mem_insert_self _ _)
  have hwv := hw v (hsuv.symm ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have hbalance : w u * ell u + w v * ell v = 0 := by
    have h := congrArg ell hval
    simpa only [hsuv, Finset.sum_pair huv, map_add, map_smul, smul_eq_mul, hpzero] using h
  have hn : ell u ≠ 0 ∨ ell v ≠ 0 := by
    obtain ⟨z, hz, hzero⟩ := hne
    simp only [hsuv, Finset.mem_insert, Finset.mem_singleton] at hz
    exact hz.elim (fun h => Or.inl (h ▸ hzero)) (fun h => Or.inr (h ▸ hzero))
  have hpseg : p ∈ segment ℝ u v := by
    simpa only [hsuv, Finset.coe_pair, convexHull_pair] using intrinsicInterior_subset hp
  by_cases hu : ell u < 0
  · have hv : 0 < ell v := by
      by_contra h
      have h0 := mul_nonpos_of_nonneg_of_nonpos hwv.le (le_of_not_gt h)
      have h1 := mul_neg_of_pos_of_neg hwu hu
      linarith
    exact ⟨u, v, huv, hsuv, hu, hv, hpseg⟩
  · have hv : ell v < 0 := by
      by_contra h
      have hu0 : 0 ≤ ell u := le_of_not_gt hu
      have hv0 : 0 ≤ ell v := le_of_not_gt h
      rcases hn with hn | hn
      · have h1 := mul_pos hwu (lt_of_le_of_ne hu0 (Ne.symm hn))
        have h0 := mul_nonneg hwv.le hv0
        linarith
      · have h1 := mul_pos hwv (lt_of_le_of_ne hv0 (Ne.symm hn))
        have h0 := mul_nonneg hwu.le hu0
        linarith
    have hu' : 0 < ell u := by
      by_contra h
      have h0 := mul_nonpos_of_nonneg_of_nonpos hwu.le (le_of_not_gt h)
      have h1 := mul_neg_of_pos_of_neg hwv hv
      linarith
    exact ⟨v, u, huv.symm, hsuv.trans (Finset.pair_comm _ _), hv, hu',
      (segment_symm ℝ u v) ▸ hpseg⟩

private theorem height_edge_coordinates
    (ell : V3 →L[ℝ] ℝ) {u v p : V3} (hu : ell u < 0) (hv : 0 < ell v)
    (hp : p ∈ segment ℝ u v) (hpzero : ell p = 0) :
    ∃ F : C3 ≃ᴬ[ℝ] V3, F 0 = p ∧
      (∀ z, ell (F z) = z.2) ∧ F.symm u = ((0, 0), ell u) ∧
      F.symm v = ((0, 0), ell v) := by
  have hgap : ell v - ell u ≠ 0 := (sub_pos.mpr (hu.trans hv)).ne'
  let d : V3 := (ell v - ell u)⁻¹ • (v - u)
  have hd : ell d = 1 := by
    simp only [d, map_smul, map_sub, smul_eq_mul, inv_mul_cancel₀ hgap]
  have hell : ell.toLinearMap ≠ 0 := by
    intro h
    have h0 : ell d = 0 := by
      change ell.toLinearMap d = 0
      rw [h]
      rfl
    linarith
  have hker : Module.finrank ℝ ell.ker = 2 := by
    have h := Module.Dual.finrank_ker_add_one_of_ne_zero hell
    have hdim : Module.finrank ℝ V3 = 3 := by simp
    change Module.finrank ℝ ell.ker + 1 = Module.finrank ℝ V3 at h
    omega
  let e : V2 ≃ₗ[ℝ] ell.ker := LinearEquiv.ofFinrankEq _ _ (by
    simp [Module.finrank_prod, hker])
  let L : C3 →ₗ[ℝ] V3 :=
    (ell.ker.subtype.comp e.toLinearMap).comp (LinearMap.fst ℝ V2 ℝ) +
      (LinearMap.snd ℝ V2 ℝ).smulRight d
  have hL (z : C3) : L z = (e z.1 : V3) + z.2 • d := rfl
  have hheight (z : C3) : ell (L z) = z.2 := by
    have he0 : ell (e z.1 : V3) = 0 := (e z.1).property
    rw [hL, map_add, map_smul, he0, hd]
    simp
  have hi : Function.Injective L := by
    intro x y hxy
    have hlast : x.2 = y.2 := (hheight x).symm.trans ((congrArg ell hxy).trans (hheight y))
    have hfirst : (e x.1 : V3) = e y.1 := by
      have heq : (e x.1 : V3) + y.2 • d = (e y.1 : V3) + y.2 • d := by
        simpa only [hL, hlast] using hxy
      exact add_right_cancel heq
    exact Prod.ext (e.injective (Subtype.ext hfirst)) hlast
  have hsurj : Function.Surjective L := by
    intro x
    let y : ell.ker := ⟨x - ell x • d, by
      change ell (x - ell x • d) = 0
      rw [map_sub, map_smul, hd]
      simp⟩
    refine ⟨(e.symm y, ell x), ?_⟩
    rw [hL, e.apply_symm_apply]
    change x - ell x • d + ell x • d = x
    abel
  let A := (LinearEquiv.ofBijective L ⟨hi, hsurj⟩).toContinuousLinearEquiv
  let F := A.toLinearEquiv.toAffineEquiv.toContinuousAffineEquiv.trans
    (ContinuousAffineEquiv.constVAdd ℝ V3 p)
  have hF (z : C3) : F z = L z + p := add_comm _ _
  have hFp : F 0 = p := by rw [hF, map_zero, zero_add]
  have hFpheight (z : C3) : ell (F z) = z.2 := by
    rw [hF, map_add, hpzero, add_zero, hheight]
  obtain ⟨t, _ht, htp⟩ := (segment_eq_image_lineMap ℝ u v).subset hp
  have hvalue : u + t • (v - u) = p := by
    rw [AffineMap.lineMap_apply_module] at htp
    calc
      u + t • (v - u) = (1 - t) • u + t • v := by module
      _ = p := htp
  have htvalue : t * (ell v - ell u) = -ell u := by
    have h := congrArg ell hvalue
    rw [map_add, map_smul, map_sub, hpzero] at h
    change ell u + t * (ell v - ell u) = 0 at h
    linarith
  have htdiv : t = -ell u * (ell v - ell u)⁻¹ := by
    rw [← div_eq_mul_inv]
    exact (eq_div_iff hgap).mpr htvalue
  have haxis (r : ℝ) : F ((0, 0), r) = r • d + p := by
    rw [hF, hL]
    change (e (0 : V2) : V3) + r • d + p = r • d + p
    rw [map_zero]
    change (0 : V3) + r • d + p = r • d + p
    rw [zero_add]
  have haxisu : F ((0, 0), ell u) = u := by
    rw [haxis, ← hvalue, htdiv]
    dsimp only [d]
    module
  have haxisv : F ((0, 0), ell v) = v := by
    calc
      F ((0, 0), ell v) = F ((0, 0), ell u) + (ell v - ell u) • d := by
        rw [haxis, haxis]
        module
      _ = u + (v - u) := by
        rw [haxisu]
        dsimp only [d]
        rw [smul_smul, mul_inv_cancel₀ hgap, one_smul]
      _ = v := by abel
  refine ⟨F, hFp, hFpheight, ?_, ?_⟩
  · exact (congrArg F.symm haxisu).symm.trans (F.symm_apply_apply _)
  · exact (congrArg F.symm haxisv).symm.trans (F.symm_apply_apply _)

private theorem triangle_height_crossing
    (K : SimplicialComplex ℝ V3) (hK : K.faces.Finite)
    (hbound : ∀ t ∈ K.faces, t.card ≤ 3)
    {s : Finset V3} (hs : s ∈ K.faces) (hs3 : s.card = 3)
    (ell : V3 →L[ℝ] ℝ) {p : V3}
    (hp : p ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set V3)))
    (hpzero : ell p = 0) (hne : ∃ v ∈ s, ell v ≠ 0)
    {O : Set V3} (hO : IsOpen O) (hpO : p ∈ O) :
    ∃ H : OpenPartialHomeomorph V3 C3,
      p ∈ H.source ∧ H.source ⊆ O ∧ H p = 0 ∧
      LocallyPiecewiseAffineOn H H.source ∧
      LocallyPiecewiseAffineOn H.symm H.target ∧
      (∀ x ∈ H.source, x ∈ K.space ↔ (H x).1.1 = 0) ∧
      ∀ x ∈ H.source, ell x = (H x).2 := by
  have hmax : ∀ t ∈ K.faces, s ⊆ t → t = s := by
    intro t ht hst
    exact (Finset.eq_of_subset_of_card_le hst (by simpa only [hs3] using hbound t ht)).symm
  obtain ⟨U, hU, hpU, hKU⟩ := K.exists_open_maximal_face_affine_germ hK hs hmax hp
  have hpP : p ∈ affineSpan ℝ (s : Set V3) :=
    convexHull_subset_affineSpan (s := (s : Set V3)) (intrinsicInterior_subset hp)
  obtain ⟨v, hv, hvzero⟩ := hne
  obtain ⟨F, hFzero, hFell, hFplane⟩ :=
    (affineSpan ℝ (s : Set V3)).exists_centered_height_plane_coordinates (by simp)
      (K.finrank_faceDirection_of_card hs hs3) ell.toAffineMap
      ⟨v, subset_affineSpan ℝ _ hv, p, hpP, by
        change ell v ≠ ell p
        rwa [hpzero]⟩ hpP
  let S : C3 ≃L[ℝ] C3 := {
    toFun := fun z => ((z.2, z.1.2), z.1.1)
    invFun := fun z => ((z.2, z.1.2), z.1.1)
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  let A := F.symm.trans S.toLinearEquiv.toAffineEquiv.toContinuousAffineEquiv
  let H := A.toHomeomorph.toOpenPartialHomeomorphOfImageEq
    (O ∩ U) (hO.inter hU) (A '' (O ∩ U)) rfl
  refine ⟨H, ⟨hpO, hpU⟩, fun _ hx => hx.1, ?_,
    locallyPiecewiseAffineOn_affine A.toContinuousAffineMap H.open_source,
    locallyPiecewiseAffineOn_affine A.symm.toContinuousAffineMap H.open_target, ?_, ?_⟩
  · change S (F.symm p) = 0
    rw [← hFzero, F.symm_apply_apply, map_zero]
  · intro x hx
    change x ∈ K.space ↔ (F.symm x).2 = 0
    exact (hKU x hx.2).trans (by simpa only [F.apply_symm_apply] using hFplane (F.symm x))
  · intro x _
    change ell x = (F.symm x).1.1
    have hh := hFell (F.symm x)
    change ell (F (F.symm x)) = ell p + (F.symm x).1.1 at hh
    simpa only [F.apply_symm_apply, hpzero, zero_add] using hh

private theorem edge_height_crossing
    (K : SimplicialComplex ℝ V3) (hK : K.faces.Finite)
    {q : V3 → V2} (hq : K.AffineOnFaces q) (hi : InjOn q K.space)
    {s : Finset V3} (hs : s ∈ K.faces) (hs2 : s.card = 2)
    (ell : V3 →L[ℝ] ℝ) {p : V3}
    (hp : p ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set V3)))
    (hpzero : ell p = 0) (hne : ∃ v ∈ s, ell v ≠ 0)
    (hint : q p ∈ interior (q '' K.space))
    {O : Set V3} (hO : IsOpen O) (hpO : p ∈ O) :
    ∃ H : OpenPartialHomeomorph V3 C3,
      p ∈ H.source ∧ H.source ⊆ O ∧ H p = 0 ∧
      LocallyPiecewiseAffineOn H H.source ∧
      LocallyPiecewiseAffineOn H.symm H.target ∧
      (∀ x ∈ H.source, x ∈ K.space ↔ (H x).1.1 = 0) ∧
      ∀ x ∈ H.source, ell x = (H x).2 := by
  classical
  obtain ⟨u, v, _huv, hsuv, hu, hv, hpseg⟩ :=
    signed_edge_vertices K hs hs2 ell hp hpzero hne
  obtain ⟨a, b, ha, hb, ha3, hb3, hsa, hsb, hab, hcofaces⟩ :=
    actual_edge_cofaces K hK hq hi hs hs2 (intrinsicInterior_subset hp) hint
  obtain ⟨U, hU, hpU, hKU⟩ :=
    K.exists_open_two_coface_carrier_germ hK hs ha hb hcofaces hp
  obtain ⟨F, hFzero, hFell, hFu, hFv⟩ := height_edge_coordinates ell hu hv hpseg hpzero
  obtain ⟨w, hws, hwa⟩ := Finset.exists_eq_insert_iff.mpr ⟨hsa, by omega⟩
  obtain ⟨z, hzs, hzb⟩ := Finset.exists_eq_insert_iff.mpr ⟨hsb, by omega⟩
  have haxis (r : ℝ) : F ((0, 0), r) ∈ affineSpan ℝ (s : Set V3) := by
    rw [hsuv, Finset.coe_pair]
    apply mem_affineSpan_pair_iff_exists_lineMap_eq.mpr
    refine ⟨(r - ell u) / (ell v - ell u), ?_⟩
    apply F.symm.injective
    have hline : F.symm (AffineMap.lineMap u v ((r - ell u) / (ell v - ell u))) =
        AffineMap.lineMap (F.symm u) (F.symm v) ((r - ell u) / (ell v - ell u)) :=
      F.symm.toAffineEquiv.apply_lineMap _ _ _
    rw [hline, hFu, hFv, F.symm_apply_apply]
    have hgap : ell v - ell u ≠ 0 := (sub_pos.mpr (hu.trans hv)).ne'
    ext <;> simp only [AffineMap.lineMap_apply_module, Prod.smul_fst,
      Prod.smul_snd, Prod.fst_add, Prod.snd_add, smul_eq_mul, mul_zero, add_zero]
    field_simp [hgap]
    ring
  have hnonzero {t : Finset V3} (ht : t ∈ K.faces) {r : V3}
      (hrs : r ∉ s) (hrt : insert r s = t) : (F.symm r).1 ≠ 0 := by
    intro hr
    have hrspan : r ∈ affineSpan ℝ (s : Set V3) := by
      have he : F ((0, 0), (F.symm r).2) = r := by
        change F ((0 : V2), (F.symm r).2) = r
        rw [← hr]
        exact F.apply_symm_apply r
      exact he ▸ haxis (F.symm r).2
    have hrt' : r ∈ t := hrt ▸ Finset.mem_insert_self r s
    have hst : s ⊆ t := hrt ▸ Finset.subset_insert r s
    have himage : Subtype.val '' {x : t | (x : V3) ∈ s} = (s : Set V3) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        exact ⟨⟨x, hst hx⟩, hx, rfl⟩
    exact hrs ((K.indep ht).mem_affineSpan_iff ⟨r, hrt'⟩
      {x : t | (x : V3) ∈ s} |>.mp (himage.symm ▸ hrspan))
  have hw := hnonzero ha hws hwa
  have hz := hnonzero hb hzs hzb
  have hFhull (S : Set V3) : F.symm '' convexHull ℝ S =
      convexHull ℝ (F.symm '' S) := F.symm.toAffineEquiv.toAffineMap.image_convexHull S
  have hcoord (r : V3) : F.symm '' convexHull ℝ (↑(insert r s) : Set V3) =
      convexHull ℝ ({((0, 0), ell u), ((0, 0), ell v), F.symm r} : Set C3) := by
    rw [hFhull]
    simp only [Finset.coe_insert, hsuv, Finset.coe_singleton, image_insert_eq,
      image_singleton, hFu, hFv]
    congr 1
    ext x
    simp only [mem_insert_iff, mem_singleton_iff]
    tauto
  have habs : a ∩ b = s := by
    have hle : (a ∩ b).card ≤ 2 := by
      by_contra hn
      have he : a ∩ b = a :=
        Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
      have hab' : a ⊆ b := he ▸ Finset.inter_subset_right
      exact hab (Finset.eq_of_subset_of_card_le hab' (by omega))
    exact (Finset.eq_of_subset_of_card_le (Finset.subset_inter hsa hsb) (by omega)).symm
  have haxisHull : F.symm '' convexHull ℝ (s : Set V3) ⊆ {x : C3 | x.1 = 0} := by
    rw [hFhull]
    simp only [hsuv, Finset.coe_pair, image_insert_eq, image_singleton, hFu, hFv]
    apply convexHull_min
    · rintro x (rfl | rfl) <;> rfl
    · exact (convex_singleton (0 : V2)).linear_preimage (LinearMap.fst ℝ V2 ℝ)
  have hback {t : Finset V3} {x : C3}
      (hx : x ∈ F.symm '' convexHull ℝ (t : Set V3)) :
      F x ∈ convexHull ℝ (t : Set V3) := by
    obtain ⟨y, hy, rfl⟩ := hx
    simpa only [F.apply_symm_apply] using hy
  have hinter (x : C3)
      (hxa : x ∈ convexHull ℝ ({(0, ell u), (0, ell v), F.symm w} : Set C3))
      (hxb : x ∈ convexHull ℝ ({(0, ell u), (0, ell v), F.symm z} : Set C3)) :
      x.1 = 0 := by
    have hxA : F x ∈ convexHull ℝ (a : Set V3) := hwa ▸ hback ((hcoord w).symm.subset hxa)
    have hxB : F x ∈ convexHull ℝ (b : Set V3) := hzb ▸ hback ((hcoord z).symm.subset hxb)
    have hxS : F x ∈ convexHull ℝ (s : Set V3) := by
      rw [← habs, Finset.coe_inter, ← K.convexHull_inter_convexHull ha hb]
      exact ⟨hxA, hxB⟩
    exact haxisHull ⟨F x, hxS, F.symm_apply_apply x⟩
  obtain ⟨T, hTzero, hTO, hT0, hTPL, hTlast, hTwhole⟩ :=
    exists_vertical_triangle_pair_crossing_chart hw hz hu hv
      (F.symm w).2 (F.symm z).2 hinter
      (F.symm.toHomeomorph.isOpenMap _ (hO.inter hU))
      ⟨p, ⟨hpO, hpU⟩, by
        change F.symm p = 0
        rw [← hFzero, F.symm_apply_apply]⟩
  let H := F.symm.toHomeomorph.toOpenPartialHomeomorph.trans T
  have hsource (x : V3) : x ∈ H.source ↔ F.symm x ∈ T.source := by
    change x ∈ univ ∩ F.symm ⁻¹' T.source ↔ _
    exact and_iff_right (mem_univ x)
  have hOsource {x : V3} (hx : x ∈ H.source) : x ∈ O ∩ U := by
    obtain ⟨y, hy, he⟩ := hTO ((hsource x).mp hx)
    exact F.symm.injective he ▸ hy
  refine ⟨H, (hsource p).mpr (by rw [← hFzero, F.symm_apply_apply]; exact hTzero),
    fun _ hx => (hOsource hx).1, ?_, ?_, ?_, ?_, ?_⟩
  · change T (F.symm p) = 0
    rw [← hFzero, F.symm_apply_apply, hT0]
  · exact hTPL.1.comp
      (locallyPiecewiseAffineOn_affine F.symm.toContinuousAffineMap isOpen_univ)
  · exact ((locallyPiecewiseAffineOn_affine F.toContinuousAffineMap isOpen_univ).comp
      hTPL.2).mono H.open_target (fun _ hx => ⟨hx.1, mem_univ _⟩)
  · intro x hx
    change x ∈ K.space ↔ (T (F.symm x)).1.1 = 0
    rw [hKU x (hOsource hx).2, ← hTwhole _ ((hsource x).mp hx)]
    have hmem (t : Finset V3) :
        F.symm x ∈ F.symm '' convexHull ℝ (t : Set V3) ↔
          x ∈ convexHull ℝ (t : Set V3) := F.symm.injective.mem_set_image
    change x ∈ convexHull ℝ (a : Set V3) ∪ convexHull ℝ (b : Set V3) ↔
      F.symm x ∈ convexHull ℝ ({((0, 0), ell u), ((0, 0), ell v), F.symm w} : Set C3) ∪
        convexHull ℝ ({((0, 0), ell u), ((0, 0), ell v), F.symm z} : Set C3)
    rw [← hcoord w, ← hcoord z, hwa, hzb]
    exact (or_congr (hmem a) (hmem b)).symm
  · intro x hx
    change ell x = (T (F.symm x)).2
    rw [hTlast _ ((hsource x).mp hx)]
    simpa only [F.apply_symm_apply] using hFell (F.symm x)

private theorem free_point_height_crossing
    (K : SimplicialComplex ℝ V3) (hK : K.faces.Finite)
    {q : V3 → V2} (hq : K.AffineOnFaces q) (hi : InjOn q K.space)
    (ell : V3 →L[ℝ] ℝ) {p : V3} (hp : p ∈ K.space)
    (hpzero : ell p = 0) (hint : q p ∈ interior (q '' K.space))
    (hfaces : ∀ s ∈ K.faces, p ∈ convexHull ℝ (s : Set V3) →
      ∃ v ∈ s, ell v ≠ 0)
    {O : Set V3} (hO : IsOpen O) (hpO : p ∈ O) :
    ∃ H : OpenPartialHomeomorph V3 C3,
      p ∈ H.source ∧ H.source ⊆ O ∧ H p = 0 ∧
      LocallyPiecewiseAffineOn H H.source ∧
      LocallyPiecewiseAffineOn H.symm H.target ∧
      (∀ x ∈ H.source, x ∈ K.space ↔ (H x).1.1 = 0) ∧
      ∀ x ∈ H.source, ell x = (H x).2 := by
  classical
  obtain ⟨s, hs, hps⟩ := K.exists_face_intrinsicInterior_of_finite hK hp
  have hbound (t : Finset V3) (ht : t ∈ K.faces) : t.card ≤ 3 := by
    simpa [Module.finrank_prod] using hq.face_card_le_of_injOn hi ht
  have hspos := Finset.card_pos.mpr (K.nonempty_of_mem_faces hs)
  have hne := hfaces s hs (intrinsicInterior_subset hps)
  have hs1 : s.card ≠ 1 := by
    intro he
    obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp he
    have hpv : p = v := by
      simpa only [Finset.coe_singleton, convexHull_singleton, mem_singleton_iff] using
        intrinsicInterior_subset hps
    obtain ⟨x, hx, hnx⟩ := hne
    apply hnx
    rw [Finset.mem_singleton.mp hx, ← hpv]
    exact hpzero
  by_cases hs2 : s.card = 2
  · exact edge_height_crossing K hK hq hi hs hs2 ell hps hpzero hne hint hO hpO
  · exact triangle_height_crossing K hK hbound hs (by have := hbound s hs; omega)
      ell hps hpzero hne hO hpO




theorem exists_free_point_height_crossing
    (K : SimplicialComplex ℝ V3) (hK : K.faces.Finite)
    {q : V3 → V2} (hq : K.AffineOnFaces q) (hi : InjOn q K.space)
    (ell : V3 →L[ℝ] ℝ) {p : V3} (hp : p ∈ K.space)
    (hpzero : ell p = 0) (hint : q p ∈ interior (q '' K.space))
    (hfaces : ∀ s ∈ K.faces, p ∈ convexHull ℝ (s : Set V3) →
      ∃ v ∈ s, ell v ≠ 0)
    {O : Set V3} (hO : IsOpen O) (hpO : p ∈ O) :
    ∃ H : OpenPartialHomeomorph V3 C3,
      p ∈ H.source ∧ H.source ⊆ O ∧ H p = 0 ∧
      LocallyPiecewiseAffineOn H H.source ∧
      LocallyPiecewiseAffineOn H.symm H.target ∧
      (∀ x ∈ H.source, x ∈ K.space ↔ (H x).1.1 = 0) ∧
      ∀ x ∈ H.source, ell x = (H x).2 := by
  exact free_point_height_crossing K hK hq hi ell hp hpzero hint hfaces hO hpO




theorem exists_carrier_height_crossing
    (K : SimplicialComplex ℝ V3) (hK : K.faces.Finite)
    {q : V3 → V2} (hq : K.AffineOnFaces q) (hi : InjOn q K.space)
    (ell : V3 →L[ℝ] ℝ) {p : V3} (hp : p ∈ K.space)
    (hpzero : ell p = 0) (hint : q p ∈ interior (q '' K.space))
    (hfaces : ∀ s ∈ K.faces, p ∈ convexHull ℝ (s : Set V3) →
      ∃ v ∈ s, ell v ≠ 0)
    {O : Set V3} (hO : IsOpen O) (hpO : p ∈ O) :
    ∃ H : OpenPartialHomeomorph V3 C3,
      p ∈ H.source ∧ H.source ⊆ O ∧ H p = 0 ∧
      LocallyPiecewiseAffineOn H H.source ∧
      LocallyPiecewiseAffineOn H.symm H.target ∧
      (∀ x ∈ H.source, x ∈ K.space ↔ (H x).1.1 = 0) ∧
      ∀ x ∈ H.source, ell x = (H x).2 :=
  exists_free_point_height_crossing K hK hq hi ell hp hpzero hint hfaces hO hpO

open Classical in






theorem exists_repaired_free_branch_crossings
    (J K K₀ : SimplicialComplex ℝ V3) (hK : K.faces.Finite)
    {P₀ : Set V3} {ρ ε : ℝ} (hball : ball (0 : V3) ρ ⊆ interior J.space)
    (hprotected : K₀.space = P₀) (hcollar : P₀ = K.space \ ball (0 : V3) ρ)
    (q : V3 → V2) (hq : K.AffineOnFaces q) (hi : InjOn q K.space)
    (hint : ∀ x ∈ K.space, x ∈ interior J.space → q x ∈ interior (q '' K.space))
    (ell : V3 →L[ℝ] ℝ) (H : PLCarrierMotion J.space P₀ ε)
    (hH : K.AffineOnFaces (H.map 1))
    (hzero : ∀ s ∈ K.faces, (∀ v ∈ s, ell (H.map 1 v) = 0) → s ∈ K₀.faces) :
    ∃ A : SimplicialComplex ℝ V3,
      A.faces.Finite ∧ A.faces = (fun s => s.image (H.map 1)) '' K.faces ∧
      A.space = H.map 1 '' K.space ∧
      A.AffineOnFaces (q ∘ (H.map 1).symm) ∧
      InjOn (q ∘ (H.map 1).symm) A.space ∧
      ∀ p ∈ A.space, p ∈ ball (0 : V3) ρ → ell p = 0 →
        ∀ O : Set V3, IsOpen O → p ∈ O →
          ∃ T : OpenPartialHomeomorph V3 C3,
            p ∈ T.source ∧ T.source ⊆ O ∧ T p = 0 ∧
            LocallyPiecewiseAffineOn T T.source ∧
            LocallyPiecewiseAffineOn T.symm T.target ∧
            (∀ x ∈ T.source, x ∈ A.space ↔ (T x).1.1 = 0) ∧
            ∀ x ∈ T.source, ell x = (T x).2 := by
  classical
  have hHi : InjOn (H.map 1) K.space := (H.map 1).injective.injOn
  let A := hH.embeddedImage hHi
  have hA : A.faces.Finite := hH.embeddedImage_finite hHi hK
  have hAs : A.space = H.map 1 '' K.space := hH.embeddedImage_space hHi
  have hleft : LeftInvOn (H.map 1).symm (H.map 1) K.space :=
    fun x _ => (H.map 1).symm_apply_apply x
  have hparam := hH.comp_inverse_on_embeddedImage hq hHi hleft
  have hparami := hH.injOn_comp_inverse_on_embeddedImage hHi hi hleft
  have hparamimage : (q ∘ (H.map 1).symm) '' A.space = q '' K.space := by
    rw [hAs, image_image]
    congr 1
    funext x
    exact congrArg q ((H.map 1).symm_apply_apply x)
  have hinterior : H.map 1 '' interior J.space = interior J.space :=
    ((H.map 1).image_interior J.space).trans (congrArg interior (H.carrier 1))
  refine ⟨A, hA, hH.embeddedImage_faces hHi, hAs, hparam, hparami, ?_⟩
  intro p hp hpball hpzero O hO hpO
  have hpinv : (H.map 1).symm p ∈ K.space := by
    obtain ⟨x, hx, rfl⟩ := hAs.subset hp
    simpa only [(H.map 1).symm_apply_apply] using hx
  have hpint : (H.map 1).symm p ∈ interior J.space := by
    obtain ⟨x, hx, rfl⟩ := hinterior.symm.subset (hball hpball)
    simpa only [(H.map 1).symm_apply_apply] using hx
  have hparamint : (q ∘ (H.map 1).symm) p ∈
      interior ((q ∘ (H.map 1).symm) '' A.space) := by
    rw [hparamimage]
    exact hint _ hpinv hpint
  have hfree (s : Finset V3) (hs : s ∈ A.faces)
      (hps : p ∈ convexHull ℝ (s : Set V3)) : ∃ v ∈ s, ell v ≠ 0 := by
    by_contra hn
    have hz : ∀ v ∈ s, ell v = 0 := by
      intro v hv
      by_contra h
      exact hn ⟨v, hv, h⟩
    change s ∈ (hH.embeddedImage hHi).faces at hs
    rw [hH.embeddedImage_faces hHi] at hs
    obtain ⟨t, ht, rfl⟩ := hs
    have ht₀ : t ∈ K₀.faces := hzero t ht
      (fun v hv => hz _ (Finset.mem_image.mpr ⟨v, hv, rfl⟩))
    rw [Finset.coe_image, ← hH.image_convexHull ht] at hps
    obtain ⟨x, hx, hxp⟩ := hps
    have hxP₀ : x ∈ P₀ := hprotected.subset (K₀.convexHull_subset_space ht₀ hx)
    have hxp' : x = p := (H.fixed_protected 1 x hxP₀).symm.trans hxp
    exact (hcollar.subset hxP₀).2 (hxp'.symm ▸ hpball)
  exact free_point_height_crossing A hA hparam hparami ell hp hpzero hparamint hfree hO hpO

end PoincareConjecture.M76.Dehn

namespace Geometry.OriginalPLTower

open PoincareConjecture.M76.Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1

variable {M ι : Type*} [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M V3} {S : SimplicialComplex ℝ V2}
  {f : V2 → M} {r : M → ℝ} {C : Set M}








theorem Step.exists_original_free_branch_crossings
    {s t : Stage e S f r C} (step : Step s t) {R Fmark : Set M}
    (he : PoincareConjecture.M76.PLDomain e R) (hF : Fmark ⊆ frontier R)
    {base : Fmark} {Jgroup : Subgroup (FundamentalGroup Fmark base)}
    (old : StageMarkedDisk t R Fmark base Jgroup)
    (a b : D) (hab : a ≠ b) (haint : (a : V2) ∉ Rim)
    (hpair : step.projection (step.inclusion (old.map a)) =
      step.projection (step.inclusion (old.map b)))
    {W : Set s.Carrier} (hW : IsOpen W)
    (haW : step.projection (step.inclusion (old.map a)) ∈ W)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (w : TwoBranchWindow (step.projection ∘ step.inclusion))
      (c : V3 ≃L[ℝ] C3) (Q : OpenPartialHomeomorph s.Carrier V3)
      (J A : SimplicialComplex ℝ V3) (ρ : ℝ)
      (G : I → t.Carrier ≃ₜ t.Carrier) (new : StageMarkedDisk t R Fmark base Jgroup),
      old.map a ∈ w.left.source ∧ old.map b ∈ w.right.source ∧
      step.projection (step.inclusion (old.map a)) ∈ Q.source ∧
      Q (step.projection (step.inclusion (old.map a))) = 0 ∧
      Q.source ⊆ W ∩ interior (s.projection ⁻¹' R) ∧ Q.source ⊆ w.target ∧
      (∀ k, (s.charts k).symm.trans Q ∈ piecewiseAffineGroupoid V3) ∧
      (∀ k, (t.charts k).symm.trans (w.left.trans Q) ∈ piecewiseAffineGroupoid V3 ∧
        (t.charts k).symm.trans (w.right.trans Q) ∈ piecewiseAffineGroupoid V3) ∧
      J.faces.Finite ∧ J.space ⊆ Q.target ∧ 0 < ρ ∧
      ball (0 : V3) ρ ⊆ interior J.space ∧
      (step.projection ∘ step.inclusion) ⁻¹' (Q.symm '' J.space) =
        (w.left.trans Q).symm '' J.space ∪ (w.right.trans Q).symm '' J.space ∧
      Continuous (fun z : I × t.Carrier => G z.1 z.2) ∧
      Continuous (fun z : I × t.Carrier => (G z.1).symm z.2) ∧
      (∀ x, G 0 x = x) ∧
      (∀ u, EqOn (G u) id ((w.right.trans Q).symm '' J.space)ᶜ) ∧
      (∀ u, EqOn (G u) id w.left.source) ∧
      (∀ u, EqOn (G u) id (frontier (t.projection ⁻¹' R))) ∧
      (∀ u, (G u) ⁻¹' (t.projection ⁻¹' R) = t.projection ⁻¹' R) ∧
      (∀ u k l, (t.charts k).symm.trans
        ((G u).toOpenPartialHomeomorph.trans (t.charts l)) ∈ piecewiseAffineGroupoid V3) ∧
      (∀ x, new.map x = G 1 (old.map x)) ∧ new.rim = old.rim ∧
      HEq new.basepath old.basepath ∧ (∀ x : Rim, new.map x = old.map x) ∧
      (∀ y ∈ Q.source,
        y ∈ (step.projection ∘ step.inclusion) '' (new.map '' D ∩ w.left.source) ↔
          (c (Q y)).2 = 0) ∧
      A.faces.Finite ∧
      A.space = (w.right.trans Q) '' (new.map '' D ∩ (w.right.trans Q).source) ∩
        J.space ∧
      (∀ p ∈ A.space, p ∈ ball (0 : V3) ρ → (c p).2 = 0 →
        ∀ O : Set V3, IsOpen O → p ∈ O →
          ∃ T : OpenPartialHomeomorph V3 C3,
            p ∈ T.source ∧ T.source ⊆ O ∩ ball (0 : V3) ρ ∧ T p = 0 ∧
            LocallyPiecewiseAffineOn T T.source ∧
            LocallyPiecewiseAffineOn T.symm T.target ∧
            (∀ x ∈ T.source, x ∈ A.space ↔ (T x).1.1 = 0) ∧
            ∀ x ∈ T.source, (c x).2 = (T x).2) ∧
      ∃ (Z : SimplicialComplex ℝ (V2 × V2)) (E : SimplicialComplex ℝ V2)
        (first : Z.space ≃ₜ E.space),
        Z.faces.Finite ∧ E.faces.Finite ∧
        Z.space = {z | z.1 ∈ D ∧ z.2 ∈ D ∧
          step.projection (step.inclusion (new.map z.1)) =
            step.projection (step.inclusion (new.map z.2)) ∧ z.1 ≠ z.2} ∧
        E.space = {x | x ∈ D ∧ ∃ y ∈ D, x ≠ y ∧
          step.projection (step.inclusion (new.map x)) =
            step.projection (step.inclusion (new.map y))} ∧
        first.IsFinitePL ∧ first.symm.IsFinitePL ∧
        ∀ z : Z.space, (first z : V2) = z.val.1 := by
  classical
  obtain ⟨w, c, Q, J, P, P₀, R₀, K, K₀, L, q, ρ, δ,
    ha, hb, haQ, hQzero, hQinside, hQw, hQPL, hbranches, hplane,
    hJ, _hcv, hJQ, _hzeroJ, hρ, hball, _hP, _hP₀, _hPs, hP₀s,
    _hbB, _hzeroP, _hq, hqi, hqint, hR₀, _hR₀J, hKR, hKs, hqK,
    _hK₀K, hK₀s, _hL, _hLs, _hlinks, hwhole, _hδ, _hmargin, hmotions⟩ :=
    step.exists_original_protected_branch_operation he hF old a b hab haint hpair hW haW
  obtain ⟨H, hHaff, _hsign, _hzero, hfaces, _hposition,
    Kamb, Knew, _hKamb, _hKambs, _hKnew, _hKnews, _hK₀new,
    _hnewparam, _hnewparami, _hnewstars, _hnewlinks,
    G, new, hG, hGinv, hGzero, _hGB, hGout, _hGprotected, hGleft,
    hGfront, hGregion, hGPL, hnewmap, hrim, hpath, hrimvalues, himage,
    Z, E, first, hZ, hE, hZs, hEs, hfirst, hfirstinv, hfirstval⟩ := hmotions ε hε
  let ell : V3 →L[ℝ] ℝ :=
    (ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ).comp c.toContinuousLinearMap
  have hK : K.faces.Finite := hR₀.subset hKR
  have hHi : K.AffineOnFaces (H.map 1) := fun s hs => hHaff s (hKR hs)
  have hcollar : P₀.space = K.space \ ball (0 : V3) ρ := by
    rw [hKs]
    exact hP₀s
  have hint (x : V3) (hx : x ∈ K.space) (hxJ : x ∈ interior J.space) :
      q x ∈ interior (q '' K.space) := by
    rw [hKs]
    exact hqint x (hKs.subset hx) hxJ
  obtain ⟨A, hA, _hAfaces, hAs, _hAparam, _hAparami, hcross⟩ :=
    exists_repaired_free_branch_crossings J K K₀ hK hball
    hK₀s hcollar q hqK (hqi.mono hKs.subset) hint ell H hHi
      (fun face hface hz => ((hfaces face hface).mp hz).1)
  have hleftimage : new.map '' D ∩ w.left.source = old.map '' D ∩ w.left.source := by
    ext x
    constructor
    · rintro ⟨⟨y, hy, hyx⟩, hx⟩
      have he : G 1 (old.map y) = x := (hnewmap y).symm.trans hyx
      have he' : old.map y = x := (G 1).injective (he.trans (hGleft 1 hx).symm)
      exact ⟨⟨y, hy, he'⟩, hx⟩
    · rintro ⟨⟨y, hy, rfl⟩, hx⟩
      refine ⟨⟨y, hy, ?_⟩, hx⟩
      exact (hnewmap y).trans (hGleft 1 hx)
  refine ⟨w, c, Q, J, A, ρ, G, new,
    ha, hb, haQ, hQzero, hQinside, hQw, hQPL, hbranches,
    hJ, hJQ, hρ, hball, hwhole, hG, hGinv, hGzero, hGout, hGleft,
    hGfront, hGregion, hGPL, hnewmap, hrim, hpath, hrimvalues, ?_, hA, ?_, ?_,
    Z, E, first, hZ, hE, hZs, hEs, hfirst, hfirstinv, hfirstval⟩
  · intro y hy
    rw [hleftimage]
    exact hplane y hy
  · rw [hAs, hKs, himage]
  · intro p hp hpball hpzero O hO hpO
    exact hcross p hp hpball hpzero (O ∩ ball 0 ρ) (hO.inter isOpen_ball) ⟨hpO, hpball⟩

end Geometry.OriginalPLTower
