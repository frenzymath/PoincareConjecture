import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Simplicial.LocalDiskEdgeCofaces
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Simplicial.TransverseEdgeFaceGerm
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.VerticalTrianglePairCrossing
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.TwoCofaceCarrierGerm
import Mathlib.LinearAlgebra.Dual.Lemmas










set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

local notation "V3" => (Fin 3 → ℝ)
local notation "V2" => (ℝ × ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)

private theorem signed_edge_endpoints
    (K : SimplicialComplex ℝ V3) {s : Finset V3} (hs : s ∈ K.faces)
    (hs2 : s.card = 2) (A : V3 →ᵃ[ℝ] ℝ) {p : V3}
    (hp : p ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set V3)))
    (hpzero : A p = 0) (hne : ∃ v ∈ s, A v ≠ 0) :
    ∃ u v : V3, u ≠ v ∧ s = {u, v} ∧ A u < 0 ∧ 0 < A v := by
  classical
  obtain ⟨u, v, huv, hsuv⟩ := Finset.card_eq_two.mp hs2
  obtain ⟨w, hw, hsum, hval⟩ := (K.indep hs).exists_positive_weights_of_mem_intrinsicInterior hp
  have hwu := hw u (hsuv.symm ▸ Finset.mem_insert_self _ _)
  have hwv := hw v (hsuv.symm ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have hsum' : w u + w v = 1 := by simpa only [hsuv, Finset.sum_pair huv] using hsum
  have hline : AffineMap.lineMap u v (w v) = p := by
    rw [AffineMap.lineMap_apply_module, show 1 - w v = w u by linarith]
    simpa only [hsuv, Finset.sum_pair huv] using hval
  have hbalance : w u * A u + w v * A v = 0 := by
    have h := congrArg A hline
    rw [A.apply_lineMap, AffineMap.lineMap_apply_module,
      show 1 - w v = w u by linarith, hpzero] at h
    simpa only [smul_eq_mul] using h
  have hn : A u ≠ 0 ∨ A v ≠ 0 := by
    obtain ⟨z, hz, hzero⟩ := hne
    simp only [hsuv, Finset.mem_insert, Finset.mem_singleton] at hz
    exact hz.elim (fun h => Or.inl (h ▸ hzero)) (fun h => Or.inr (h ▸ hzero))
  by_cases hu : A u < 0
  · have hv : 0 < A v := by
      by_contra h
      have := mul_nonpos_of_nonneg_of_nonpos hwv.le (le_of_not_gt h)
      have := mul_neg_of_pos_of_neg hwu hu
      linarith
    exact ⟨u, v, huv, hsuv, hu, hv⟩
  · have hv : A v < 0 := by
      by_contra h
      have hu0 := le_of_not_gt hu
      have hv0 := le_of_not_gt h
      rcases hn with hn | hn
      · have := mul_pos hwu (lt_of_le_of_ne hu0 (Ne.symm hn))
        have := mul_nonneg hwv.le hv0
        linarith
      · have := mul_pos hwv (lt_of_le_of_ne hv0 (Ne.symm hn))
        have := mul_nonneg hwu.le hu0
        linarith
    have hu' : 0 < A u := by
      by_contra h
      have := mul_nonpos_of_nonneg_of_nonpos hwu.le (le_of_not_gt h)
      have := mul_neg_of_pos_of_neg hwv hv
      linarith
    exact ⟨v, u, huv.symm, hsuv.trans (Finset.pair_comm _ _), hv, hu'⟩

private theorem affine_height_edge_coordinates
    (A : V3 →ᵃ[ℝ] ℝ) {u v p : V3} (hu : A u < 0) (hv : 0 < A v)
    (hp : p ∈ segment ℝ u v) (hpzero : A p = 0) :
    ∃ F : C3 ≃ᴬ[ℝ] V3, F 0 = p ∧
      (∀ z, A (F z) = z.2) ∧ F.symm u = ((0, 0), A u) ∧
      F.symm v = ((0, 0), A v) := by
  let ell : V3 →ₗ[ℝ] ℝ := A.linear
  have hgap : A v - A u ≠ 0 := (sub_pos.mpr (hu.trans hv)).ne'
  let d : V3 := (A v - A u)⁻¹ • (v - u)
  have hd : ell d = 1 := by
    change A.linear ((A v - A u)⁻¹ • (v - u)) = 1
    have hsub : A.linear (v - u) = A v - A u := A.linearMap_vsub v u
    rw [map_smul, hsub]
    exact inv_mul_cancel₀ hgap
  have hell : ell ≠ 0 := by
    intro h
    have h0 : ell d = 0 := by rw [h]; rfl
    linarith
  have hker : Module.finrank ℝ ell.ker = 2 := by
    have h := Module.Dual.finrank_ker_add_one_of_ne_zero hell
    have hdim : Module.finrank ℝ V3 = 3 := by simp
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
  let B := (LinearEquiv.ofBijective L ⟨hi, hsurj⟩).toContinuousLinearEquiv
  let F := B.toLinearEquiv.toAffineEquiv.toContinuousAffineEquiv.trans
    (ContinuousAffineEquiv.constVAdd ℝ V3 p)
  have hF (z : C3) : F z = L z + p := add_comm _ _
  have hFp : F 0 = p := by rw [hF, map_zero, zero_add]
  have hFpheight (z : C3) : A (F z) = z.2 := by
    rw [hF]
    change A (L z +ᵥ p) = z.2
    rw [A.map_vadd, hpzero]
    exact (add_zero _).trans (hheight z)
  obtain ⟨t, _ht, htp⟩ := (segment_eq_image_lineMap ℝ u v).subset hp
  have hvalue : u + t • (v - u) = p := by
    rw [AffineMap.lineMap_apply_module] at htp
    calc
      u + t • (v - u) = (1 - t) • u + t • v := by module
      _ = p := htp
  have htvalue : t * (A v - A u) = -A u := by
    have h := congrArg A htp
    rw [A.apply_lineMap, AffineMap.lineMap_apply_module, hpzero] at h
    simp only [smul_eq_mul] at h
    nlinarith
  have htdiv : t = -A u * (A v - A u)⁻¹ := by
    rw [← div_eq_mul_inv]
    exact (eq_div_iff hgap).mpr htvalue
  have haxis (r : ℝ) : F ((0, 0), r) = r • d + p := by
    rw [hF, hL]
    change (e (0 : V2) : V3) + r • d + p = r • d + p
    rw [map_zero]
    change (0 : V3) + r • d + p = r • d + p
    rw [zero_add]
  have haxisu : F ((0, 0), A u) = u := by
    rw [haxis, ← hvalue, htdiv]
    dsimp only [d]
    module
  have haxisv : F ((0, 0), A v) = v := by
    calc
      F ((0, 0), A v) = F ((0, 0), A u) + (A v - A u) • d := by
        rw [haxis, haxis]
        module
      _ = u + (v - u) := by
        rw [haxisu]
        dsimp only [d]
        rw [smul_smul, mul_inv_cancel₀ hgap, one_smul]
      _ = v := by abel
  exact ⟨F, hFp, hFpheight,
    (congrArg F.symm haxisu).symm.trans (F.symm_apply_apply _),
    (congrArg F.symm haxisv).symm.trans (F.symm_apply_apply _)⟩





theorem exists_transverse_edge_crossing_chart_of_local_disk
    (K : SimplicialComplex ℝ V3) (hK : K.faces.Finite)
    (hbound : ∀ a ∈ K.faces, a.card ≤ 3)
    {s : Finset V3} (hs : s ∈ K.faces) (hs2 : s.card = 2)
    (A : V3 →ᵃ[ℝ] ℝ) {p : V3}
    (hp : p ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set V3)))
    (hpzero : A p = 0) (hne : ∃ v ∈ s, A v ≠ 0)
    {d rim : Set V3} (hd : IsFinitePLBallPair (Fin 2 → ℝ) d rim)
    (hdK : d ⊆ K.space) (hpd : p ∈ d \ rim)
    (hopen : IsOpen ((Subtype.val : K.space → V3) ⁻¹' (d \ rim)))
    {O : Set V3} (hO : IsOpen O) (hpO : p ∈ O) :
    ∃ H : OpenPartialHomeomorph V3 C3,
      p ∈ H.source ∧ H.source ⊆ O ∧ H p = 0 ∧
      LocallyPiecewiseAffineOn H H.source ∧
      LocallyPiecewiseAffineOn H.symm H.target ∧
      (∀ x ∈ H.source, x ∈ K.space ↔ (H x).1.1 = 0) ∧
      ∀ x ∈ H.source, A x = (H x).2 := by
  classical
  obtain ⟨u, v, _huv, hsuv, hu, hv⟩ :=
    signed_edge_endpoints K hs hs2 A hp hpzero hne
  have hpseg : p ∈ segment ℝ u v := by
    simpa only [hsuv, Finset.coe_pair, convexHull_pair] using intrinsicInterior_subset hp
  obtain ⟨a, b, hab, hset⟩ := ncard_eq_two.mp
    (K.ncard_triangle_cofaces_eq_two_of_local_disk hK hbound hs hs2 hp hd hdK hpd hopen)
  have ha : a ∈ K.faces ∧ a.card = 3 ∧ s ⊆ a := by
    change a ∈ {t | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}
    rw [hset]
    exact Or.inl rfl
  have hb : b ∈ K.faces ∧ b.card = 3 ∧ s ⊆ b := by
    change b ∈ {t | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}
    rw [hset]
    exact Or.inr rfl
  have hcofaces (t : Finset V3) (ht : t ∈ K.faces) (hst : s ⊆ t) : t ⊆ a ∨ t ⊆ b := by
    have hlo := Finset.card_le_card hst
    have hhi := hbound t ht
    by_cases ht2 : t.card = 2
    · have he : s = t := Finset.eq_of_subset_of_card_le hst (by omega)
      exact Or.inl (he ▸ ha.2.2)
    · have hmem : t ∈ {t | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t} := ⟨ht, by omega, hst⟩
      rw [hset] at hmem
      exact hmem.elim (fun h => Or.inl (h ▸ Finset.Subset.rfl))
        (fun h => Or.inr (h ▸ Finset.Subset.rfl))
  obtain ⟨U, hU, hpU, hKU⟩ :=
    K.exists_open_two_coface_carrier_germ hK hs ha.1 hb.1 hcofaces hp
  obtain ⟨F, hFzero, hFheight, hFu, hFv⟩ := affine_height_edge_coordinates A hu hv hpseg hpzero
  obtain ⟨w, hws, hwa⟩ := Finset.exists_eq_insert_iff.mpr ⟨ha.2.2, by have := ha.2.1; omega⟩
  obtain ⟨z, hzs, hzb⟩ := Finset.exists_eq_insert_iff.mpr ⟨hb.2.2, by have := hb.2.1; omega⟩
  have haxis (r : ℝ) : F ((0, 0), r) ∈ affineSpan ℝ (s : Set V3) := by
    rw [hsuv, Finset.coe_pair]
    apply mem_affineSpan_pair_iff_exists_lineMap_eq.mpr
    refine ⟨(r - A u) / (A v - A u), ?_⟩
    apply F.symm.injective
    have hline : F.symm (AffineMap.lineMap u v ((r - A u) / (A v - A u))) =
        AffineMap.lineMap (F.symm u) (F.symm v) ((r - A u) / (A v - A u)) :=
      F.symm.toAffineEquiv.apply_lineMap u v ((r - A u) / (A v - A u))
    rw [hline, hFu, hFv, F.symm_apply_apply]
    have hgap : A v - A u ≠ 0 := (sub_pos.mpr (hu.trans hv)).ne'
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
  have hw := hnonzero ha.1 hws hwa
  have hz := hnonzero hb.1 hzs hzb
  have hFhull (S : Set V3) : F.symm '' convexHull ℝ S =
      convexHull ℝ (F.symm '' S) := F.symm.toAffineEquiv.toAffineMap.image_convexHull S
  have hcoord (r : V3) : F.symm '' convexHull ℝ (↑(insert r s) : Set V3) =
      convexHull ℝ ({((0, 0), A u), ((0, 0), A v), F.symm r} : Set C3) := by
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
      have he : a ∩ b = a := Finset.eq_of_subset_of_card_le Finset.inter_subset_left
        (by have := ha.2.1; omega)
      have hab' : a ⊆ b := he ▸ Finset.inter_subset_right
      exact hab (Finset.eq_of_subset_of_card_le hab' (by have := ha.2.1; have := hb.2.1; omega))
    exact (Finset.eq_of_subset_of_card_le (Finset.subset_inter ha.2.2 hb.2.2) (by omega)).symm
  have haxisHull : F.symm '' convexHull ℝ (s : Set V3) ⊆ {x : C3 | x.1 = 0} := by
    rw [hFhull]
    simp only [hsuv, Finset.coe_pair, image_insert_eq, image_singleton, hFu, hFv]
    apply convexHull_min
    · rintro x (rfl | rfl) <;> rfl
    · exact (convex_singleton (0 : V2)).linear_preimage (LinearMap.fst ℝ V2 ℝ)
  have hback {t : Finset V3} {x : C3}
      (hx : x ∈ F.symm '' convexHull ℝ (t : Set V3)) : F x ∈ convexHull ℝ (t : Set V3) := by
    obtain ⟨y, hy, rfl⟩ := hx
    simpa only [F.apply_symm_apply] using hy
  have hinter (x : C3)
      (hxa : x ∈ convexHull ℝ ({(0, A u), (0, A v), F.symm w} : Set C3))
      (hxb : x ∈ convexHull ℝ ({(0, A u), (0, A v), F.symm z} : Set C3)) : x.1 = 0 := by
    have hxA : F x ∈ convexHull ℝ (a : Set V3) := hwa ▸ hback ((hcoord w).symm.subset hxa)
    have hxB : F x ∈ convexHull ℝ (b : Set V3) := hzb ▸ hback ((hcoord z).symm.subset hxb)
    have hxS : F x ∈ convexHull ℝ (s : Set V3) := by
      rw [← habs, Finset.coe_inter, ← K.convexHull_inter_convexHull ha.1 hb.1]
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
      F.symm x ∈ convexHull ℝ ({((0, 0), A u), ((0, 0), A v), F.symm w} : Set C3) ∪
        convexHull ℝ ({((0, 0), A u), ((0, 0), A v), F.symm z} : Set C3)
    rw [← hcoord w, ← hcoord z, hwa, hzb]
    exact (or_congr (hmem a) (hmem b)).symm
  · intro x hx
    change A x = (T (F.symm x)).2
    rw [hTlast _ ((hsource x).mp hx)]
    simpa only [F.apply_symm_apply] using hFheight (F.symm x)

end Geometry.SimplicialComplex
