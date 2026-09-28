import PoincareConjecture.Proofs.M76.Dehn.OriginalDoubleArcSurgeryCrossings
import PoincareConjecture.Proofs.M76.Wall.Mathlib.TwoRayStraightening
import PoincareConjecture.Proofs.M76.Mathlib.PiecewiseAffineProd











set_option autoImplicit false

open Set Metric Geometry Geometry.SimplicialComplex Topology
open PoincareConjecture.M76.Dehn

namespace Geometry.OriginalPLTower

local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)

set_option maxHeartbeats 1600000 in


theorem exists_zero_edge_crossing_of_signed_cofaces
    (K : SimplicialComplex ℝ V3) (hK : K.faces.Finite)
    (edge : Finset V3) (heK : edge ∈ K.faces) (he2 : edge.card = 2)
    (ell : V3 →L[ℝ] ℝ) (hezero : ∀ x ∈ edge, ell x = 0)
    (a₁ b₁ : Finset V3) (u v : V3) (ha₁ : a₁ ∈ K.faces) (hb₁ : b₁ ∈ K.faces)
    (hau : insert u edge = a₁) (hbv : insert v edge = b₁)
    (hu : ell u < 0) (hv : 0 < ell v)
    (hexhaust : ∀ face ∈ K.faces, edge ⊆ face → face ⊆ a₁ ∨ face ⊆ b₁)
    (z : V3) (hzedge : z ∈ intrinsicInterior ℝ (convexHull ℝ (edge : Set V3)))
    (O : Set V3) (hO : IsOpen O) (hzO : z ∈ O) :
    ∃ T : OpenPartialHomeomorph V3 C3,
      z ∈ T.source ∧ T.source ⊆ O ∧ T z = 0 ∧
      LocallyPiecewiseAffineOn T T.source ∧
      (∀ x ∈ T.source, x ∈ K.space ↔ (T x).1.1 = 0) ∧
      ∀ x ∈ T.source, (T x).2 = ell x := by
  classical
  obtain ⟨V, hV, hzV, hgerm⟩ :=
    K.exists_open_two_coface_carrier_germ hK heK ha₁ hb₁ hexhaust hzedge
  have hz0 : ell z = 0 := by
    apply convexHull_min hezero
      ((convex_singleton (0 : ℝ)).linear_preimage ell.toLinearMap)
      (intrinsicInterior_subset hzedge)
  have huedge : u ∉ edge := fun h ↦ hu.ne (hezero u h)
  have ha3 : a₁.card = 3 := by
    rw [← hau, Finset.card_insert_of_notMem huedge, he2]
  have hzHull : z ∈ convexHull ℝ (a₁ : Set V3) :=
    convexHull_mono (by rw [← hau]; exact Finset.subset_insert _ _)
      (intrinsicInterior_subset hzedge)
  let plane := affineSpan ℝ (a₁ : Set V3)
  have hzplane : z ∈ plane := convexHull_subset_affineSpan (s :=
    (a₁ : Set V3)) hzHull
  have huplane : u ∈ plane := subset_affineSpan ℝ _
    (hau ▸ Finset.mem_insert_self _ _)
  have hA : ∃ x ∈ plane, ∃ y ∈ plane, ell x ≠ ell y := by
    refine ⟨u, huplane, z, hzplane, ?_⟩
    intro heq
    apply (ne_of_lt hu)
    exact heq.trans hz0
  obtain ⟨F, hFzero, hFell', hFplane⟩ := plane.exists_centered_height_plane_coordinates
    (by simp) (K.finrank_faceDirection_of_card ha₁ ha3) ell.toLinearMap.toAffineMap
    hA hzplane
  have hFell (x : C3) : ell (F x) = x.1.1 := by
    have h := hFell' x
    change ell (F x) = ell z + x.1.1 at h
    simpa only [hz0, zero_add] using h
  let swap : C3 ≃ₗ[ℝ] C3 :=
    { toFun := fun x ↦ ((x.1.1, x.2), x.1.2)
      invFun := fun x ↦ ((x.1.1, x.2), x.1.2)
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  let A := F.symm.trans swap.toAffineEquiv.toContinuousAffineEquiv
  have hAzero : A z = 0 := by
    change swap (F.symm z) = 0
    rw [← hFzero, F.symm_apply_apply, map_zero]
  have hAz : (A z).2 = 0 := congrArg Prod.snd hAzero
  have hAell (x : V3) : (A x).1.1 = ell x := by
    change (F.symm x).1.1 = ell x
    simpa only [F.apply_symm_apply] using (hFell (F.symm x)).symm
  have hAedge (x : V3) (hx : x ∈ edge) : (A x).1 = 0 := by
    apply Prod.ext
    · exact (hAell x).trans (hezero x hx)
    · change (F.symm x).2 = 0
      apply (hFplane _).mp
      rw [F.apply_symm_apply]
      apply subset_affineSpan ℝ _
      rw [← hau]
      exact Finset.mem_insert_of_mem hx
  obtain ⟨r₀, s₀, hrs, hepair⟩ := Finset.card_eq_two.mp he2
  have hr₀ : r₀ ∈ edge := hepair.symm ▸ Finset.mem_insert_self _ _
  have hs₀ : s₀ ∈ edge := hepair.symm ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hAr : A r₀ = (0, (A r₀).2) := Prod.ext (hAedge r₀ hr₀) rfl
  have hAs : A s₀ = (0, (A s₀).2) := Prod.ext (hAedge s₀ hs₀) rfl
  obtain ⟨wt, hwt, hsum, hval⟩ := (K.indep heK).exists_positive_weights_of_mem_intrinsicInterior
    hzedge
  have hmap := Finset.map_affineCombination (s := edge) id wt hsum A.toAffineEquiv.toAffineMap
  simp only [Finset.affineCombination_eq_linear_combination _ _ _ hsum,
    id_eq, Function.comp_apply] at hmap
  rw [hval] at hmap
  change A z = ∑ x ∈ edge, wt x • A x at hmap
  have hbalance : wt r₀ * (A r₀).2 + wt s₀ * (A s₀).2 = 0 := by
    have h := congrArg Prod.snd hmap.symm
    rw [hepair, Finset.sum_pair hrs] at h
    change wt r₀ * (A r₀).2 + wt s₀ * (A s₀).2 = (A z).2 at h
    exact h.trans hAz
  have hwr := hwt r₀ hr₀
  have hws := hwt s₀ hs₀
  have hparameters : (A r₀).2 ≠ (A s₀).2 := fun h ↦
    hrs (A.injective (hAr.trans ((congrArg (fun d : ℝ ↦ ((0 : ℝ × ℝ), d)) h).trans hAs.symm)))
  have hrnonzero : (A r₀).2 ≠ 0 := by
    intro hr0
    have hs0 : (A s₀).2 = 0 := by
      have hprod : wt s₀ * (A s₀).2 = 0 := by simpa only [hr0, mul_zero, zero_add] using hbalance
      exact (mul_eq_zero.mp hprod).resolve_left hws.ne'
    exact hparameters (hr0.trans hs0.symm)
  obtain ⟨r₁, s₁, hr₁, hs₁, hAr₁, hAs₁, hepair'⟩ :
      ∃ r₁ s₁ : V3, (A r₁).2 < 0 ∧ 0 < (A s₁).2 ∧
        A r₁ = (0, (A r₁).2) ∧ A s₁ = (0, (A s₁).2) ∧ edge = {r₁, s₁} := by
    rcases lt_or_gt_of_ne hrnonzero with hr | hr
    · have hs : 0 < (A s₀).2 := by
        by_contra hn
        have h₁ := mul_neg_of_pos_of_neg hwr hr
        have h₂ := mul_nonpos_of_nonneg_of_nonpos hws.le (not_lt.mp hn)
        linarith
      exact ⟨r₀, s₀, hr, hs, hAr, hAs, hepair⟩
    · have hs : (A s₀).2 < 0 := by
        by_contra hn
        have h₁ := mul_pos hwr hr
        have h₂ := mul_nonneg hws.le (not_lt.mp hn)
        linarith
      exact ⟨s₀, r₀, hs, hr, hAs, hAr, hepair.trans (Finset.pair_comm _ _)⟩
  let u' := (A (u)).1
  let v' := (A (v)).1
  let hgt := ContinuousLinearMap.fst ℝ ℝ ℝ
  have hu' : hgt u' < 0 := by change (A (u)).1.1 < 0; rw [hAell]; exact hu
  have hv' : 0 < hgt v' := by change 0 < (A (v)).1.1; rw [hAell]; exact hv
  have hu'0 : u' ≠ 0 := fun h ↦ hu'.ne (by rw [h, map_zero])
  have hv'0 : v' ≠ 0 := fun h ↦ hv'.ne' (by rw [h, map_zero])
  obtain ⟨Nu, hNu, h0Nu, htriU⟩ := exists_open_vertical_triangle_germ hu'0 hr₁ hs₁
    (A (u)).2
  obtain ⟨Nv, hNv, h0Nv, htriV⟩ := exists_open_vertical_triangle_germ hv'0 hr₁ hs₁
    (A (v)).2
  have hcoord (d : V3) (face : Finset V3)
      (hface : insert d edge = face) :
      A '' convexHull ℝ (face : Set V3) =
        convexHull ℝ ({(0, (A r₁).2), (0, (A s₁).2), A d} : Set C3) := by
    change A.toAffineEquiv.toAffineMap '' convexHull ℝ (face : Set V3) = _
    rw [A.toAffineEquiv.toAffineMap.image_convexHull]
    change convexHull ℝ (A '' (face : Set V3)) = _
    rw [← hface, hepair']
    simp only [Finset.coe_insert, Finset.coe_singleton]
    rw [Set.image_insert_eq, Set.image_pair, hAr₁, hAs₁]
    dsimp only
    congr 1
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  obtain ⟨axis, haxis, shear, hshear, hshear0, hheight, hnegativeRay, hpositiveRay⟩ :=
    hgt.exists_two_ray_straightening u' v' hu' hv'
  have hwholeRay (x : ℝ × ℝ) :
      ((∃ t : ℝ, 0 ≤ t ∧ x = t • u') ∨ (∃ t : ℝ, 0 ≤ t ∧ x = t • v')) ↔
        (shear x).2 - axis.2 * (shear x).1 = 0 := by
    have haxis₁ : axis.1 = 1 := haxis
    have hline (y : ℝ × ℝ) : (∃ t : ℝ, y = t • axis) ↔ y.2 - axis.2 * y.1 = 0 := by
      constructor
      · rintro ⟨t, rfl⟩
        change t * axis.2 - axis.2 * (t * axis.1) = 0
        rw [haxis₁]
        ring
      · intro h
        refine ⟨y.1, Prod.ext ?_ ?_⟩
        · change y.1 = y.1 * axis.1
          rw [haxis₁, mul_one]
        · change y.2 = y.1 * axis.2
          linarith
    rw [← hline]
    constructor
    · rintro (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
      · exact ⟨t * hgt u', hnegativeRay t ht⟩
      · exact ⟨t * hgt v', hpositiveRay t ht⟩
    · rintro ⟨t, ht⟩
      by_cases ht0 : 0 ≤ t
      · have hquot := div_nonneg ht0 hv'.le
        refine Or.inr ⟨t / hgt v', hquot, shear.injective ?_⟩
        rw [ht, hpositiveRay _ hquot, div_mul_cancel₀ _ hv'.ne']
      · have hquot := div_nonneg_of_nonpos (lt_of_not_ge ht0).le hu'.le
        refine Or.inl ⟨t / hgt u', hquot, shear.injective ?_⟩
        rw [ht, hnegativeRay _ hquot, div_mul_cancel₀ _ hu'.ne]
  let product := shear.prodCongr (Homeomorph.refl ℝ)
  have hproduct : product.toOpenPartialHomeomorph ∈ piecewiseAffineGroupoid C3 := by
    have hs : LocallyPiecewiseAffineOn shear univ ∧
        LocallyPiecewiseAffineOn shear.symm univ := hshear
    have hid : LocallyPiecewiseAffineOn (id : ℝ → ℝ) univ :=
      locallyPiecewiseAffineOn_affine (ContinuousAffineMap.id ℝ ℝ) isOpen_univ
    constructor
    · change LocallyPiecewiseAffineOn (Prod.map shear id) univ
      simpa only [univ_prod_univ] using hs.1.prodMap hid
    · change LocallyPiecewiseAffineOn (Prod.map shear.symm id) univ
      simpa only [univ_prod_univ] using hs.2.prodMap hid
  let normalize : C3 ≃ₗ[ℝ] C3 :=
    { toFun := fun x ↦ ((x.1.2 - axis.2 * x.1.1, x.2), x.1.1)
      invFun := fun x ↦ ((x.2, x.1.1 + axis.2 * x.2), x.1.2)
      left_inv := by
        intro x
        ext
        all_goals dsimp
        all_goals ring
      right_inv := by
        intro x
        ext
        all_goals dsimp
        all_goals ring
      map_add' := by
        intro x y
        ext
        all_goals dsimp
        all_goals ring
      map_smul' := by
        intro r x
        ext
        all_goals dsimp
        all_goals ring }
  let B := normalize.toAffineEquiv.toContinuousAffineEquiv
  let Fglobal := (A.toHomeomorph.trans product).trans B.toHomeomorph
  have hglobal (x : V3) :
      Fglobal x = (( (shear (A x).1).2 - axis.2 * (shear (A x).1).1,
        (A x).2), (shear (A x).1).1) := rfl
  have hglobal0 : Fglobal z = 0 := by
    rw [hglobal, hAzero]
    change (((shear (0 : ℝ × ℝ)).2 - axis.2 * (shear 0).1, 0), (shear 0).1) = 0
    rw [hshear0]
    change ((0 - axis.2 * 0, (0 : ℝ)), (0 : ℝ)) = ((0, 0), 0)
    simp
  have hglobalHeight (x : V3) : (Fglobal x).2 = ell x :=
    (hheight (A x).1).trans (hAell x)
  have hglobalPL : LocallyPiecewiseAffineOn Fglobal univ := by
    have h := (locallyPiecewiseAffineOn_affine B.toContinuousAffineMap isOpen_univ).comp
      (hproduct.1.comp (locallyPiecewiseAffineOn_affine A.toContinuousAffineMap isOpen_univ))
    change LocallyPiecewiseAffineOn (B ∘ product ∘ A)
      ((univ ∩ A ⁻¹' univ) ∩ (product ∘ A) ⁻¹' univ) at h
    change LocallyPiecewiseAffineOn (B ∘ product ∘ A) univ
    simpa only [preimage_univ, inter_univ] using h
  let Tsource := O ∩ (V ∩ A ⁻¹' (Nu ∩ Nv))
  have hTsource : IsOpen Tsource :=
    hO.inter (hV.inter ((hNu.inter hNv).preimage A.continuous))
  have hzTsource : z ∈ Tsource :=
    ⟨hzO, hzV, by change A z ∈ Nu ∩ Nv; rw [hAzero]; exact ⟨h0Nu, h0Nv⟩⟩
  let T := Fglobal.toOpenPartialHomeomorphOfImageEq Tsource hTsource
    (Fglobal '' Tsource) rfl
  refine ⟨T, hzTsource, fun _ hx ↦ hx.1, hglobal0,
    hglobalPL.mono T.open_source (subset_univ _), ?_, fun x _ ↦ hglobalHeight x⟩
  intro x hx
  change x ∈ K.space ↔ (Fglobal x).1.1 = 0
  rw [hgerm x hx.2.1, hglobal]
  have htriangle (face : Finset V3) :
      A x ∈ A '' convexHull ℝ (face : Set V3) ↔
        x ∈ convexHull ℝ (face : Set V3) := A.injective.mem_set_image
  rw [Set.mem_union, ← htriangle a₁, ← htriangle b₁,
    hcoord u a₁ hau, hcoord v b₁ hbv]
  have hucoord : A u = (u', (A u).2) := rfl
  have hvcoord : A v = (v', (A v).2) := rfl
  rw [hucoord, hvcoord, htriU _ hx.2.2.1, htriV _ hx.2.2.2]
  exact hwholeRay (A x).1

set_option maxHeartbeats 800000 in


theorem exists_signed_zero_edge_cofaces
    (K : SimplicialComplex ℝ V3) (hK : K.faces.Finite)
    (q : V3 → ℝ × ℝ) (hq : K.AffineOnFaces q) (hi : InjOn q K.space)
    (edge : Finset V3) (heK : edge ∈ K.faces) (he2 : edge.card = 2)
    (ell : V3 →L[ℝ] ℝ) (hezero : ∀ x ∈ edge, ell x = 0)
    (z : V3) (hzedge : z ∈ intrinsicInterior ℝ (convexHull ℝ (edge : Set V3)))
    (hint : q z ∈ interior (q '' K.space))
    (hpositive : z ∈ closure (K.space ∩ {x | 0 < ell x}))
    (hnegative : z ∈ closure (K.space ∩ {x | ell x < 0})) :
    ∃ u v : V3, insert u edge ∈ K.faces ∧ insert v edge ∈ K.faces ∧
      ell u < 0 ∧ 0 < ell v ∧
      ∀ face ∈ K.faces, edge ⊆ face →
        face ⊆ insert u edge ∨ face ⊆ insert v edge := by
  classical
  let Kq := hq.embeddedImage hi
  have hKq : Kq.faces.Finite := hq.embeddedImage_finite hi hK
  have heq : edge.image q ∈ Kq.faces :=
    (hq.image_mem_embeddedImage_iff hi (K.subset_space heK)).mpr heK
  have heqcard : (edge.image q).card = Module.finrank ℝ (ℝ × ℝ) := by
    rw [Finset.card_image_iff.mpr (hi.mono (K.subset_space heK)), he2]
    simp [Module.finrank_prod]
  have hzq : q z ∈ convexHull ℝ (edge.image q : Set (ℝ × ℝ)) := by
    rw [Finset.coe_image, ← hq.image_convexHull heK]
    exact mem_image_of_mem q (intrinsicInterior_subset hzedge)
  have hzqint : q z ∈ interior Kq.space := by
    rw [hq.embeddedImage_space hi]
    exact hint
  have hcount := Kq.faceLink_ncard_eq_two_of_hull_meets_interior hKq heq heqcard
    ⟨q z, hzq, hzqint⟩
  rw [hq.ncard_embeddedImage_faceLink hi heK,
    K.ncard_faceLink_vertices_eq_cofaces, he2] at hcount
  obtain ⟨a₀, b₀, _hab₀, hset⟩ := ncard_eq_two.mp hcount
  have ha₀ : a₀ ∈ K.faces ∧ a₀.card = 3 ∧ edge ⊆ a₀ := by
    change a₀ ∈ {face | face ∈ K.faces ∧ face.card = 3 ∧ edge ⊆ face}
    rw [hset]
    exact Or.inl rfl
  have hb₀ : b₀ ∈ K.faces ∧ b₀.card = 3 ∧ edge ⊆ b₀ := by
    change b₀ ∈ {face | face ∈ K.faces ∧ face.card = 3 ∧ edge ⊆ face}
    rw [hset]
    exact Or.inr rfl
  have hexhaust (face : Finset V3) (hf : face ∈ K.faces) (hef : edge ⊆ face) :
      face ⊆ a₀ ∨ face ⊆ b₀ := by
    have hhi : face.card ≤ 3 := by
      simpa [Module.finrank_prod] using hq.face_card_le_of_injOn hi hf
    have hlo := Finset.card_le_card hef
    by_cases htwo : face.card = 2
    · have he : edge = face := Finset.eq_of_subset_of_card_le hef (by omega)
      exact Or.inl (he ▸ ha₀.2.2)
    · have hmem : face ∈ {f | f ∈ K.faces ∧ f.card = 3 ∧ edge ⊆ f} :=
        ⟨hf, by omega, hef⟩
      rw [hset] at hmem
      exact hmem.elim (fun h ↦ Or.inl (h ▸ Finset.Subset.rfl))
        (fun h ↦ Or.inr (h ▸ Finset.Subset.rfl))
  obtain ⟨V, hV, hzV, hgerm⟩ := K.exists_open_two_coface_carrier_germ hK
    heK ha₀.1 hb₀.1 hexhaust hzedge
  obtain ⟨u₀, _hu₀, hua⟩ := Finset.exists_eq_insert_iff.mpr ⟨ha₀.2.2, by omega⟩
  obtain ⟨v₀, _hv₀, hvb⟩ := Finset.exists_eq_insert_iff.mpr ⟨hb₀.2.2, by omega⟩
  have signed (L : V3 →L[ℝ] ℝ) (heL : ∀ x ∈ edge, L x = 0)
      (hcl : z ∈ closure (K.space ∩ {x | 0 < L x})) :
      0 < L u₀ ∨ 0 < L v₀ := by
    by_contra hn
    have hu : L u₀ ≤ 0 := not_lt.mp (fun h ↦ hn (Or.inl h))
    have hv : L v₀ ≤ 0 := not_lt.mp (fun h ↦ hn (Or.inr h))
    obtain ⟨x, hxV, hxK, hxpos⟩ := _root_.mem_closure_iff.mp hcl V hV hzV
    have half (u : V3) (hu : L u ≤ 0) :
        convexHull ℝ ((insert u edge : Finset V3) : Set V3) ⊆ {x | L x ≤ 0} := by
      apply convexHull_min ?_ ((convex_Iic (0 : ℝ)).linear_preimage L.toLinearMap)
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hu
      · exact (heL x hx).le
    rcases (hgerm x hxV).mp hxK with hx | hx
    · have hle : L x ≤ 0 := half u₀ hu (hua.symm ▸ hx)
      exact (not_lt_of_ge hle) hxpos
    · have hle : L x ≤ 0 := half v₀ hv (hvb.symm ▸ hx)
      exact (not_lt_of_ge hle) hxpos
  have hpos := signed ell hezero hpositive
  have hneg : ell u₀ < 0 ∨ ell v₀ < 0 := by
    have hzeroNeg : ∀ x ∈ edge, (-ell) x = 0 := by
      intro x hx
      change -(ell x) = 0
      rw [hezero x hx, neg_zero]
    have hnegcl : z ∈ closure (K.space ∩ {x | (-ell) x > 0}) := by
      simpa only [neg_apply, neg_pos] using hnegative
    have h := signed (-ell) hzeroNeg hnegcl
    simpa only [neg_apply, neg_pos] using h
  rcases hneg with hu | hv
  · refine ⟨u₀, v₀, hua.symm ▸ ha₀.1, hvb.symm ▸ hb₀.1, hu,
      hpos.resolve_left hu.not_gt, ?_⟩
    intro face hf hef
    simpa only [hua, hvb] using hexhaust face hf hef
  · refine ⟨v₀, u₀, hvb.symm ▸ hb₀.1, hua.symm ▸ ha₀.1, hv,
      hpos.resolve_right hv.not_gt, ?_⟩
    intro face hf hef
    simpa only [hua, hvb] using (hexhaust face hf hef).symm


set_option maxHeartbeats 800000 in
open Classical in



theorem exists_moved_zero_edge_crossing
    (K N : SimplicialComplex ℝ V3) (hK : K.faces.Finite)
    (H : V3 → V3) (hH : K.AffineOnFaces H) (hHi : Function.Injective H)
    (hN : N = hH.embeddedImage hHi.injOn)
    (q : V3 → ℝ × ℝ) (hq : K.AffineOnFaces q) (hi : InjOn q K.space)
    (edge : Finset V3) (heK : edge ∈ K.faces) (he2 : edge.card = 2)
    (ell : V3 →L[ℝ] ℝ) (hezero : ∀ x ∈ edge, ell x = 0)
    (henew : ∀ x ∈ edge, ell (H x) = 0)
    (z : V3) (hzedge : z ∈ intrinsicInterior ℝ (convexHull ℝ (edge : Set V3)))
    (hint : q z ∈ interior (q '' K.space))
    (hpositive : z ∈ closure (K.space ∩ {x | 0 < ell x}))
    (hnegative : z ∈ closure (K.space ∩ {x | ell x < 0}))
    (hsigns : ∀ x ∈ K.vertices, ell x ≠ 0 →
      (0 < ell (H x) ↔ 0 < ell x) ∧ (ell (H x) < 0 ↔ ell x < 0))
    (p : V3)
    (hp : p ∈ intrinsicInterior ℝ (convexHull ℝ (edge.image H : Set V3)))
    (O : Set V3) (hO : IsOpen O) (hpO : p ∈ O) :
    ∃ T : OpenPartialHomeomorph V3 C3,
      p ∈ T.source ∧ T.source ⊆ O ∧ T p = 0 ∧
      LocallyPiecewiseAffineOn T T.source ∧
      (∀ x ∈ T.source, x ∈ N.space ↔ (T x).1.1 = 0) ∧
      ∀ x ∈ T.source, (T x).2 = ell x := by
  classical
  subst N
  let N := hH.embeddedImage hHi.injOn
  obtain ⟨u, v, huK, hvK, hu, hv, hexhaust⟩ :=
    exists_signed_zero_edge_cofaces K hK q hq hi edge heK he2 ell hezero z
      hzedge hint hpositive hnegative
  have hNfinite : N.faces.Finite := hH.embeddedImage_finite hHi.injOn hK
  have heN : edge.image H ∈ N.faces :=
    (hH.image_mem_embeddedImage_iff hHi.injOn (K.subset_space heK)).mpr heK
  have heN2 : (edge.image H).card = 2 := by
    rw [Finset.card_image_iff.mpr hHi.injOn, he2]
  have haN : insert (H u) (edge.image H) ∈ N.faces := by
    simpa only [Finset.image_insert] using
      (hH.image_mem_embeddedImage_iff hHi.injOn (K.subset_space huK)).mpr huK
  have hbN : insert (H v) (edge.image H) ∈ N.faces := by
    simpa only [Finset.image_insert] using
      (hH.image_mem_embeddedImage_iff hHi.injOn (K.subset_space hvK)).mpr hvK
  have huN : ell (H u) < 0 :=
    ((hsigns u (K.face_subset_vertices huK (Finset.mem_insert_self _ _)) hu.ne).2).mpr hu
  have hvN : 0 < ell (H v) :=
    ((hsigns v (K.face_subset_vertices hvK (Finset.mem_insert_self _ _)) hv.ne').1).mpr hv
  have hnewzero : ∀ x ∈ edge.image H, ell x = 0 := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact henew y hy
  have hnewcofaces (face : Finset V3) (hf : face ∈ N.faces)
      (hef : edge.image H ⊆ face) :
      face ⊆ insert (H u) (edge.image H) ∨ face ⊆ insert (H v) (edge.image H) := by
    obtain ⟨oldFace, holdFace, heold, _hcard, rfl⟩ :=
      hH.pullback_embeddedImage_coface hHi.injOn heK hf hef rfl
    rcases hexhaust oldFace holdFace heold with h | h
    · exact Or.inl (by
        simpa only [Finset.image_insert] using Finset.image_subset_image h)
    · exact Or.inr (by
        simpa only [Finset.image_insert] using Finset.image_subset_image h)
  exact exists_zero_edge_crossing_of_signed_cofaces N hNfinite (edge.image H) heN heN2
    ell hnewzero (insert (H u) (edge.image H)) (insert (H v) (edge.image H))
    (H u) (H v) haN hbN rfl rfl huN hvN hnewcofaces p hp O hO hpO


end Geometry.OriginalPLTower
