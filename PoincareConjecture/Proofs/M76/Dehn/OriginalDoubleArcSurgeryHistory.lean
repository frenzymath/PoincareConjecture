import PoincareConjecture.Proofs.M76.Dehn.OriginalDoubleArcSurgeryAssembly
import PoincareConjecture.Proofs.M76.Dehn.OriginalFiniteExceptionalPairs
import PoincareConjecture.Proofs.M76.Dehn.OriginalIntersectionRankBounds
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.TriangleInteriorCrossingChart













set_option autoImplicit false

open Set Geometry

namespace Geometry.OriginalPLTower

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "C2" => (ℝ × ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)

variable {M ι : Type*} [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M V3} {S : SimplicialComplex ℝ V2}
  {f : V2 → M} {r : M → ℝ} {C : Set M}

set_option maxHeartbeats 800000 in






theorem Step.exists_history_original_crossed_pair
    {s t : Stage e S f r C} (step : Step s t)
    {K : SimplicialComplex ℝ V2} (hK : K.faces.Finite)
    (Rim : SimplicialComplex ℝ V2) (hRim : Rim.space = Metric.sphere (0 : V2) 1)
    {n : ℕ} (order : Fin n → K.faces) (horder : Function.Bijective order)
    (hbefore : ∀ i k, (order k).val ⊂ (order i).val → k < i)
    (P : ℕ → SimplicialComplex ℝ V2)
    (hP : ∀ k, P k ≤ K ∧
      (P k).faces = {a | ∃ i : Fin n, i.val < k ∧ (order i).val = a})
    (hsucc : ∀ i : Fin n, (P (i.val + 1)).space = (P i.val).space ∪
      convexHull ℝ ((order i).val : Set V2))
    (boundary : Fin n → Bool)
    (hboundary : ∀ i, boundary i = true ↔ (order i).val ∈ Rim.faces)
    (Q : Fin n → OpenPartialHomeomorph t.Carrier V3)
    (B : Fin n → OpenPartialHomeomorph s.Carrier V3)
    (J : Fin n → SimplicialComplex ℝ V3)
    (hQ : ∀ i k, (t.charts k).symm.trans (Q i) ∈ piecewiseAffineGroupoid V3)
    (hB : ∀ i k, (s.charts k).symm.trans (B i) ∈ piecewiseAffineGroupoid V3)
    (hval : ∀ i z, Q i z = B i (step.projection (step.inclusion z)))
    (hmaps : ∀ i, MapsTo (step.projection ∘ step.inclusion) (Q i).source (B i).source)
    (U : K.faces → Set t.Carrier) (hUQ : ∀ i, U (order i) ⊆ (Q i).source)
    {R Fmark : Set M} (states : ℕ → FaceDiskState t K U R Fmark)
    (motions : ∀ i : Fin n,
      FaceMotionData step K (P i.val) (P (i.val + 1)) (states i.val).map
        (Q i) (B i) (J i) U R Fmark (boundary i))
    (htransitions : ∀ i : Fin n,
      (states (i.val + 1)).map = (motions i).ambient 1 ∘ (states i.val).map)
    (hstable : ∀ i k, i ≤ k → k ≤ n →
      EqOn (states k).map (states i).map (P i).space)
    (hcell : ∀ a : K.faces, InjOn ((step.projection ∘ step.inclusion) ∘ (states n).map)
      (convexHull ℝ (a.val : Set V2)))
    {x y : V2} (hx : x ∈ K.space) (hy : y ∈ K.space) (hne : x ≠ y)
    (hxy : step.projection (step.inclusion ((states n).map x)) =
      step.projection (step.inclusion ((states n).map y)))
    (hoff : ∀ a ∈ K.faces, a.card ≤ 2 →
      x ∉ convexHull ℝ (a : Set V2) ∧ y ∉ convexHull ℝ (a : Set V2)) :
    ∃ (i k : Fin n) (x' y' : V2) (H : OpenPartialHomeomorph V3 C3),
      k < i ∧ ((x' = x ∧ y' = y) ∨ (x' = y ∧ y' = x)) ∧
      x' ∈ intrinsicInterior ℝ (convexHull ℝ ((order i).val : Set V2)) ∧
      y' ∈ intrinsicInterior ℝ (convexHull ℝ ((order k).val : Set V2)) ∧
      (order i).val.card = 3 ∧ (order k).val.card = 3 ∧ boundary i = false ∧
      (states n).map x' ∈ (Q i).source ∧
      step.projection (step.inclusion ((states n).map y')) ∈ (B i).source ∧
      Q i ((states n).map x') = B i (step.projection (step.inclusion ((states n).map y'))) ∧
      Q i ((states n).map x') ∈ H.source ∧ H.source ⊆ (B i).target ∧
      H (Q i ((states n).map x')) = 0 ∧
      LocallyPiecewiseAffineOn H H.source ∧
      LocallyPiecewiseAffineOn H.symm H.target ∧
      (∀ z ∈ H.source,
        z ∈ B i '' (((step.projection ∘ step.inclusion) ∘ (states n).map) ''
          convexHull ℝ ((order i).val : Set V2) ∩ (B i).source) ↔ (H z).2 = 0) ∧
      ∀ z ∈ H.source,
        z ∈ B i '' (((step.projection ∘ step.inclusion) ∘ (states n).map) ''
          convexHull ℝ ((order k).val : Set V2) ∩ (B i).source) ↔ (H z).1.1 = 0 := by
  classical
  obtain ⟨i, k, x', y', hki, hswap, hxface, hyface, hxold, hkold, hpair⟩ :=
    SimplicialComplex.exists_ordered_faces_of_double_pair hK order horder hbefore P
      (fun l => (hP l).2) hcell hx hy hne hxy
  have hcard (a : Finset V2) (ha : a ∈ K.faces) : a.card ≤ 3 := by
    have h := (K.indep ha).card_le_finrank_succ.trans
      (Nat.add_le_add_right (Submodule.finrank_le _) 1)
    simpa only [Fintype.card_coe, Module.finrank_fintype_fun_eq_card,
      Fintype.card_fin] using h
  have hlarge {z : V2} (hz : z = x ∨ z = y) {a : Finset V2}
      (ha : a ∈ K.faces) (hza : z ∈ convexHull ℝ (a : Set V2)) : a.card = 3 := by
    have hu := hcard a ha
    have hn : ¬ a.card ≤ 2 := by
      intro hsmall
      rcases hz with rfl | rfl
      · exact (hoff a ha hsmall).1 hza
      · exact (hoff a ha hsmall).2 hza
    omega
  have hi3 := hlarge (hswap.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1))
    (order i).property (intrinsicInterior_subset hxface)
  have hk3 := hlarge (hswap.elim (fun h => Or.inr h.2) (fun h => Or.inl h.2))
    (order k).property (intrinsicInterior_subset hyface)
  have hfalse : boundary i = false := by
    cases hbi : boundary i with
    | false => rfl
    | true =>
      have hint : interior Rim.space = ∅ := by rw [hRim, interior_sphere']
      have hbound := Rim.face_card_le_of_interior_space_eq_empty hint ((hboundary i).mp hbi)
      simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hbound
      omega
  let motion := motions i
  let old : (P i.val).faces := ⟨(order k).val, hkold⟩
  let jf := (states n).map
  let jp := (states i.val).map
  let lower : V2 → s.Carrier := (step.projection ∘ step.inclusion) ∘ jf
  let p := Q i (jf x')
  have hinj : InjOn jp K.space := by
    intro z hz w hw he
    have hzw : (⟨z, hz⟩ : K.space) = ⟨w, hw⟩ :=
      (states i.val).embedding.injective he
    exact congrArg Subtype.val hzw
  have hold := hstable i.val n i.isLt.le le_rfl
  have hnext : EqOn jf (motion.ambient 1 ∘ jp) (P (i.val + 1)).space := by
    intro z hz
    exact (hstable (i.val + 1) n (by omega) le_rfl hz).trans
      (congrFun (htransitions i) z)
  have hjQ : MapsTo jp (convexHull ℝ ((order i).val : Set V2)) (Q i).source :=
    fun z hz => hUQ i ((states i.val).retained (order i) hz)
  obtain ⟨A, qA, qB, a, b, hA, _hAfaces, hAs, hqA, hqAi, hqB, hqBi,
    ha, hb, hcommon, hpa, hpb, _hqAx, _hqBy, _hqAint, _hqBint, hjoin,
    hcases, hacofaces, hbcofaces⟩ :=
    motion.exists_original_pair_incidence hK (hP i.val).1 (hP (i.val + 1)).1
      (order i).property hi3 (hsucc i) (states i.val).original_PL hinj
      (states n).original_PL (hQ i) hjQ (hB i) (hval i) (hmaps i) hfalse
      hold hnext old hk3 (hcell (order k)) hxface hxold hyface hpair
  obtain ⟨hxQ, hyB, _hcommon, _hpC, _hpA, hpnot, _hpL⟩ :=
    motion.original_pair_chart_coordinates (hP i.val).1 (order i).property (hsucc i)
      hinj hjQ (hval i) (hmaps i) hold hnext old (intrinsicInterior_subset hxface)
      hxold (intrinsicInterior_subset hyface) hpair
  have hpint : p ∈ interior motion.support.space := by
    have hxnext : x' ∈ (P (i.val + 1)).space :=
      (hsucc i).symm.subset (Or.inr (intrinsicInterior_subset hxface))
    have hc := motion.active_supported x' hxnext hxold
    have he := motion.coordinate_of_successor_agreement hnext hxnext
      (hjQ (intrinsicInterior_subset hxface)) (interior_subset hc)
    have himage := ((motion.coordinates.map 1).image_interior motion.support.space).trans
      (congrArg interior (motion.coordinates.carrier 1))
    change Q i (jf x') ∈ interior motion.support.space
    rw [he]
    exact himage.subset (mem_image_of_mem (motion.coordinates.map 1) hc)
  let O := interior motion.support.space ∩ motion.fixedSource.spaceᶜ
  have hO : IsOpen O := isOpen_interior.inter
    (motion.fixedSource.isCompact_space_of_finite motion.protected_finite).isClosed.isOpen_compl
  have hpO : p ∈ O := ⟨hpint, hpnot⟩
  have hAbound (u : Finset V3) (hu : u ∈ A.faces) : u.card ≤ 3 := by
    obtain ⟨T, hT, hTs, hTa⟩ := hqA
    have hTi : InjOn qA T.space := hqAi.mono hTs.subset
    exact A.face_card_le_of_hull_subset_finite_carrier T hT hu
      ((A.convexHull_subset_space hu).trans hTs.symm.subset) (fun c hc => by
        simpa [Module.finrank_prod] using hTa.face_card_le_of_injOn hTi hc)
  have hBbound (u : Finset V3) (hu : u ∈ (motion.targets old).faces) : u.card ≤ 3 :=
    (motion.targets_card old u hu).trans_eq hk3
  have hmax {L : SimplicialComplex ℝ V3} {a : Finset V3}
      (hbound : ∀ c ∈ L.faces, c.card ≤ 3) (ha3 : a.card = 3) :
      ∀ c ∈ L.faces, a ⊆ c → c = a := by
    intro c hc hac
    exact (Finset.eq_of_subset_of_card_le hac (by have h := hbound c hc; omega)).symm


  have hedge (L N : SimplicialComplex ℝ V3) (hN : N.faces.Finite)
      {a b : Finset V3} (ha : a ∈ L.faces) (hb : b ∈ N.faces)
      (ha2 : a.card = 2) (hb3 : b.card = 3)
      (hbmax : ∀ c ∈ N.faces, b ⊆ c → c = b)
      (hpa : p ∈ intrinsicInterior ℝ (convexHull ℝ (a : Set V3)))
      (hpb : p ∈ intrinsicInterior ℝ (convexHull ℝ (b : Set V3)))
      (hjoin : affineSpan ℝ ((a : Set V3) ∪ (b : Set V3)) = ⊤)
      (hcofaces : ∃ u v : Finset V3, u ∈ L.faces ∧ v ∈ L.faces ∧
        u.card = 3 ∧ v.card = 3 ∧ a ⊆ u ∧ a ⊆ v ∧ u ≠ v ∧
        (∀ z ∈ L.faces, a ⊆ z → z ⊆ u ∨ z ⊆ v) ∧
        ∃ W : Set V3, IsOpen W ∧ p ∈ W ∧
          ∀ x ∈ W, x ∈ L.space ↔
            x ∈ convexHull ℝ (u : Set V3) ∪ convexHull ℝ (v : Set V3)) :
      ∃ H : OpenPartialHomeomorph V3 C3,
        p ∈ H.source ∧ H.source ⊆ O ∧ H p = 0 ∧
        LocallyPiecewiseAffineOn H H.source ∧
        LocallyPiecewiseAffineOn H.symm H.target ∧
        (∀ z ∈ H.source, z ∈ L.space ↔ (H z).1.1 = 0) ∧
        ∀ z ∈ H.source, z ∈ N.space ↔ (H z).2 = 0 := by
    obtain ⟨c, d, hc, hd, hc3, hd3, hac, had, hcd, _hexhaust, W, hW, hpW, hLW⟩ := hcofaces
    obtain ⟨V, hV, hpV, hNV⟩ := N.exists_open_maximal_face_affine_germ hN hb hbmax hpb
    obtain ⟨ell, hell, hplane⟩ :=
      (affineSpan ℝ (b : Set V3)).exists_direction_height_of_codim_one
        (by rw [N.finrank_faceDirection_of_card hb hb3]; simp)
        (convexHull_subset_affineSpan (s := (b : Set V3)) (intrinsicInterior_subset hpb))
    let height : V3 → ℝ := fun z => ell (z - p)
    have hnonconstant : ∃ z ∈ a, height z ≠ 0 := by
      by_contra hn
      have hzero : ∀ z ∈ a, height z = 0 := by
        intro z hz
        exact not_not.mp (fun he => hn ⟨z, hz, he⟩)
      have hle : affineSpan ℝ ((a : Set V3) ∪ (b : Set V3)) ≤
          affineSpan ℝ (b : Set V3) := affineSpan_le.mpr (union_subset
        (fun z hz => (hplane z).mpr (hzero z hz)) (subset_affineSpan ℝ _))
      rw [hjoin] at hle
      have htop : affineSpan ℝ (b : Set V3) = ⊤ := top_le_iff.mp hle
      have hrank := N.finrank_faceDirection_of_card hb hb3
      rw [htop, AffineSubspace.direction_top, finrank_top] at hrank
      simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hrank
      omega
    have hsigned : ∃ u v : V3, u ≠ v ∧ a = {u, v} ∧
        height u < 0 ∧ 0 < height v ∧ p ∈ segment ℝ u v := by
      obtain ⟨u, v, huv, hauv⟩ := Finset.card_eq_two.mp ha2
      obtain ⟨w, hw, hsum, hvalue⟩ :=
        (L.indep ha).exists_positive_weights_of_mem_intrinsicInterior hpa
      have hwu := hw u (hauv.symm ▸ Finset.mem_insert_self _ _)
      have hwv := hw v (hauv.symm ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
      have hsum' : w u + w v = 1 := by simpa only [hauv, Finset.sum_pair huv] using hsum
      have hraw : w u * ell u + w v * ell v = ell p := by
        simpa only [hauv, Finset.sum_pair huv, map_add, map_smul, smul_eq_mul] using
          congrArg ell hvalue
      have hbalance : w u * height u + w v * height v = 0 := by
        dsimp only [height]
        simp only [map_sub]
        calc
          w u * (ell u - ell p) + w v * (ell v - ell p) =
              (w u * ell u + w v * ell v) - (w u + w v) * ell p := by ring
          _ = 0 := by rw [hraw, hsum', one_mul, sub_self]
      have hn : height u ≠ 0 ∨ height v ≠ 0 := by
        obtain ⟨z, hz, hzero⟩ := hnonconstant
        simp only [hauv, Finset.mem_insert, Finset.mem_singleton] at hz
        exact hz.elim (fun he => Or.inl (he ▸ hzero)) (fun he => Or.inr (he ▸ hzero))
      have hpseg : p ∈ segment ℝ u v := by
        simpa only [hauv, Finset.coe_pair, convexHull_pair] using intrinsicInterior_subset hpa
      by_cases hu : height u < 0
      · have hv : 0 < height v := by
          by_contra h
          have h0 := mul_nonpos_of_nonneg_of_nonpos hwv.le (le_of_not_gt h)
          have h1 := mul_neg_of_pos_of_neg hwu hu
          linarith
        exact ⟨u, v, huv, hauv, hu, hv, hpseg⟩
      · have hv : height v < 0 := by
          by_contra h
          have hu0 : 0 ≤ height u := le_of_not_gt hu
          have hv0 : 0 ≤ height v := le_of_not_gt h
          rcases hn with hn | hn
          · have h1 := mul_pos hwu (lt_of_le_of_ne hu0 (Ne.symm hn))
            have h0 := mul_nonneg hwv.le hv0
            linarith
          · have h1 := mul_pos hwv (lt_of_le_of_ne hv0 (Ne.symm hn))
            have h0 := mul_nonneg hwu.le hu0
            linarith
        have hu' : 0 < height u := by
          by_contra h
          have h0 := mul_nonpos_of_nonneg_of_nonpos hwu.le (le_of_not_gt h)
          have h1 := mul_neg_of_pos_of_neg hwv hv
          linarith
        exact ⟨v, u, huv.symm, hauv.trans (Finset.pair_comm _ _), hv, hu',
          (segment_symm ℝ u v) ▸ hpseg⟩
    obtain ⟨u, v, _huv, hauv, hu, hv, hpseg⟩ := hsigned
    have hgap : height v - height u ≠ 0 := (sub_pos.mpr (hu.trans hv)).ne'
    have hellgap : ell v - ell u = height v - height u := by
      dsimp only [height]
      simp only [map_sub]
      ring
    let axis : V3 := (height v - height u)⁻¹ • (v - u)
    have haxisheight : ell axis = 1 := by
      rw [show axis = (height v - height u)⁻¹ • (v - u) from rfl]
      rw [map_smul, map_sub, hellgap]
      exact inv_mul_cancel₀ hgap
    have hker : Module.finrank ℝ ell.ker = 2 := by
      have h := Module.Dual.finrank_ker_add_one_of_ne_zero hell
      simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
      omega
    let coords : C2 ≃ₗ[ℝ] ell.ker := LinearEquiv.ofFinrankEq _ _ (by
      simp [Module.finrank_prod, hker])
    let linear : C3 →ₗ[ℝ] V3 :=
      (ell.ker.subtype.comp coords.toLinearMap).comp (LinearMap.fst ℝ C2 ℝ) +
        (LinearMap.snd ℝ C2 ℝ).smulRight axis
    have hlinear (z : C3) : linear z = (coords z.1 : V3) + z.2 • axis := rfl
    have hheight (z : C3) : ell (linear z) = z.2 := by
      have he0 : ell (coords z.1 : V3) = 0 := (coords z.1).property
      rw [hlinear, map_add, map_smul, he0, haxisheight]
      simp
    have hli : Function.Injective linear := by
      intro z w he
      have hlast : z.2 = w.2 := (hheight z).symm.trans ((congrArg ell he).trans (hheight w))
      have hfirst : (coords z.1 : V3) = coords w.1 := by
        have hsum : (coords z.1 : V3) + w.2 • axis = (coords w.1 : V3) + w.2 • axis := by
          simpa only [hlinear, hlast] using he
        exact add_right_cancel hsum
      exact Prod.ext (coords.injective (Subtype.ext hfirst)) hlast
    have hls : Function.Surjective linear := by
      intro z
      let w : ell.ker := ⟨z - ell z • axis, by
        change ell (z - ell z • axis) = 0
        rw [map_sub, map_smul, haxisheight]
        simp⟩
      refine ⟨(coords.symm w, ell z), ?_⟩
      rw [hlinear, coords.apply_symm_apply]
      change z - ell z • axis + ell z • axis = z
      abel
    let equiv := (LinearEquiv.ofBijective linear ⟨hli, hls⟩).toContinuousLinearEquiv
    let F := equiv.toLinearEquiv.toAffineEquiv.toContinuousAffineEquiv.trans
      (ContinuousAffineEquiv.constVAdd ℝ V3 p)
    have hF (z : C3) : F z = linear z + p := add_comm _ _
    have hFzero : F 0 = p := by rw [hF, map_zero, zero_add]
    have hFheight (z : C3) : height (F z) = z.2 := by
      change ell (F z - p) = z.2
      rw [hF, add_sub_cancel_right, hheight]
    obtain ⟨t₀, _ht₀, ht₀p⟩ := (segment_eq_image_lineMap ℝ u v).subset hpseg
    have hpvalue : u + t₀ • (v - u) = p := by
      rw [AffineMap.lineMap_apply_module] at ht₀p
      calc
        u + t₀ • (v - u) = (1 - t₀) • u + t₀ • v := by module
        _ = p := ht₀p
    have htvalue : t₀ * (height v - height u) = -height u := by
      have h := congrArg ell hpvalue
      rw [map_add, map_smul, map_sub, hellgap] at h
      change ell u + t₀ * (height v - height u) = ell p at h
      have huheight : height u = ell u - ell p := map_sub ell u p
      linarith
    have htdiv : t₀ = -height u * (height v - height u)⁻¹ := by
      rw [← div_eq_mul_inv]
      exact (eq_div_iff hgap).mpr htvalue
    have hFaxis (z : ℝ) : F ((0, 0), z) = z • axis + p := by
      rw [hF, hlinear]
      change (coords (0 : C2) : V3) + z • axis + p = z • axis + p
      rw [map_zero]
      change (0 : V3) + z • axis + p = z • axis + p
      rw [zero_add]
    have hFu0 : F ((0, 0), height u) = u := by
      rw [hFaxis, ← hpvalue, htdiv]
      dsimp only [axis]
      module
    have hFv0 : F ((0, 0), height v) = v := by
      calc
        F ((0, 0), height v) = F ((0, 0), height u) + (height v - height u) • axis := by
          rw [hFaxis, hFaxis]
          module
        _ = u + (v - u) := by
          rw [hFu0]
          dsimp only [axis]
          rw [smul_smul, mul_inv_cancel₀ hgap, one_smul]
        _ = v := by abel
    have hFu : F.symm u = ((0, 0), height u) :=
      (congrArg F.symm hFu0).symm.trans (F.symm_apply_apply _)
    have hFv : F.symm v = ((0, 0), height v) :=
      (congrArg F.symm hFv0).symm.trans (F.symm_apply_apply _)
    obtain ⟨w, hwa, hwc⟩ := Finset.exists_eq_insert_iff.mpr ⟨hac, by omega⟩
    obtain ⟨z, hza, hzd⟩ := Finset.exists_eq_insert_iff.mpr ⟨had, by omega⟩
    have haxis (t₀ : ℝ) : F ((0, 0), t₀) ∈ affineSpan ℝ (a : Set V3) := by
      rw [hauv, Finset.coe_pair]
      apply mem_affineSpan_pair_iff_exists_lineMap_eq.mpr
      refine ⟨(t₀ - height u) / (height v - height u), ?_⟩
      apply F.symm.injective
      have hline : F.symm (AffineMap.lineMap u v ((t₀ - height u) / (height v - height u))) =
          AffineMap.lineMap (F.symm u) (F.symm v) ((t₀ - height u) / (height v - height u)) :=
        F.symm.toAffineEquiv.apply_lineMap _ _ _
      rw [hline, hFu, hFv, F.symm_apply_apply]
      ext <;> simp only [AffineMap.lineMap_apply_module, Prod.smul_fst,
        Prod.smul_snd, Prod.fst_add, Prod.snd_add, smul_eq_mul, mul_zero, add_zero]
      field_simp [hgap]
      ring
    have hnonzero {c : Finset V3} (hc : c ∈ L.faces) {w : V3}
        (hwa : w ∉ a) (hwc : insert w a = c) : (F.symm w).1 ≠ 0 := by
      intro hw
      have hwspan : w ∈ affineSpan ℝ (a : Set V3) := by
        have he : F ((0, 0), (F.symm w).2) = w := by
          change F ((0 : C2), (F.symm w).2) = w
          rw [← hw]
          exact F.apply_symm_apply w
        exact he ▸ haxis (F.symm w).2
      have hwc' : w ∈ c := hwc ▸ Finset.mem_insert_self w a
      have hac' : a ⊆ c := hwc ▸ Finset.subset_insert w a
      have himage : Subtype.val '' {v : c | (v : V3) ∈ a} = (a : Set V3) := by
        ext v
        constructor
        · rintro ⟨q, hq, rfl⟩
          exact hq
        · intro hv
          exact ⟨⟨v, hac' hv⟩, hv, rfl⟩
      exact hwa ((L.indep hc).mem_affineSpan_iff ⟨w, hwc'⟩
        {v : c | (v : V3) ∈ a} |>.mp (himage.symm ▸ hwspan))
    have hw := hnonzero hc hwa hwc
    have hz := hnonzero hd hza hzd
    have hFhull (S : Set V3) : F.symm '' convexHull ℝ S =
        convexHull ℝ (F.symm '' S) := F.symm.toAffineEquiv.toAffineMap.image_convexHull S
    have hcoord (w : V3) : F.symm '' convexHull ℝ (↑(insert w a) : Set V3) =
        convexHull ℝ ({((0, 0), height u), ((0, 0), height v), F.symm w} : Set C3) := by
      rw [hFhull]
      simp only [Finset.coe_insert, hauv, Finset.coe_singleton, image_insert_eq,
        image_singleton, hFu, hFv]
      rw [insert_comm (F.symm w) ((0, 0), height u),
        pair_comm (F.symm w) ((0, 0), height v)]
    have hcda : c ∩ d = a := by
      have hle : (c ∩ d).card ≤ 2 := by
        by_contra hn
        have he : c ∩ d = c :=
          Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
        have hcd' : c ⊆ d := he ▸ Finset.inter_subset_right
        exact hcd (Finset.eq_of_subset_of_card_le hcd' (by omega))
      exact (Finset.eq_of_subset_of_card_le (Finset.subset_inter hac had) (by omega)).symm
    have haxisHull : F.symm '' convexHull ℝ (a : Set V3) ⊆ {q : C3 | q.1 = 0} := by
      rw [hFhull]
      simp only [hauv, Finset.coe_pair, image_insert_eq, image_singleton, hFu, hFv]
      apply convexHull_min
      · rintro q (rfl | rfl) <;> rfl
      · exact (convex_singleton (0 : C2)).linear_preimage (LinearMap.fst ℝ C2 ℝ)
    have hback {c : Finset V3} {q : C3}
        (hq : q ∈ F.symm '' convexHull ℝ (c : Set V3)) :
        F q ∈ convexHull ℝ (c : Set V3) := by
      obtain ⟨v, hv, rfl⟩ := hq
      simpa only [F.apply_symm_apply] using hv
    have hinter (q : C3)
        (hqc : q ∈ convexHull ℝ ({(0, height u), (0, height v), F.symm w} : Set C3))
        (hqd : q ∈ convexHull ℝ ({(0, height u), (0, height v), F.symm z} : Set C3)) :
        q.1 = 0 := by
      have hcq : F q ∈ convexHull ℝ (c : Set V3) := hwc ▸ hback ((hcoord w).symm.subset hqc)
      have hdq : F q ∈ convexHull ℝ (d : Set V3) := hzd ▸ hback ((hcoord z).symm.subset hqd)
      have haq : F q ∈ convexHull ℝ (a : Set V3) := by
        rw [← hcda, Finset.coe_inter, ← L.convexHull_inter_convexHull hc hd]
        exact ⟨hcq, hdq⟩
      exact haxisHull ⟨F q, haq, F.symm_apply_apply q⟩
    let V₀ := O ∩ (W ∩ V)
    have hV₀ : IsOpen V₀ := hO.inter (hW.inter hV)
    obtain ⟨T, hTzero, hTO, hT0, hTPL, hTlast, hTwhole⟩ :=
      exists_vertical_triangle_pair_crossing_chart hw hz hu hv
        (F.symm w).2 (F.symm z).2 hinter (F.symm.toHomeomorph.isOpenMap _ hV₀)
        ⟨p, ⟨hpO, hpW, hpV⟩, by
          change F.symm p = 0
          rw [← hFzero, F.symm_apply_apply]⟩
    let H := F.symm.toHomeomorph.toOpenPartialHomeomorph.trans T
    have hsource (q : V3) : q ∈ H.source ↔ F.symm q ∈ T.source := by
      change q ∈ univ ∩ F.symm ⁻¹' T.source ↔ _
      exact and_iff_right (mem_univ q)
    have hlocal {q : V3} (hq : q ∈ H.source) : q ∈ V₀ := by
      obtain ⟨v, hv, he⟩ := hTO ((hsource q).mp hq)
      exact F.symm.injective he ▸ hv
    refine ⟨H, (hsource p).mpr (by rw [← hFzero, F.symm_apply_apply]; exact hTzero),
      fun _ hq => (hlocal hq).1, ?_, ?_, ?_, ?_, ?_⟩
    · change T (F.symm p) = 0
      rw [← hFzero, F.symm_apply_apply, hT0]
    · exact hTPL.1.comp
        (locallyPiecewiseAffineOn_affine F.symm.toContinuousAffineMap isOpen_univ)
    · exact ((locallyPiecewiseAffineOn_affine F.toContinuousAffineMap isOpen_univ).comp
        hTPL.2).mono H.open_target (fun _ hq => ⟨hq.1, mem_univ _⟩)
    · intro q hq
      change q ∈ L.space ↔ (T (F.symm q)).1.1 = 0
      rw [hLW q (hlocal hq).2.1, ← hTwhole _ ((hsource q).mp hq)]
      have hmem (c : Finset V3) : F.symm q ∈ F.symm '' convexHull ℝ (c : Set V3) ↔
          q ∈ convexHull ℝ (c : Set V3) := F.symm.injective.mem_set_image
      change q ∈ convexHull ℝ (c : Set V3) ∪ convexHull ℝ (d : Set V3) ↔
        F.symm q ∈ convexHull ℝ ({((0, 0), height u), ((0, 0), height v), F.symm w} : Set C3) ∪
          convexHull ℝ ({((0, 0), height u), ((0, 0), height v), F.symm z} : Set C3)
      rw [← hcoord w, ← hcoord z, hwc, hzd]
      exact (or_congr (hmem c) (hmem d)).symm
    · intro q hq
      change q ∈ N.space ↔ (T (F.symm q)).2 = 0
      rw [hTlast _ ((hsource q).mp hq)]
      have hlevel : height q = (F.symm q).2 := by
        simpa only [F.apply_symm_apply] using hFheight (F.symm q)
      exact (hNV q (hlocal hq).2.2).trans ((hplane q).trans (by rw [← hlevel]))
  have hchart : ∃ H : OpenPartialHomeomorph V3 C3,
      p ∈ H.source ∧ H.source ⊆ O ∧ H p = 0 ∧
      LocallyPiecewiseAffineOn H H.source ∧ LocallyPiecewiseAffineOn H.symm H.target ∧
      (∀ z ∈ H.source, z ∈ A.space ↔ (H z).2 = 0) ∧
      ∀ z ∈ H.source, z ∈ (motion.targets old).space ↔ (H z).1.1 = 0 := by
    rcases hcases with ⟨ha3, hb3⟩ | ⟨ha2, hb3⟩ | ⟨ha3, hb2⟩
    · exact SimplicialComplex.exists_triangle_interior_crossing_chart (by simp)
        A (motion.targets old) hA (motion.targets_finite old) ha hb ha3 hb3
        (hmax hAbound ha3) (hmax hBbound hb3) hjoin hpa hpb hO hpO
    · obtain ⟨H, hpH, hHO, hH0, hHPL, hHiPL, hHA, hHB⟩ :=
        hedge A (motion.targets old) (motion.targets_finite old) ha hb ha2 hb3
          (hmax hBbound hb3) hpa hpb hjoin (hacofaces ha2)
      let perm : C3 ≃ₗ[ℝ] C3 :=
        { toFun := fun z => ((z.2, z.1.2), z.1.1)
          invFun := fun z => ((z.2, z.1.2), z.1.1)
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      let E := perm.toContinuousLinearEquiv.toLinearEquiv.toAffineEquiv.toContinuousAffineEquiv
      let H' := H.trans E.toHomeomorph.toOpenPartialHomeomorph
      have hsrc : H'.source = H.source := by
        change H.source ∩ H ⁻¹' univ = H.source
        simp only [preimage_univ, inter_univ]
      refine ⟨H', hsrc.symm.subset hpH, hsrc.subset.trans hHO, ?_, ?_, ?_, ?_, ?_⟩
      · change E (H p) = 0
        rw [hH0]
        rfl
      · exact ((locallyPiecewiseAffineOn_affine E.toContinuousAffineMap isOpen_univ).comp
          hHPL).mono H'.open_source (fun _ hz => ⟨hsrc.subset hz, mem_univ _⟩)
      · exact hHiPL.comp
          (locallyPiecewiseAffineOn_affine E.symm.toContinuousAffineMap isOpen_univ)
      · intro z hz
        exact hHA z (hsrc.subset hz)
      · intro z hz
        exact hHB z (hsrc.subset hz)
    · obtain ⟨H, hpH, hHO, hH0, hHPL, hHiPL, hHB, hHA⟩ :=
        hedge (motion.targets old) A hA hb ha hb2 ha3 (hmax hAbound ha3) hpb hpa
          (by simpa only [union_comm] using hjoin) (hbcofaces hb2)
      exact ⟨H, hpH, hHO, hH0, hHPL, hHiPL, hHA, hHB⟩
  obtain ⟨H, hpH, hHO, hH0, hHPL, hHiPL, hHA, hHB⟩ := hchart


  have hactive (z : V3) (hz : z ∈ O) : z ∈ A.space ↔
      z ∈ B i '' (lower '' convexHull ℝ ((order i).val : Set V2) ∩ (B i).source) := by
    constructor
    · intro hzA
      obtain ⟨w, hw, hwz⟩ := hAs.subset hzA
      rw [motion.source_space] at hw
      obtain ⟨⟨v, ⟨⟨q, hqnext, rfl⟩, hqQ⟩, hqw⟩, hwC⟩ := hw
      have hqnot : q ∉ (P i.val).space := by
        intro hqold
        have hwfixed : w ∈ motion.fixedSource.space := by
          rw [motion.protected_space]
          exact ⟨⟨jp q, ⟨mem_image_of_mem jp hqold, hqQ⟩, hqw⟩, hwC⟩
        exact hz.2 ((motion.coordinates.fixed_protected 1 w hwfixed).symm.trans hwz ▸ hwfixed)
      have hqface : q ∈ convexHull ℝ ((order i).val : Set V2) :=
        ((hsucc i).subset hqnext).resolve_left hqnot
      have hqcoord : Q i (jf q) = z := by
        have hc := motion.coordinate_of_successor_agreement hnext hqnext hqQ
          (hqw.symm ▸ hwC)
        exact hc.trans ((congrArg (motion.coordinates.map 1) hqw).trans hwz)
      have hqfinalQ : jf q ∈ (Q i).source := by
        rw [hnext hqnext]
        exact hUQ i (motion.retained 1 (order i) hqface)
      refine ⟨lower q, ⟨mem_image_of_mem lower hqface, (hmaps i) hqfinalQ⟩, ?_⟩
      exact (hval i (jf q)).symm.trans hqcoord
    · rintro ⟨v, ⟨⟨q, hqface, rfl⟩, _hqB⟩, hqz⟩
      have hqnext : q ∈ (P (i.val + 1)).space := (hsucc i).symm.subset (Or.inr hqface)
      have hqQ := hjQ hqface
      have hmapQ : motion.coordinates.map 1 (Q i (jp q)) ∈ (Q i).target :=
        (motion.coordinates.mem_superset_iff motion.support_upper 1 _).mpr
          ((Q i).map_source hqQ)
      have hqcoord : motion.coordinates.map 1 (Q i (jp q)) = z := by
        calc
          motion.coordinates.map 1 (Q i (jp q)) =
              Q i ((Q i).symm (motion.coordinates.map 1 (Q i (jp q)))) :=
            ((Q i).right_inv hmapQ).symm
          _ = Q i (motion.ambient 1 (jp q)) :=
            congrArg (Q i) (motion.chart_formula 1 hqQ).symm
          _ = Q i (jf q) := congrArg (Q i) (hnext hqnext).symm
          _ = B i (lower q) := hval i (jf q)
          _ = z := hqz
      have hqc : Q i (jp q) ∈ motion.support.space :=
        (motion.coordinates.mem_superset_iff (Subset.rfl) 1 _).mp
          (hqcoord.symm ▸ interior_subset hz.1)
      apply hAs.symm.subset
      refine ⟨Q i (jp q), ?_, hqcoord⟩
      rw [motion.source_space]
      exact ⟨⟨jp q, ⟨mem_image_of_mem jp hqnext, hqQ⟩, rfl⟩, hqc⟩
  have hpassive (z : V3) (hz : z ∈ O) : z ∈ (motion.targets old).space ↔
      z ∈ B i '' (lower '' convexHull ℝ ((order k).val : Set V2) ∩ (B i).source) := by
    rw [motion.targets_space_of_prefix_agreement hold old]
    exact and_iff_left (interior_subset hz.1)
  refine ⟨i, k, x', y', H, hki, hswap, hxface, hyface, hi3, hk3, hfalse,
    hxQ, hyB, hcommon, hpH, fun z hz => motion.support_lower
      (interior_subset (hHO hz).1), hH0, hHPL, hHiPL, ?_, ?_⟩
  · intro z hz
    exact (hactive z (hHO hz)).symm.trans (hHA z hz)
  · intro z hz
    exact (hpassive z (hHO hz)).symm.trans (hHB z hz)

end Geometry.OriginalPLTower
