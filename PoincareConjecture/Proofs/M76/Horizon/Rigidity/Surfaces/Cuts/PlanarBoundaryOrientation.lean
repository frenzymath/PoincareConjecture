import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.PlanarBoundaryCycle
import PoincareConjecture.Proofs.M76.Mathlib.ConvexBoundaryCone
import PoincareConjecture.Proofs.M76.Mathlib.PairedFacetCentroidSigns
import PoincareConjecture.Proofs.M76.Horizon.Polyhedral.Simplicial.PlanarTriangleBoundaries
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Boundary.Orientation.CofaceSideTransport









set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.OriginalTriangleCopies


def planarCross (v : ℝ × ℝ) : (ℝ × ℝ) →ₗ[ℝ] ℝ where
  toFun w := v.1 * w.2 - v.2 * w.1
  map_add' x y := by simp only [Prod.fst_add, Prod.snd_add]; ring
  map_smul' r x := by
    change v.1 * (r * x.2) - v.2 * (r * x.1) = r * (v.1 * x.2 - v.2 * x.1)
    ring

theorem planarCross_swap (v w : ℝ × ℝ) : planarCross v w = -planarCross w v := by
  change v.1 * w.2 - v.2 * w.1 = -(w.1 * v.2 - w.2 * v.1)
  ring

theorem planarCross_self (v : ℝ × ℝ) : planarCross v v = 0 := by
  change v.1 * v.2 - v.2 * v.1 = 0
  ring

theorem planarCross_ne_zero {v : ℝ × ℝ} (hv : v ≠ 0) : planarCross v ≠ 0 := by
  intro h
  have h₁ := LinearMap.congr_fun h (0, 1)
  have h₂ := LinearMap.congr_fun h (1, 0)
  simp only [planarCross, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.zero_apply,
    mul_one, mul_zero, sub_zero, zero_sub, neg_eq_zero] at h₁ h₂
  exact hv (Prod.ext h₁ h₂)


theorem planar_triangle_cross_ne_zero (p : Fin 3 → ℝ × ℝ)
    (hp : AffineIndependent ℝ p) : planarCross (p 1 - p 0) (p 2 - p 0) ≠ 0 := by
  have hpair : LinearIndependent ℝ ![p 1 - p 0, p 2 - p 0] := by
    have h := (affineIndependent_iff_linearIndependent_vsub ℝ p 0).mp hp
    have hc := h.comp
      (fun i : Fin 2 ↦ (⟨i.succ, Fin.succ_ne_zero i⟩ : {j : Fin 3 // j ≠ 0}))
      (by intro i j he; exact Fin.succ_injective _ (congrArg Subtype.val he))
    convert! hc using 1
    funext i
    fin_cases i <;> rfl
  let u := p 1 - p 0
  let v := p 2 - p 0
  obtain ⟨hv, hmul⟩ := linearIndependent_fin2.mp hpair
  change v ≠ 0 at hv
  change ∀ r : ℝ, r • v ≠ u at hmul
  intro hd
  change u.1 * v.2 - u.2 * v.1 = 0 at hd
  by_cases hv₁ : v.1 = 0
  · have hv₂ : v.2 ≠ 0 := by intro h; exact hv (Prod.ext hv₁ h)
    apply hmul (u.2 / v.2)
    apply Prod.ext
    · change u.2 / v.2 * v.1 = u.1
      rw [hv₁, mul_zero]
      have : u.1 * v.2 = 0 := by simpa only [hv₁, mul_zero, sub_zero] using hd
      exact ((mul_eq_zero.mp this).resolve_right hv₂).symm
    · change u.2 / v.2 * v.2 = u.2
      exact div_mul_cancel₀ _ hv₂
  · apply hmul (u.1 / v.1)
    apply Prod.ext
    · change u.1 / v.1 * v.1 = u.1
      exact div_mul_cancel₀ _ hv₁
    · change u.1 / v.1 * v.2 = u.2
      field_simp
      nlinarith



theorem paired_planar_fan_positive_product
    (K : SimplicialComplex ℝ (ℝ × ℝ)) (a b c : ℝ × ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (ht : {0, a, b} ∈ K.faces) (hu : {0, b, c} ∈ K.faces) :
    0 < planarCross a b * planarCross b c := by
  classical
  have hs : {0, b} ∈ K.faces :=
    K.down_closed ht (by intro x hx; simp only [Finset.mem_insert,
      Finset.mem_singleton] at hx ⊢; tauto) (by simp)
  have hdim : Module.finrank ℝ (ℝ × ℝ) = 2 := by simp
  have hsc : ({0, b} : Finset (ℝ × ℝ)).card = Module.finrank ℝ (ℝ × ℝ) := by
    simp [hdim, hb.symm]
  have htc : ({0, a, b} : Finset (ℝ × ℝ)).card = Module.finrank ℝ (ℝ × ℝ) + 1 := by
    simp [hdim, ha.symm, hb.symm, hab]
  have huc : ({0, b, c} : Finset (ℝ × ℝ)).card = Module.finrank ℝ (ℝ × ℝ) + 1 := by
    simp [hdim, hb.symm, hc.symm, hbc]
  have htu : ({0, a, b} : Finset (ℝ × ℝ)) ≠ {0, b, c} := by
    intro he
    have hm : a ∈ ({0, b, c} : Finset (ℝ × ℝ)) := he ▸ (by simp)
    simp [ha, hab, hac] at hm
  obtain h | h := K.opposite_centroid_signs_of_paired_facet hs ht hu hsc htc huc
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢; tauto)
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢; tauto)
    htu (planarCross b).toAffineMap (planarCross_ne_zero hb)
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with hx | hx
        · rw [hx]; exact (planarCross b).map_zero
        · rw [hx]; exact planarCross_self b)
  all_goals
    have hid : K.AffineOnFaces (id : (ℝ × ℝ) → (ℝ × ℝ)) := by
      intro s hs
      exact ⟨ContinuousAffineMap.id ℝ _, fun _ _ ↦ rfl⟩
    have hta := SimplicialComplex.AffineOnFaces.strict_vertex_signs_of_centroid
      K id hid _ ht a (planarCross b) 0 (by
      intro x hx hxa
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with hx | hx | hx
      · rw [hx]; simp
      · exact (hxa hx).elim
      · rw [hx]; simpa using planarCross_self b)
    have huc' := SimplicialComplex.AffineOnFaces.strict_vertex_signs_of_centroid
      K id hid _ hu c (planarCross b) 0 (by
      intro x hx hxc
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with hx | hx | hx
      · rw [hx]; simp
      · rw [hx]; simpa using planarCross_self b
      · exact (hxc hx).elim)
    simp only [id_eq, sub_zero] at hta huc'
  · have ha' := hta.1 h.1
    have hc' := huc'.2 h.2
    rw [planarCross_swap a b]
    exact mul_pos (neg_pos.mpr ha') hc'
  · have ha' := hta.2 h.1
    have hc' := huc'.1 h.2
    rw [planarCross_swap a b]
    exact mul_pos_of_neg_of_neg (neg_neg_of_pos ha') hc'

private theorem rotate_ne_self (n : ℕ) (i : Fin (n + 3)) :
    finRotate (n + 3) i ≠ i := by
  intro he
  have h : (1 : Fin (n + 3)) = 0 := by
    apply add_left_cancel (a := i)
    simpa only [finRotate_apply, add_zero] using he
  have hv := congrArg Fin.val h
  norm_num [Fin.val_ofNat, Nat.mod_eq_of_lt (by omega : 1 < n + 3)] at hv

private theorem rotate_twice_ne_self (n : ℕ) (i : Fin (n + 3)) :
    finRotate (n + 3) (finRotate (n + 3) i) ≠ i := by
  intro he
  have hone : (1 : Fin (n + 3)) + 1 = 2 := by
    apply Fin.ext
    norm_num [Fin.val_add, Fin.val_ofNat,
      Nat.mod_eq_of_lt (by omega : 1 < n + 3),
      Nat.mod_eq_of_lt (by omega : 2 < n + 3)]
  have h : (2 : Fin (n + 3)) = 0 := by
    apply add_left_cancel (a := i)
    simpa only [finRotate_apply, add_assoc, hone, add_zero] using he
  have hv := congrArg Fin.val h
  norm_num [Fin.val_ofNat, Nat.mod_eq_of_lt (by omega : 2 < n + 3)] at hv



theorem planar_boundary_cycle_uniform_direction
    (K : SimplicialComplex ℝ (ℝ × ℝ)) (hcv : Convex ℝ K.space)
    (hzero : (0 : ℝ × ℝ) ∈ interior K.space)
    (n : ℕ) (P : Polygon (ℝ × ℝ) (n + 3)) (hPi : Function.Injective P)
    (hedge : ∀ i, {P i, P (finRotate (n + 3) i)} ∈
      (K.frontierSubcomplex K.space).faces) :
    (∀ i, 0 < planarCross (P i) (P (finRotate (n + 3) i))) ∨
      (∀ i, planarCross (P i) (P (finRotate (n + 3) i)) < 0) := by
  classical
  let L := K.frontierSubcomplex K.space
  have hLs : L.space ⊆ frontier K.space := by
    intro x hx
    obtain ⟨s, hs, hxs⟩ := SimplicialComplex.mem_space_iff.mp hx
    exact hs.2 hxs
  have hlin := L.linearIndependent_faces_of_space_subset_frontier hcv hzero hLs
  have hrad := (hcv.injOn_normalize_frontier hzero).mono hLs
  let C := L.coneAtZero hlin hrad
  have hPzero (i : Fin (n + 3)) : P i ≠ 0 := by
    intro he
    have hx : P i ∈ frontier K.space :=
      (hedge i).2 (subset_convexHull ℝ _ (by simp))
    exact hx.2 (he.symm ▸ hzero)
  have htri (i : Fin (n + 3)) : {0, P i, P (finRotate (n + 3) i)} ∈ C.faces :=
    L.insert_zero_mem_coneAtZero_faces hlin hrad (hedge i)
  let d : Fin (n + 3) → ℝ := fun i ↦ planarCross (P i) (P (finRotate (n + 3) i))
  have hprod (i : Fin (n + 3)) : 0 < d i * d (finRotate (n + 3) i) := by
    exact paired_planar_fan_positive_product C _ _ _ (hPzero i)
      (hPzero _) (hPzero _)
      (fun he ↦ rotate_ne_self n i (hPi he).symm)
      (fun he ↦ rotate_ne_self n _ (hPi he).symm)
      (fun he ↦ rotate_twice_ne_self n i (hPi he).symm)
      (htri i) (htri _)
  have hcycle := isCycle_finRotate_of_le (show 2 ≤ n + 3 by omega)
  have hreach (i : Fin (n + 3)) : ∃ k : ℕ, (finRotate (n + 3) ^ k) 0 = i :=
    hcycle.exists_pow_eq (rotate_ne_self n 0) (rotate_ne_self n i)
  rcases (mul_pos_iff.mp (hprod 0)) with hpos | hneg
  · left
    intro i
    change 0 < d i
    obtain ⟨k, rfl⟩ := hreach i
    induction k with
    | zero => simpa using hpos.1
    | succ k ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      exact (mul_pos_iff.mp (hprod _)).resolve_right
        (fun h ↦ (not_lt_of_ge ih.le h.1)) |>.2
  · right
    intro i
    change d i < 0
    obtain ⟨k, rfl⟩ := hreach i
    induction k with
    | zero => simpa using hneg.1
    | succ k ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      exact (mul_pos_iff.mp (hprod _)).resolve_left
        (fun h ↦ (not_lt_of_ge h.1.le ih)) |>.2

private theorem planarCross_support_identity
    (L : (ℝ × ℝ) →ₗ[ℝ] ℝ) (a b x : ℝ × ℝ) (c : ℝ)
    (ha : L a = c) (hb : L b = c) :
    c * planarCross (b - a) (x - a) = planarCross a b * (c - L x) := by
  have heval (v : ℝ × ℝ) : L v = v.1 * L (1, 0) + v.2 * L (0, 1) := by
    have hv : v = v.1 • (1, 0) + v.2 • (0, 1) := by ext <;> simp
    calc
      L v = L (v.1 • (1, 0) + v.2 • (0, 1)) := congrArg L hv
      _ = _ := by rw [map_add, map_smul, map_smul]; rfl
  rw [heval] at ha hb ⊢
  change c * ((b.1 - a.1) * (x.2 - a.2) - (b.2 - a.2) * (x.1 - a.1)) =
    (a.1 * b.2 - a.2 * b.1) * (c - (x.1 * L (1, 0) + x.2 * L (0, 1)))
  linear_combination (b.2 * x.1 - b.1 * x.2) * ha +
    (a.1 * x.2 - a.2 * x.1) * hb

private theorem planar_edge_support_at
    (K : SimplicialComplex ℝ (ℝ × ℝ)) (hcv : Convex ℝ K.space)
    (z : ℝ × ℝ) (hz : z ∈ interior K.space) (a b : ℝ × ℝ)
    (he : {a, b} ∈ (K.frontierSubcomplex K.space).faces) :
    ∃ (L : (ℝ × ℝ) →ₗ[ℝ] ℝ) (c : ℝ),
      0 < c - L z ∧ L a = c ∧ L b = c ∧ ∀ x ∈ interior K.space, L x < c := by
  let t := convexHull ℝ ({a, b} : Set (ℝ × ℝ))
  have ht : Convex ℝ t := convex_convexHull ℝ _
  have hts : t ⊆ frontier K.space := by simpa only [Finset.coe_pair] using he.2
  have hdisj : Disjoint (interior K.space) t :=
    disjoint_left.mpr fun x hx hxt ↦ (hts hxt).2 hx
  obtain ⟨L, c, hLi, hLt⟩ :=
    geometric_hahn_banach_open hcv.interior isOpen_interior ht hdisj
  have hcl : ∀ x ∈ closure (interior K.space), L x ≤ c :=
    fun x hx ↦ le_on_closure (fun y hy ↦ (hLi y hy).le)
      L.continuous.continuousOn continuousOn_const hx
  have heq : closure (interior K.space) = closure K.space :=
    hcv.closure_interior_eq_closure_of_nonempty_interior ⟨z, hz⟩
  have hlevel (x : ℝ × ℝ) (hx : x ∈ t) : L x = c :=
    le_antisymm (hcl x (heq.symm ▸ (hts hx).1)) (hLt x hx)
  exact ⟨L.toLinearMap, c, sub_pos.mpr (hLi z hz),
    hlevel a (subset_convexHull ℝ _ (by simp)),
    hlevel b (subset_convexHull ℝ _ (by simp)), hLi⟩




theorem planar_boundary_coface_cross_product
    (K : SimplicialComplex ℝ (ℝ × ℝ)) (hcv : Convex ℝ K.space)
    (hzero : (0 : ℝ × ℝ) ∈ interior K.space) (a b x : ℝ × ℝ)
    (he : {a, b} ∈ (K.frontierSubcomplex K.space).faces)
    {t : Finset (ℝ × ℝ)} (ht : t ∈ K.faces) (htc : t.card = 3)
    (het : {a, b} ⊆ t) (hx : x ∈ t) (hxa : x ≠ a) (hxb : x ≠ b)
    (hd : planarCross a b ≠ 0) :
    0 < planarCross (b - a) (x - a) * planarCross a b := by
  classical
  obtain ⟨L, c, hc, hLa, hLb, hLi⟩ := planar_edge_support_at K hcv 0 hzero a b he
  simp only [map_zero, sub_zero] at hc
  have hcent : t.centroid ℝ id ∈ interior K.space :=
    interior_mono (K.convexHull_subset_space ht)
      (K.triangle_centroid_mem_interior (by simp) ht htc)
  have hgap : 0 < c - L (t.centroid ℝ id) := sub_pos.mpr (hLi _ hcent)
  have hid : K.AffineOnFaces (id : (ℝ × ℝ) → (ℝ × ℝ)) := by
    intro s hs
    exact ⟨ContinuousAffineMap.id ℝ _, fun _ _ ↦ rfl⟩
  have hab : a ≠ b := by intro h; subst b; exact hd (planarCross_self a)
  have htset : t = {x, a, b} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl | rfl
      · exact hx
      · exact het (by simp)
      · exact het (by simp)
    · simp [htc, hxa, hxb, hab]
  have hvertex := SimplicialComplex.AffineOnFaces.strict_vertex_signs_of_centroid
    K id hid t ht x (planarCross (b - a)) a (by
      intro y hy hyx
      rw [htset] at hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with hy | hy | hy
      · exact (hyx hy).elim
      · rw [hy]; simp
      · rw [hy]; exact planarCross_self (b - a))
  simp only [id_eq] at hvertex
  have hident := planarCross_support_identity L a b (t.centroid ℝ id) c hLa hLb
  rcases lt_or_gt_of_ne hd with hdneg | hdpos
  · have hcneg : planarCross (b - a) (t.centroid ℝ id - a) < 0 := by
      have hm := mul_neg_of_neg_of_pos hdneg hgap
      rw [← hident] at hm
      exact neg_of_mul_neg_right hm hc.le
    exact mul_pos_of_neg_of_neg (hvertex.1 hcneg) hdneg
  · have hcpos : 0 < planarCross (b - a) (t.centroid ℝ id - a) := by
      have hm := mul_pos hdpos hgap
      rw [← hident] at hm
      exact (mul_pos_iff_of_pos_left hc).mp hm
    exact mul_pos (hvertex.2 hcpos) hdpos





theorem exists_oriented_planar_boundary_cycle
    (K : SimplicialComplex ℝ (ℝ × ℝ)) (hK : K.faces.Finite)
    (hcv : Convex ℝ K.space) (hzero : (0 : ℝ × ℝ) ∈ interior K.space) :
    ∃ (n : ℕ) (P : Polygon (ℝ × ℝ) (n + 3))
      (edge : Fin (n + 3) ≃
        {s : Finset (ℝ × ℝ) // s ∈ (K.frontierSubcomplex K.space).faces ∧ s.card = 2})
      (coface : Fin (n + 3) → Finset (ℝ × ℝ)) (apex : Fin (n + 3) → ℝ × ℝ),
      Function.Injective P ∧ P.boundary ℝ = frontier K.space ∧
      Equiv.Perm.IsCycle (finRotate (n + 3)) ∧
      (∀ i, (edge i).val = {P i, P (finRotate (n + 3) i)}) ∧
      (∀ i, coface i ∈ K.faces ∧ (edge i).val ⊆ coface i ∧ (coface i).card = 3) ∧
      (∀ i t, t ∈ K.faces → (edge i).val ⊆ t → t.card = 3 → t = coface i) ∧
      (∀ i, apex i ∈ coface i ∧ apex i ≠ P i ∧ apex i ≠ P (finRotate (n + 3) i)) ∧
      ((∀ i, 0 < planarCross (P (finRotate (n + 3) i) - P i) (apex i - P i)) ∨
        (∀ i, planarCross (P (finRotate (n + 3) i) - P i) (apex i - P i) < 0)) := by
  classical
  obtain ⟨n, P, edge, coface, hPi, hPb, hcycle, hedge, hcoface, huniq⟩ :=
    exists_planar_boundary_dart_cycle K hK hcv ⟨0, hzero⟩
  have hapex (i : Fin (n + 3)) :
      ∃ x ∈ coface i, x ≠ P i ∧ x ≠ P (finRotate (n + 3) i) := by
    obtain ⟨x, hx, hxt⟩ := Finset.exists_eq_insert_iff.mpr
      ⟨(hcoface i).2.1, by rw [(edge i).property.2, (hcoface i).2.2]⟩
    refine ⟨x, hxt ▸ Finset.mem_insert_self _ _, ?_⟩
    simpa only [hedge i, Finset.mem_insert, Finset.mem_singleton, not_or] using hx
  choose apex hapex using hapex
  have hedges (i : Fin (n + 3)) :
      {P i, P (finRotate (n + 3) i)} ∈ (K.frontierSubcomplex K.space).faces :=
    hedge i ▸ (edge i).property.1
  have hprod (i : Fin (n + 3)) (hd : planarCross (P i) (P (finRotate (n + 3) i)) ≠ 0) :
      0 < planarCross (P (finRotate (n + 3) i) - P i) (apex i - P i) *
        planarCross (P i) (P (finRotate (n + 3) i)) :=
    planar_boundary_coface_cross_product K hcv hzero _ _ _ (hedges i)
      (hcoface i).1 (hcoface i).2.2 (hedge i ▸ (hcoface i).2.1)
      (hapex i).1 (hapex i).2.1 (hapex i).2.2 hd
  refine ⟨n, P, edge, coface, apex, hPi, hPb, hcycle, hedge, hcoface, huniq, hapex, ?_⟩
  rcases planar_boundary_cycle_uniform_direction K hcv hzero n P hPi hedges with hp | hn
  · left
    intro i
    exact (mul_pos_iff.mp (hprod i (hp i).ne')).resolve_right
      (fun h ↦ not_lt_of_ge (hp i).le h.2) |>.1
  · right
    intro i
    exact (mul_pos_iff.mp (hprod i (hn i).ne)).resolve_left
      (fun h ↦ not_lt_of_ge h.2.le (hn i)) |>.1


theorem planar_triangle_boundary_cross (p : Fin 3 → ℝ × ℝ) (i : Fin 3) :
    planarCross (p (i.succAbove 1) - p (i.succAbove 0)) (p i - p (i.succAbove 0)) =
      (-1 : ℝ) ^ i.val * planarCross (p 1 - p 0) (p 2 - p 0) := by
  fin_cases i
  · change planarCross (p 2 - p 1) (p 0 - p 1) =
      1 * planarCross (p 1 - p 0) (p 2 - p 0)
    dsimp [planarCross]
    ring
  · change planarCross (p 2 - p 0) (p 1 - p 0) =
      ((-1 : ℝ) ^ 1) * planarCross (p 1 - p 0) (p 2 - p 0)
    dsimp [planarCross]
    ring
  · change planarCross (p 1 - p 0) (p 2 - p 0) =
      ((-1 : ℝ) ^ 2) * planarCross (p 1 - p 0) (p 2 - p 0)
    ring

private theorem parity_signed_real (d : ℝ) (hd : d ≠ 0) (i : Fin 3) :
    orientationSignParity (SignType.sign ((-1 : ℝ) ^ i.val * d)) =
      orientationSignParity (SignType.sign d) + (i.val : ZMod 2) := by
  rcases lt_or_gt_of_ne hd with h | h
  · have hn := sign_neg h
    have hp := sign_pos (neg_pos.mpr h)
    fin_cases i <;> norm_num [orientationSignParity, hn, hp]
    decide
  · have hp := sign_pos h
    have hn := sign_neg (neg_neg_of_pos h)
    fin_cases i <;> norm_num [orientationSignParity, hn, hp]



theorem planar_numbered_boundary_cross_parity
    (number : (ℝ × ℝ) → ℕ) (p : Fin 3 → ℝ × ℝ)
    (hp : Function.Injective p) (hnumber : StrictMono (number ∘ p))
    (hd : planarCross (p 1 - p 0) (p 2 - p 0) ≠ 0) (i : Fin 3) :
    orientationSignParity (SignType.sign
      (planarCross (p (i.succAbove 1) - p (i.succAbove 0)) (p i - p (i.succAbove 0)))) =
      orientationSignParity (SignType.sign (planarCross (p 1 - p 0) (p 2 - p 0))) +
        Dehn.orderedCofaceParity number (Finset.univ.image p)
          (p (i.succAbove 0)) (p (i.succAbove 1)) := by
  classical
  have he : (Finset.univ.erase i).image p = {p (i.succAbove 0), p (i.succAbove 1)} := by
    ext x
    constructor
    · rintro hx
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq (Finset.mem_erase.mp hj).1
      fin_cases k <;> simp
    · intro hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact Finset.mem_image.mpr ⟨i.succAbove 0,
          Finset.mem_erase.mpr ⟨Fin.succAbove_ne i 0, Finset.mem_univ _⟩, rfl⟩
      · exact Finset.mem_image.mpr ⟨i.succAbove 1,
          Finset.mem_erase.mpr ⟨Fin.succAbove_ne i 1, Finset.mem_univ _⟩, rfl⟩
  have hpar := AbstractSimplicialComplex.boundaryFaceParity_ordered_triangle
    number p hp hnumber i
  rw [he] at hpar
  have hord : number (p (i.succAbove 0)) < number (p (i.succAbove 1)) :=
    hnumber ((Fin.strictMono_succAbove i) (by decide : (0 : Fin 2) < 1))
  rw [planar_triangle_boundary_cross, parity_signed_real _ hd i]
  simp only [Dehn.orderedCofaceParity, hpar, if_neg (not_lt_of_gt hord), add_zero]



theorem planar_numbered_boundary_cross_parity_reverse
    (number : (ℝ × ℝ) → ℕ) (p : Fin 3 → ℝ × ℝ)
    (hp : Function.Injective p) (hnumber : StrictMono (number ∘ p))
    (hd : planarCross (p 1 - p 0) (p 2 - p 0) ≠ 0) (i : Fin 3) :
    orientationSignParity (SignType.sign
      (planarCross (p (i.succAbove 0) - p (i.succAbove 1)) (p i - p (i.succAbove 1)))) =
      orientationSignParity (SignType.sign (planarCross (p 1 - p 0) (p 2 - p 0))) +
        Dehn.orderedCofaceParity number (Finset.univ.image p)
          (p (i.succAbove 1)) (p (i.succAbove 0)) := by
  classical
  have hbase := planar_numbered_boundary_cross_parity number p hp hnumber hd i
  have hcross : planarCross (p (i.succAbove 0) - p (i.succAbove 1))
      (p i - p (i.succAbove 1)) =
      -planarCross (p (i.succAbove 1) - p (i.succAbove 0)) (p i - p (i.succAbove 0)) := by
    dsimp [planarCross]
    ring
  have hnonzero : planarCross (p (i.succAbove 1) - p (i.succAbove 0))
      (p i - p (i.succAbove 0)) ≠ 0 := by
    rw [planar_triangle_boundary_cross]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hd
  have hneg := parity_signed_real _ hnonzero (1 : Fin 3)
  norm_num only [Fin.val_one, pow_one, neg_one_mul, Nat.cast_one] at hneg
  have hord : number (p (i.succAbove 0)) < number (p (i.succAbove 1)) :=
    hnumber ((Fin.strictMono_succAbove i) (by decide : (0 : Fin 2) < 1))
  have hrev := Dehn.orderedCofaceParity_reverse_of_label_ne number (Finset.univ.image p)
    hord.ne
  rw [hcross, hneg, hbase]
  linear_combination (norm := ring_nf) hrev
  simp only [show (2 : ZMod 2) = 0 from rfl, mul_zero, sub_zero]



theorem planar_numbered_edge_apex_parity
    (number : (ℝ × ℝ) → ℕ) (p : Fin 3 → ℝ × ℝ)
    (hp : Function.Injective p) (hnumber : StrictMono (number ∘ p))
    (hd : planarCross (p 1 - p 0) (p 2 - p 0) ≠ 0)
    (a b x : ℝ × ℝ) (ha : a ∈ Finset.univ.image p)
    (hb : b ∈ Finset.univ.image p) (hx : x ∈ Finset.univ.image p)
    (hab : a ≠ b) (hax : a ≠ x) (hbx : b ≠ x) :
    orientationSignParity (SignType.sign (planarCross (b - a) (x - a))) =
      orientationSignParity (SignType.sign (planarCross (p 1 - p 0) (p 2 - p 0))) +
        Dehn.orderedCofaceParity number (Finset.univ.image p) a b := by
  classical
  obtain ⟨ia, _, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨ib, _, rfl⟩ := Finset.mem_image.mp hb
  obtain ⟨ix, _, rfl⟩ := Finset.mem_image.mp hx
  have hiab : ia ≠ ib := fun h ↦ hab (congrArg p h)
  have hiax : ia ≠ ix := fun h ↦ hax (congrArg p h)
  have hibx : ib ≠ ix := fun h ↦ hbx (congrArg p h)
  fin_cases ia <;> fin_cases ib <;> fin_cases ix
  all_goals first | exact (hiab rfl).elim | exact (hiax rfl).elim | exact (hibx rfl).elim | skip
  all_goals first
    | exact planar_numbered_boundary_cross_parity number p hp hnumber hd 0
    | exact planar_numbered_boundary_cross_parity number p hp hnumber hd 1
    | exact planar_numbered_boundary_cross_parity number p hp hnumber hd 2
    | exact planar_numbered_boundary_cross_parity_reverse number p hp hnumber hd 0
    | exact planar_numbered_boundary_cross_parity_reverse number p hp hnumber hd 1
    | exact planar_numbered_boundary_cross_parity_reverse number p hp hnumber hd 2



theorem planar_paired_edge_cross_product
    (K : SimplicialComplex ℝ (ℝ × ℝ)) (a b x y : ℝ × ℝ)
    (hab : a ≠ b) (hax : a ≠ x) (hay : a ≠ y)
    (hbx : b ≠ x) (hby : b ≠ y) (hxy : x ≠ y)
    (ht : {a, x, b} ∈ K.faces) (hu : {a, b, y} ∈ K.faces) :
    planarCross (b - a) (x - a) * planarCross (b - a) (y - a) < 0 := by
  classical
  let f : (ℝ × ℝ) →ᴬ[ℝ] (ℝ × ℝ) :=
    ContinuousAffineMap.id ℝ _ - ContinuousAffineMap.const ℝ _ a
  have hf : K.AffineOnFaces f := fun s hs ↦ ⟨f, fun _ _ ↦ rfl⟩
  have hfi : InjOn f K.space := by
    intro z hz w hw hzw
    exact sub_left_injective hzw
  let C := hf.embeddedImage hfi
  have hft : {0, x - a, b - a} ∈ C.faces := by
    rw [hf.embeddedImage_faces hfi]
    refine ⟨{a, x, b}, ht, ?_⟩
    simp [f]
  have hfu : {0, b - a, y - a} ∈ C.faces := by
    rw [hf.embeddedImage_faces hfi]
    refine ⟨{a, b, y}, hu, ?_⟩
    simp [f]
  have h := paired_planar_fan_positive_product C (x - a) (b - a) (y - a)
    (sub_ne_zero.mpr hax.symm) (sub_ne_zero.mpr hab.symm) (sub_ne_zero.mpr hay.symm)
    (fun h ↦ hbx (sub_left_injective h).symm)
    (fun h ↦ hby (sub_left_injective h)) (fun h ↦ hxy (sub_left_injective h)) hft hfu
  rw [planarCross_swap (x - a) (b - a), neg_mul, neg_pos] at h
  exact h



theorem planar_sorted_cross_cancellation
    (K : SimplicialComplex ℝ (ℝ × ℝ)) (number : (ℝ × ℝ) → ℕ)
    {t u s : Finset (ℝ × ℝ)} (ht : t ∈ K.faces) (hu : u ∈ K.faces)
    (htc : t.card = 3) (huc : u.card = 3) (htu : t ≠ u)
    (hsc : s.card = 2) (hst : s ⊆ t) (hsu : s ⊆ u)
    (p q : Fin 3 → ℝ × ℝ) (hpi : Function.Injective p) (hqi : Function.Injective q)
    (hpt : Finset.univ.image p = t) (hqu : Finset.univ.image q = u)
    (hpn : StrictMono (number ∘ p)) (hqn : StrictMono (number ∘ q)) :
    (orientationSignParity (SignType.sign (planarCross (p 1 - p 0) (p 2 - p 0))) +
      AbstractSimplicialComplex.boundaryFaceParity number t s) +
      (orientationSignParity (SignType.sign (planarCross (q 1 - q 0) (q 2 - q 0))) +
        AbstractSimplicialComplex.boundaryFaceParity number u s) = 1 := by
  classical
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hsc
  obtain ⟨x, hx, hxt⟩ := Finset.exists_eq_insert_iff.mpr
    ⟨hst, by simp [hab, htc]⟩
  obtain ⟨y, hy, hyu⟩ := Finset.exists_eq_insert_iff.mpr
    ⟨hsu, by simp [hab, huc]⟩
  have hxne : x ≠ a ∧ x ≠ b := by simpa using hx
  have hyne : y ≠ a ∧ y ≠ b := by simpa using hy
  have hxy : x ≠ y := by intro h; exact htu (hxt.symm.trans (h ▸ hyu))
  have htx : {a, x, b} ∈ K.faces := by
    convert ht using 1
    rw [← hxt]
    ext z
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  have huy : {a, b, y} ∈ K.faces := by
    convert hu using 1
    rw [← hyu]
    ext z
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  have hpind : AffineIndependent ℝ p := by
    let e : Fin 3 ↪ t := ⟨fun i ↦ ⟨p i, hpt ▸ Finset.mem_image.mpr
      ⟨i, Finset.mem_univ _, rfl⟩⟩, fun i j h ↦ hpi (congrArg Subtype.val h)⟩
    exact (K.indep ht).comp_embedding e
  have hqind : AffineIndependent ℝ q := by
    let e : Fin 3 ↪ u := ⟨fun i ↦ ⟨q i, hqu ▸ Finset.mem_image.mpr
      ⟨i, Finset.mem_univ _, rfl⟩⟩, fun i j h ↦ hqi (congrArg Subtype.val h)⟩
    exact (K.indep hu).comp_embedding e
  have hpa := planar_numbered_edge_apex_parity number p hpi hpn
    (planar_triangle_cross_ne_zero p hpind) a b x
    (hpt.symm ▸ hst (by simp)) (hpt.symm ▸ hst (by simp))
    (hpt.symm ▸ hxt ▸ Finset.mem_insert_self _ _) hab hxne.1.symm hxne.2.symm
  have hqa := planar_numbered_edge_apex_parity number q hqi hqn
    (planar_triangle_cross_ne_zero q hqind) a b y
    (hqu.symm ▸ hsu (by simp)) (hqu.symm ▸ hsu (by simp))
    (hqu.symm ▸ hyu ▸ Finset.mem_insert_self _ _) hab hyne.1.symm hyne.2.symm
  have hprod := planar_paired_edge_cross_product K a b x y hab hxne.1.symm hyne.1.symm
    hxne.2.symm hyne.2.symm hxy htx huy
  have hsign : orientationSignParity (SignType.sign (planarCross (b - a) (x - a))) +
      orientationSignParity (SignType.sign (planarCross (b - a) (y - a))) = 1 := by
    rcases mul_neg_iff.mp hprod with h | h
    · rw [sign_pos h.1, sign_neg h.2]
      norm_num [orientationSignParity]
    · rw [sign_neg h.1, sign_pos h.2]
      norm_num [orientationSignParity]
  rw [hpa, hqa, hpt, hqu] at hsign
  unfold Dehn.orderedCofaceParity at hsign
  linear_combination (norm := ring_nf) hsign
  simp only [show (2 : ZMod 2) = 0 from rfl, mul_zero, neg_zero]



theorem exists_planar_sorted_cross_signs
    (K : SimplicialComplex ℝ (ℝ × ℝ)) (number : (ℝ × ℝ) → ℕ)
    (hnumber : InjOn number K.vertices) :
    ∃ (p : {t : Finset (ℝ × ℝ) // t ∈ K.faces ∧ t.card = 3} → Fin 3 → ℝ × ℝ)
      (sigma : {t : Finset (ℝ × ℝ) // t ∈ K.faces ∧ t.card = 3} → ZMod 2),
      (∀ t, Function.Injective (p t) ∧ Finset.univ.image (p t) = t.val ∧
        StrictMono (number ∘ p t) ∧ AffineIndependent ℝ (p t)) ∧
      (∀ t, sigma t = orientationSignParity
        (SignType.sign (planarCross (p t 1 - p t 0) (p t 2 - p t 0)))) ∧
      ∀ t u, t ≠ u → ∀ s : Finset (ℝ × ℝ), s.card = 2 → s ⊆ t.val → s ⊆ u.val →
        (sigma t + AbstractSimplicialComplex.boundaryFaceParity number t.val s) +
          (sigma u + AbstractSimplicialComplex.boundaryFaceParity number u.val s) = 1 := by
  classical
  have henum (t : {t : Finset (ℝ × ℝ) // t ∈ K.faces ∧ t.card = 3}) :
      ∃ p : Fin 3 → ℝ × ℝ, Function.Injective p ∧ Finset.univ.image p = t.val ∧
        StrictMono (number ∘ p) ∧ AffineIndependent ℝ p := by
    have hv (x : t.val) : (x : ℝ × ℝ) ∈ K.vertices :=
      K.down_closed t.property.1 (Finset.singleton_subset_iff.mpr x.property) (by simp)
    let nt : t.val ↪ ℕ := ⟨fun x ↦ number x, fun x y h ↦
      Subtype.ext (hnumber (hv x) (hv y) h)⟩
    obtain ⟨q, hqi, hqimage, hqn⟩ := AbstractSimplicialComplex.exists_numbered_triangle_enumeration
      nt Finset.univ (by simpa using t.property.2)
    let p : Fin 3 → ℝ × ℝ := fun i ↦ q i
    have hpi : Function.Injective p := fun i j h ↦ hqi (Subtype.ext h)
    have hpt : Finset.univ.image p = t.val := by
      change Finset.univ.image (Subtype.val ∘ q) = t.val
      rw [Finset.image_comp, hqimage]
      ext x
      simp
    have hpn : StrictMono (number ∘ p) := hqn
    let e : Fin 3 ↪ t.val := ⟨q, hqi⟩
    exact ⟨p, hpi, hpt, hpn, (K.indep t.property.1).comp_embedding e⟩
  choose p hpi hpt hpn hpind using henum
  let sigma : {t : Finset (ℝ × ℝ) // t ∈ K.faces ∧ t.card = 3} → ZMod 2 :=
    fun t ↦ orientationSignParity (SignType.sign (planarCross (p t 1 - p t 0) (p t 2 - p t 0)))
  refine ⟨p, sigma, fun t ↦ ⟨hpi t, hpt t, hpn t, hpind t⟩, fun _ ↦ rfl, ?_⟩
  intro t u htu s hsc hst hsu
  exact planar_sorted_cross_cancellation K number t.property.1 u.property.1
    t.property.2 u.property.2 (fun h ↦ htu (Subtype.ext h)) hsc hst hsu
    (p t) (p u) (hpi t) (hpi u) (hpt t) (hpt u) (hpn t) (hpn u)


theorem planar_boundary_edge_interior_cross_ne_zero
    (K : SimplicialComplex ℝ (ℝ × ℝ)) (hcv : Convex ℝ K.space)
    (z : ℝ × ℝ) (hz : z ∈ interior K.space) (a b : ℝ × ℝ) (hab : a ≠ b)
    (he : {a, b} ∈ (K.frontierSubcomplex K.space).faces) :
    planarCross (b - a) (z - a) ≠ 0 := by
  obtain ⟨L, c, hc, hLa, hLb, _⟩ := planar_edge_support_at K hcv z hz a b he
  intro hd
  have hcross : planarCross (a - z) (b - z) = 0 := by
    calc
      planarCross (a - z) (b - z) = planarCross (b - a) (z - a) := by
        dsimp [planarCross]
        ring
      _ = 0 := hd
  have hzero : planarCross (b - a) = 0 := by
    apply LinearMap.ext
    intro w
    have h := planarCross_support_identity L (a - z) (b - z) (a + w - z)
      (c - L z) (by rw [map_sub, hLa]) (by rw [map_sub, hLb])
    have hab' : (b - z) - (a - z) = b - a := by abel
    have hw : (a + w - z) - (a - z) = w := by abel
    rw [hab', hw, hcross, zero_mul] at h
    exact (mul_eq_zero.mp h).resolve_left hc.ne'
  exact planarCross_ne_zero (sub_ne_zero.mpr hab.symm) hzero



theorem planar_boundary_coface_interior_cross_product
    (K : SimplicialComplex ℝ (ℝ × ℝ)) (hcv : Convex ℝ K.space)
    (z : ℝ × ℝ) (hz : z ∈ interior K.space) (a b x : ℝ × ℝ)
    (he : {a, b} ∈ (K.frontierSubcomplex K.space).faces)
    {t : Finset (ℝ × ℝ)} (ht : t ∈ K.faces) (htc : t.card = 3)
    (het : {a, b} ⊆ t) (hx : x ∈ t) (hxa : x ≠ a) (hxb : x ≠ b)
    (hd : planarCross (b - a) (z - a) ≠ 0) :
    0 < planarCross (b - a) (x - a) * planarCross (b - a) (z - a) := by
  classical
  obtain ⟨L, c, hc, hLa, hLb, hLi⟩ := planar_edge_support_at K hcv z hz a b he
  have hcent : t.centroid ℝ id ∈ interior K.space :=
    interior_mono (K.convexHull_subset_space ht)
      (K.triangle_centroid_mem_interior (by simp) ht htc)
  have hgap : 0 < c - L (t.centroid ℝ id) := sub_pos.mpr (hLi _ hcent)
  have hident : (c - L z) * planarCross (b - a) (t.centroid ℝ id - a) =
      planarCross (b - a) (z - a) * (c - L (t.centroid ℝ id)) := by
    have h := planarCross_support_identity L (a - z) (b - z) (t.centroid ℝ id - z)
      (c - L z) (by rw [map_sub, hLa]) (by rw [map_sub, hLb])
    have hab : (b - z) - (a - z) = b - a := by abel
    have hcent : (t.centroid ℝ id - z) - (a - z) = t.centroid ℝ id - a := by abel
    have hcross : planarCross (a - z) (b - z) = planarCross (b - a) (z - a) := by
      dsimp [planarCross]
      ring
    rw [hab, hcent, hcross] at h
    simp only [map_sub] at h ⊢
    linear_combination h
  have hid : K.AffineOnFaces (id : (ℝ × ℝ) → (ℝ × ℝ)) := by
    intro s hs
    exact ⟨ContinuousAffineMap.id ℝ _, fun _ _ ↦ rfl⟩
  have hab : a ≠ b := by intro h; subst b; exact hd (by simp [planarCross])
  have htset : t = {x, a, b} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl | rfl
      · exact hx
      · exact het (by simp)
      · exact het (by simp)
    · simp [htc, hxa, hxb, hab]
  have hvertex := SimplicialComplex.AffineOnFaces.strict_vertex_signs_of_centroid
    K id hid t ht x (planarCross (b - a)) a (by
      intro y hy hyx
      rw [htset] at hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with hy | hy | hy
      · exact (hyx hy).elim
      · rw [hy]; simp
      · rw [hy]; exact planarCross_self (b - a))
  simp only [id_eq] at hvertex
  rcases lt_or_gt_of_ne hd with hdneg | hdpos
  · have hneg : planarCross (b - a) (t.centroid ℝ id - a) < 0 := by
      have hm := mul_neg_of_neg_of_pos hdneg hgap
      rw [← hident] at hm
      exact neg_of_mul_neg_right hm hc.le
    exact mul_pos_of_neg_of_neg (hvertex.1 hneg) hdneg
  · have hpos : 0 < planarCross (b - a) (t.centroid ℝ id - a) := by
      have hm := mul_pos hdpos hgap
      rw [← hident] at hm
      exact (mul_pos_iff_of_pos_left hc).mp hm
    exact mul_pos (hvertex.2 hpos) hdpos



theorem exists_coherently_oriented_planar_boundary_cycle
    (K : SimplicialComplex ℝ (ℝ × ℝ)) (hK : K.faces.Finite)
    (hcv : Convex ℝ K.space) (hzero : (0 : ℝ × ℝ) ∈ interior K.space)
    (number : (ℝ × ℝ) → ℕ) (hnumber : InjOn number K.vertices) :
    ∃ (n : ℕ) (P : Polygon (ℝ × ℝ) (n + 3))
      (edge : Fin (n + 3) ≃
        {s : Finset (ℝ × ℝ) // s ∈ (K.frontierSubcomplex K.space).faces ∧ s.card = 2})
      (coface : Fin (n + 3) → {t : Finset (ℝ × ℝ) // t ∈ K.faces ∧ t.card = 3})
      (sigma : {t : Finset (ℝ × ℝ) // t ∈ K.faces ∧ t.card = 3} → ZMod 2)
      (eps : ZMod 2),
      Function.Injective P ∧ P.boundary ℝ = frontier K.space ∧
      Equiv.Perm.IsCycle (finRotate (n + 3)) ∧
      (∀ i, (edge i).val = {P i, P (finRotate (n + 3) i)} ∧
        (edge i).val ⊆ (coface i).val) ∧
      (∀ i, sigma (coface i) + Dehn.orderedCofaceParity number (coface i).val
        (P i) (P (finRotate (n + 3) i)) = eps) ∧
      ∀ t u, t ≠ u → ∀ s : Finset (ℝ × ℝ), s.card = 2 → s ⊆ t.val → s ⊆ u.val →
        (sigma t + AbstractSimplicialComplex.boundaryFaceParity number t.val s) +
          (sigma u + AbstractSimplicialComplex.boundaryFaceParity number u.val s) = 1 := by
  classical
  obtain ⟨n, P, edge, coface, apex, hPi, hPb, hcycle, hedge, hcoface, _, hapex, hdir⟩ :=
    exists_oriented_planar_boundary_cycle K hK hcv hzero
  obtain ⟨p, sigma, hp, hsigma, hcancel⟩ := exists_planar_sorted_cross_signs K number hnumber
  let t (i : Fin (n + 3)) : {t : Finset (ℝ × ℝ) // t ∈ K.faces ∧ t.card = 3} :=
    ⟨coface i, (hcoface i).1, (hcoface i).2.2⟩
  have hpar (i : Fin (n + 3)) :
      sigma (t i) + Dehn.orderedCofaceParity number (t i).val
          (P i) (P (finRotate (n + 3) i)) =
        orientationSignParity (SignType.sign
          (planarCross (P (finRotate (n + 3) i) - P i) (apex i - P i))) := by
    rw [hsigma (t i)]
    have ha : P i ∈ Finset.univ.image (p (t i)) := by
      rw [(hp (t i)).2.1]
      exact (hcoface i).2.1 (hedge i ▸ (by simp))
    have hb : P (finRotate (n + 3) i) ∈ Finset.univ.image (p (t i)) := by
      rw [(hp (t i)).2.1]
      exact (hcoface i).2.1 (hedge i ▸ (by simp))
    have hx : apex i ∈ Finset.univ.image (p (t i)) := by
      rw [(hp (t i)).2.1]
      exact (hapex i).1
    have h := planar_numbered_edge_apex_parity number (p (t i)) (hp (t i)).1
      (hp (t i)).2.2.1 (planar_triangle_cross_ne_zero _ (hp (t i)).2.2.2)
      (P i) (P (finRotate (n + 3) i)) (apex i) ha hb hx
      (fun he ↦ rotate_ne_self n i (hPi he).symm) (hapex i).2.1.symm (hapex i).2.2.symm
    rw [(hp (t i)).2.1] at h
    exact h.symm
  rcases hdir with hpos | hneg
  · refine ⟨n, P, edge, t, sigma, 0, hPi, hPb, hcycle,
      fun i ↦ ⟨hedge i, (hcoface i).2.1⟩, ?_, hcancel⟩
    intro i
    rw [hpar i, sign_pos (hpos i)]
    rfl
  · refine ⟨n, P, edge, t, sigma, 1, hPi, hPb, hcycle,
      fun i ↦ ⟨hedge i, (hcoface i).2.1⟩, ?_, hcancel⟩
    intro i
    rw [hpar i, sign_neg (hneg i)]
    rfl

end PoincareConjecture.M76.OriginalTriangleCopies
