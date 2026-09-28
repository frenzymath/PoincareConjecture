import PoincareConjecture.Proofs.M02.Topology.AmbientSimplicialGrid
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.MetricSpace.Antilipschitz
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Analysis.Normed.Affine.AddTorsor

set_option autoImplicit false

open scoped BigOperators

namespace PoincareConjecture.Proofs.M02.Topology

variable {N : Nat}

noncomputable def ambientGridMoveRatio (N : Nat) : Real := 1 / (16 * (N + 1 : Real))

set_option maxHeartbeats 4000000 in

theorem exists_ambient_grid_perturbation (h : Real) (hh : 0 < h)
    (w : (Fin N → Int) → EuclideanSpace Real (Fin N))
    (hw : ∀ z, dist (w z) (ambientGridPoint h z) ≤ ambientGridMoveRatio N * h) :
    ∃ H : EuclideanSpace Real (Fin N) ≃ₜ EuclideanSpace Real (Fin N),
      (∀ z, H (ambientGridPoint h z) = w z) ∧
      (∀ x, dist (H x) x ≤ ambientGridMoveRatio N * h) ∧
      LipschitzWith (1 / 4 : NNReal) (fun x => H x - x) ∧
      (∀ z pi, ∃ A : EuclideanSpace Real (Fin N) →ᵃ[Real]
          EuclideanSpace Real (Fin N),
        ∀ x ∈ convexHull Real (ambientGridSimplex (N := N) h z pi :
          Set (EuclideanSpace Real (Fin N))), H x = A x) := by
  classical
  let E := EuclideanSpace Real (Fin N)
  let Q := (Fin N → Int) × Equiv.Perm (Fin N)
  let C (q : Q) := convexHull Real (ambientGridSimplex h q.1 q.2 : Set E)
  have hratio : 0 < ambientGridMoveRatio N := by
    unfold ambientGridMoveRatio
    positivity
  have hinj : Function.Injective (ambientGridPoint (N := N) h) := by
    intro a b hab
    funext i
    have hi := congrArg (fun x : E => x i) hab
    change h * (a i : Real) = h * (b i : Real) at hi
    exact_mod_cast mul_left_cancel₀ hh.ne' hi
  have hc0 (z : Fin N → Int) (pi : Equiv.Perm (Fin N)) :
      ambientGridCorner h z pi 0 = ambientGridPoint h z := by
    apply congrArg (ambientGridPoint h)
    funext i
    simp
  have hsne (q : Q) : (ambientGridSimplex h q.1 q.2).Nonempty :=
    ⟨ambientGridCorner h q.1 q.2 0, Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩⟩
  have hlocal (q : Q) : ∃ A : E →ᵃ[Real] E,
      (∀ k : Fin (N + 1), A (ambientGridCorner h q.1 q.2 k) =
        w (fun i => q.1 i + if (q.2.symm i).val < k.val then 1 else 0) -
          ambientGridCorner h q.1 q.2 k) ∧ LipschitzWith (1 / 4 : NNReal) A := by
    let c := ambientGridCorner h q.1 q.2
    let d (k : Fin (N + 1)) :=
      w (fun i => q.1 i + if (q.2.symm i).val < k.val then 1 else 0) - c k
    let b (i : Fin N) : E →ᵃ[Real] Real :=
      (EuclideanSpace.projₗ (q.2 i)).toAffineMap -
        AffineMap.const Real E (h * (q.1 (q.2 i) : Real))
    let L (k : Fin (N + 1)) : E →ᵃ[Real] Real :=
      (if hk : 0 < k.val then b ⟨k.val - 1, by omega⟩ else AffineMap.const Real E h) -
        (if hk : k.val < N then b ⟨k.val, hk⟩ else 0)
    have hbval (i : Fin N) (j : Fin (N + 1)) :
        b i (c j) = if i.val < j.val then h else 0 := by
      change h * ((q.1 (q.2 i) + if (q.2.symm (q.2 i)).val < j.val then 1 else 0 : Int) : Real) -
        h * (q.1 (q.2 i) : Real) = _
      simp only [Equiv.symm_apply_apply]
      split_ifs <;> push_cast <;> ring
    have hcoeff (k j : Fin (N + 1)) :
        (if 0 < k.val then (if k.val - 1 < j.val then h else 0) else h) -
          (if k.val < N then (if k.val < j.val then h else 0) else 0) =
            if k = j then h else 0 := by
      by_cases hkj : k = j
      · subst j
        by_cases hk : 0 < k.val
        · have hp : k.val - 1 < k.val := by omega
          simp only [if_pos hk, if_pos hp, lt_self_iff_false, if_false,
            ite_self, if_true, sub_zero]
        · simp only [if_neg hk, lt_self_iff_false, if_false, ite_self, if_true, sub_zero]
      · have hne : k.val ≠ j.val := fun he => hkj (Fin.ext he)
        split_ifs <;> (try simp_all only [sub_zero, sub_self]) <;> omega
    have hL (k j : Fin (N + 1)) : L k (c j) = if k = j then h else 0 := by
      by_cases hp : 0 < k.val <;> by_cases hn : k.val < N
      · simpa only [L, dif_pos hp, dif_pos hn, AffineMap.coe_sub, Pi.sub_apply,
          hbval, Fin.val_mk, if_pos hp, if_pos hn] using hcoeff k j
      · simpa only [L, dif_pos hp, dif_neg hn, sub_zero, hbval, Fin.val_mk,
          if_pos hp, if_neg hn] using hcoeff k j
      · simpa only [L, dif_neg hp, dif_pos hn, AffineMap.coe_sub, Pi.sub_apply,
          AffineMap.const_apply, hbval, Fin.val_mk, if_neg hp, if_pos hn] using hcoeff k j
      · simpa only [L, dif_neg hp, dif_neg hn, sub_zero, AffineMap.const_apply,
          if_neg hp, if_neg hn] using hcoeff k j
    have hLd (k : Fin (N + 1)) (x y : E) : |L k x - L k y| ≤ 2 * dist x y := by
      have hb (i : Fin N) : |b i x - b i y| ≤ dist x y := by
        change |(x (q.2 i) - h * (q.1 (q.2 i) : Real)) -
          (y (q.2 i) - h * (q.1 (q.2 i) : Real))| ≤ dist x y
        simpa only [sub_sub_sub_cancel_right, Real.dist_eq] using PiLp.dist_apply_le x y (q.2 i)
      by_cases hp : 0 < k.val <;> by_cases hn : k.val < N
      · simp only [L, dif_pos hp, dif_pos hn, AffineMap.coe_sub, Pi.sub_apply]
        rw [show (b ⟨k.val - 1, _⟩ x - b ⟨k.val, _⟩ x) -
            (b ⟨k.val - 1, _⟩ y - b ⟨k.val, _⟩ y) =
            (b ⟨k.val - 1, _⟩ x - b ⟨k.val - 1, _⟩ y) -
              (b ⟨k.val, _⟩ x - b ⟨k.val, _⟩ y) by ring]
        exact (abs_sub _ _).trans (by linarith [hb ⟨k.val - 1, by omega⟩, hb ⟨k.val, hn⟩])
      · simp only [L, dif_pos hp, dif_neg hn, sub_zero]
        exact (hb ⟨k.val - 1, by omega⟩).trans (by linarith [dist_nonneg (x := x) (y := y)])
      · simp only [L, dif_neg hp, dif_pos hn, AffineMap.coe_sub, Pi.sub_apply,
          AffineMap.const_apply]
        rw [sub_sub_sub_cancel_left, abs_sub_comm]
        exact (hb ⟨k.val, hn⟩).trans (by linarith [dist_nonneg (x := x) (y := y)])
      · simp only [L, dif_neg hp, dif_neg hn, sub_zero, AffineMap.const_apply, sub_self, abs_zero]
        positivity
    let A : E →ᵃ[Real] E :=
      { toFun := fun x => h⁻¹ • ∑ k, L k x • d k
        linear := h⁻¹ • ∑ k, (L k).linear.smulRight (d k)
        map_vadd' := by
          intro x v
          change h⁻¹ • (∑ k, L k (v +ᵥ x) • d k) =
            (h⁻¹ • ∑ k, (L k).linear.smulRight (d k)) v +ᵥ
              h⁻¹ • ∑ k, L k x • d k
          simp_rw [AffineMap.map_vadd]
          simp only [vadd_eq_add, LinearMap.smul_apply, LinearMap.sum_apply,
            LinearMap.smulRight_apply, add_smul, Finset.sum_add_distrib, smul_add] }
    refine ⟨A, ?_, ?_⟩
    · intro j
      change h⁻¹ • (∑ k, L k (c j) • d k) = d j
      simp only [hL, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [smul_smul, inv_mul_cancel₀ hh.ne', one_smul]
    · apply LipschitzWith.of_dist_le_mul
      intro x y
      change ‖h⁻¹ • (∑ k, L k x • d k) - h⁻¹ • (∑ k, L k y • d k)‖ ≤
        (1 / 4 : Real) * dist x y
      rw [← smul_sub, ← Finset.sum_sub_distrib]
      simp_rw [← sub_smul]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hh)]
      have hd (k : Fin (N + 1)) : ‖d k‖ ≤ ambientGridMoveRatio N * h := by
        change ‖w (fun i => q.1 i + if (q.2.symm i).val < k.val then 1 else 0) -
          ambientGridPoint h (fun i => q.1 i + if (q.2.symm i).val < k.val then 1 else 0)‖ ≤ _
        simpa only [dist_eq_norm] using
          hw (fun i => q.1 i + if (q.2.symm i).val < k.val then 1 else 0)
      calc
        h⁻¹ * ‖∑ k, (L k x - L k y) • d k‖ ≤
            h⁻¹ * ∑ k, |L k x - L k y| * ‖d k‖ := by
          apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hh.le)
          simpa only [norm_smul, Real.norm_eq_abs] using norm_sum_le Finset.univ
            (fun k => (L k x - L k y) • d k)
        _ ≤ h⁻¹ * ∑ _k : Fin (N + 1), (2 * dist x y) * (ambientGridMoveRatio N * h) := by
          apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hh.le)
          exact Finset.sum_le_sum fun k _ =>
            mul_le_mul (hLd k x y) (hd k) (norm_nonneg _) (by positivity)
        _ = (1 / 8 : Real) * dist x y := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            Nat.cast_add, Nat.cast_one]
          unfold ambientGridMoveRatio
          field_simp [hh.ne', show (N : Real) + 1 ≠ 0 by positivity]
          ring
        _ ≤ (1 / 4 : Real) * dist x y := by linarith [dist_nonneg (x := x) (y := y)]
  let A (q : Q) := (hlocal q).choose
  have hAv (q : Q) (k : Fin (N + 1)) := (hlocal q).choose_spec.1 k
  have hAl (q : Q) : LipschitzWith (1 / 4 : NNReal) (A q) := (hlocal q).choose_spec.2
  have hpoint (q : Q) (a : Fin N → Int)
      (ha : ambientGridPoint h a ∈ ambientGridSimplex h q.1 q.2) :
      A q (ambientGridPoint h a) = w a - ambientGridPoint h a := by
    obtain ⟨k, _, hk⟩ := Finset.mem_image.mp ha
    have he : (fun i => q.1 i + if (q.2.symm i).val < k.val then 1 else 0) = a := hinj hk
    simpa only [he, hk] using hAv q k
  have hsmall (q : Q) (x : E) (hx : x ∈ C q) : ‖A q x‖ ≤ ambientGridMoveRatio N * h := by
    have hx' : A q x ∈ Metric.closedBall (0 : E) (ambientGridMoveRatio N * h) := by
      apply convexHull_min (t := (A q) ⁻¹' Metric.closedBall (0 : E) (ambientGridMoveRatio N
        * h)) ?_
        (Convex.affine_preimage (A q) (convex_closedBall _ _)) hx
      intro v hv
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hv
      change dist (A q (ambientGridCorner h q.1 q.2 k)) 0 ≤ _
      rw [dist_zero_right, hAv]
      change ‖w (fun i => q.1 i + if (q.2.symm i).val < k.val then 1 else 0) -
        ambientGridPoint h (fun i => q.1 i + if (q.2.symm i).val < k.val then 1 else 0)‖ ≤ _
      simpa only [dist_eq_norm] using
        hw (fun i => q.1 i + if (q.2.symm i).val < k.val then 1 else 0)
    simpa only [Metric.mem_closedBall, dist_zero_right] using hx'
  have hcover (x : E) : ∃ q : Q, x ∈ C q := by
    obtain ⟨B, hB⟩ := exists_nat_gt (‖x‖ / h)
    have hp : 0 < B := by
      exact_mod_cast lt_of_le_of_lt (div_nonneg (norm_nonneg x) hh.le) hB
    have hb : ‖x‖ < (B : Real) * h := (div_lt_iff₀ hh).mp hB
    obtain ⟨K, hK, _, hspace⟩ := exists_ambient_grid_complex (N := N) h hh B hp
    have hx : x ∈ K.space := by
      rw [hspace]
      intro i
      have hi : |x i| ≤ ‖x‖ := by
        simpa only [Real.dist_eq, WithLp.ofLp_zero, Pi.zero_apply, sub_zero,
          dist_zero_right, Real.norm_eq_abs] using PiLp.dist_apply_le x 0 i
      constructor <;> linarith [(abs_le.mp hi).1, (abs_le.mp hi).2]
    obtain ⟨s, hs, hxs⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx
    rw [hK] at hs
    obtain ⟨_, z, pi, _, hsub⟩ := hs
    exact ⟨⟨z, pi⟩, convexHull_mono hsub hxs⟩
  have hagree (q r : Q) (x : E) (hx : x ∈ C q) (hy : x ∈ C r) : A q x = A r x := by
    let B := (∑ i : Fin N, ((q.1 i).natAbs + (r.1 i).natAbs)) + 1
    have hbound (i : Fin N) :
        -(B : Int) ≤ q.1 i ∧ q.1 i < B ∧ -(B : Int) ≤ r.1 i ∧ r.1 i < B := by
      have hi : (q.1 i).natAbs + (r.1 i).natAbs < B :=
        Nat.lt_succ_of_le (Finset.single_le_sum
          (fun j _ => Nat.zero_le ((q.1 j).natAbs + (r.1 j).natAbs)) (Finset.mem_univ i))
      have hq : |q.1 i| < (B : Int) := by
        rw [← Int.natCast_natAbs]
        exact_mod_cast (show (q.1 i).natAbs < B by omega)
      have hr : |r.1 i| < (B : Int) := by
        rw [← Int.natCast_natAbs]
        exact_mod_cast (show (r.1 i).natAbs < B by omega)
      exact ⟨(abs_lt.mp hq).1.le, (abs_lt.mp hq).2, (abs_lt.mp hr).1.le, (abs_lt.mp hr).2⟩
    obtain ⟨K, hK, _, _⟩ := exists_ambient_grid_complex (N := N) h hh B (Nat.succ_pos _)
    have hq : ambientGridSimplex h q.1 q.2 ∈ K.faces := by
      rw [hK]
      exact ⟨hsne q, q.1, q.2, fun i => ⟨(hbound i).1, (hbound i).2.1⟩, Finset.Subset.refl _⟩
    have hr : ambientGridSimplex h r.1 r.2 ∈ K.faces := by
      rw [hK]
      exact ⟨hsne r, r.1, r.2, fun i => (hbound i).2.2, Finset.Subset.refl _⟩
    have hxy : x ∈ convexHull Real ((ambientGridSimplex h q.1 q.2 : Set E) ∩
        (ambientGridSimplex h r.1 r.2 : Set E)) := by
      rw [← K.convexHull_inter_convexHull hq hr]
      exact ⟨hx, hy⟩
    refine affineSpan_induction ((convexHull_subset_affineSpan _) hxy) ?_ ?_
    · intro v hv
      obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hv.1
      let a : Fin N → Int := fun i => q.1 i + if (q.2.symm i).val < k.val then 1 else 0
      have hpa : ambientGridPoint h a = v := hk
      rw [← hpa, hpoint q a (hpa.symm ▸ hv.1), hpoint r a (hpa.symm ▸ hv.2)]
    · intro a v y z hv hy hz
      simp only [AffineMap.map_vadd, map_smul, AffineMap.linearMap_vsub, hv, hy, hz]
  let u (x : E) := A (hcover x).choose x
  have hueq (q : Q) (x : E) (hx : x ∈ C q) : u x = A q x :=
    hagree (hcover x).choose q x (hcover x).choose_spec hx
  have husmall (x : E) : ‖u x‖ ≤ ambientGridMoveRatio N * h :=
    hsmall _ x (hcover x).choose_spec
  have huvertex (a : Fin N → Int) : u (ambientGridPoint h a) = w a - ambientGridPoint h a := by
    let q : Q := ⟨a, Equiv.refl _⟩
    have hv : ambientGridPoint h a ∈ ambientGridSimplex h q.1 q.2 := by
      rw [← hc0 a q.2]
      exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
    rw [hueq q _ (subset_convexHull Real _ hv), hpoint q a hv]

  have hul : LipschitzWith (1 / 4 : NNReal) u := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    let g := AffineMap.lineMap (k := Real) x y
    have hg : Continuous g := (_root_.lipschitzWith_lineMap x y).continuous
    let J (q : Q) : Set Real := Set.Icc 0 1 ∩ g ⁻¹' C q
    have hjcompact (q : Q) : IsCompact (J q) :=
      isCompact_Icc.inter_right
        (((ambientGridSimplex h q.1 q.2).finite_toSet.isClosed_convexHull Real).preimage hg)
    have hjconvex (q : Q) : Convex Real (J q) :=
      (convex_Icc 0 1).inter (Convex.affine_preimage g (convex_convexHull Real _))
    let S := {q : Q | (J q).Nonempty}
    have hS : S.Finite := by
      apply (ambient_grid_faces_locally_finite h hh x (dist x y)).subset
      rintro q ⟨t, ht, hqt⟩
      refine ⟨g t, hqt, ?_⟩
      apply segment_subset_closedBall_left x y
      rw [segment_eq_image_lineMap]
      exact ⟨t, ht, rfl⟩
    let lo (q : Q) := sInf (J q)
    let hi (q : Q) := sSup (J q)
    have hlo (q : Q) (hq : q ∈ S) : lo q ∈ J q := (hjcompact q).sInf_mem hq
    have hhi (q : Q) (hq : q ∈ S) : hi q ∈ J q := (hjcompact q).sSup_mem hq
    have hbetween (q : Q) (hq : q ∈ S) {t : Real} (ht : lo q ≤ t ∧ t ≤ hi q) : t ∈ J q := by
      apply (hjconvex q).ordConnected.out (hlo q hq) (hhi q hq)
      exact ht
    let T : Finset Real := {0, 1} ∪ hS.toFinset.biUnion (fun q => {lo q, hi q})
    have hT0 : (0 : Real) ∈ T := by simp [T]
    have hT1 : (1 : Real) ∈ T := by simp [T]
    have hends (q : Q) (hq : q ∈ S) : lo q ∈ T ∧ hi q ∈ T := by
      constructor <;> apply Finset.mem_union_right _ <;>
        apply Finset.mem_biUnion.mpr <;> exact ⟨q, hS.mem_toFinset.mpr hq, by simp⟩
    have hT (t : Real) (ht : t ∈ T) : t ∈ Set.Icc (0 : Real) 1 := by
      rcases Finset.mem_union.mp ht with ht | ht
      · simp only [Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl <;> constructor <;> norm_num
      · obtain ⟨q, hq, ht⟩ := Finset.mem_biUnion.mp ht
        have hq' := hS.mem_toFinset.mp hq
        simp only [Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl
        · exact (hlo q hq').1
        · exact (hhi q hq').1
    have hstep (a b : Real) (ha : a ∈ T) (hb : b ∈ T) (hab : a < b)
        (hempty : ∀ c ∈ T, ¬(a < c ∧ c < b)) :
        dist (u (g a)) (u (g b)) ≤ (1 / 4 : Real) * (b - a) * dist x y := by
      let t := (a + b) / 2
      have ht : t ∈ Set.Icc (0 : Real) 1 := by
        constructor <;> dsimp [t] <;> linarith [(hT a ha).1, (hT b hb).2]
      obtain ⟨q, hqt⟩ := hcover (g t)
      have hq : q ∈ S := ⟨t, ht, hqt⟩
      have hlo' : lo q ≤ t := csInf_le (hjcompact q).bddBelow ⟨ht, hqt⟩
      have hhi' : t ≤ hi q := le_csSup (hjcompact q).bddAbove ⟨ht, hqt⟩
      have hla : lo q ≤ a := by
        by_contra hn
        apply hempty (lo q) (hends q hq).1
        exact ⟨lt_of_not_ge hn, by dsimp [t] at hlo'; linarith⟩
      have hbh : b ≤ hi q := by
        by_contra hn
        apply hempty (hi q) (hends q hq).2
        exact ⟨by dsimp [t] at hhi'; linarith, lt_of_not_ge hn⟩
      have hqa := (hbetween q hq ⟨hla, hab.le.trans hbh⟩).2
      have hqb := (hbetween q hq ⟨hla.trans hab.le, hbh⟩).2
      rw [hueq q _ hqa, hueq q _ hqb]
      have hd := (hAl q).dist_le_mul (g a) (g b)
      rw [_root_.dist_lineMap_lineMap, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hab.le)] at hd
      norm_num at hd ⊢
      nlinarith
    have hchain : ∀ m : Nat, ∀ a b : Real, a ∈ T → b ∈ T → a ≤ b →
        (T.filter (fun t => a < t ∧ t < b)).card = m →
        dist (u (g a)) (u (g b)) ≤ (1 / 4 : Real) * (b - a) * dist x y := by
      intro m
      induction m using Nat.strong_induction_on with
      | h m ih =>
        intro a b ha hb hab hm
        rcases eq_or_lt_of_le hab with rfl | hab
        · rw [dist_self, sub_self, mul_zero, zero_mul]
        by_cases he : (T.filter (fun t => a < t ∧ t < b)).Nonempty
        · obtain ⟨c, hc⟩ := he
          have hcT := (Finset.mem_filter.mp hc).1
          have hac := (Finset.mem_filter.mp hc).2.1
          have hcb := (Finset.mem_filter.mp hc).2.2
          have hl : (T.filter (fun t => a < t ∧ t < c)).card < m := by
            rw [← hm]
            apply Finset.card_lt_card
            refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
            · intro t ht
              exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp ht).1,
                (Finset.mem_filter.mp ht).2.1, (Finset.mem_filter.mp ht).2.2.trans hcb⟩
            · intro heq
              have hmem := heq.symm ▸ hc
              exact (lt_irrefl c) (Finset.mem_filter.mp hmem).2.2
          have hr : (T.filter (fun t => c < t ∧ t < b)).card < m := by
            rw [← hm]
            apply Finset.card_lt_card
            refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
            · intro t ht
              exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp ht).1,
                hac.trans (Finset.mem_filter.mp ht).2.1, (Finset.mem_filter.mp ht).2.2⟩
            · intro heq
              have hmem := heq.symm ▸ hc
              exact (lt_irrefl c) (Finset.mem_filter.mp hmem).2.1
          have hl' := ih _ hl a c ha hcT hac.le rfl
          have hr' := ih _ hr c b hcT hb hcb.le rfl
          have hd := dist_triangle (u (g a)) (u (g c)) (u (g b))
          nlinarith
        · apply hstep a b ha hb hab
          intro c hc hmid
          exact he ⟨c, Finset.mem_filter.mpr ⟨hc, hmid⟩⟩
    have ht := hchain _ 0 1 hT0 hT1 zero_le_one rfl
    simpa only [g, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one,
      sub_zero, mul_one, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] using ht
  let F (x : E) := x + u x
  have hanti : AntilipschitzWith (4 / 3 : NNReal) F := by
    apply AntilipschitzWith.of_le_mul_dist
    intro x y
    have hu := hul.dist_le_mul x y
    have he : x - y = (F x - F y) - (u x - u y) := by dsimp [F]; abel
    have hd := norm_sub_le (F x - F y) (u x - u y)
    rw [← he] at hd
    simp only [← dist_eq_norm] at hd
    norm_num at hu ⊢
    linarith
  have hcontract (y : E) : ContractingWith (1 / 4 : NNReal) (fun x => y - u x) := by
    refine ⟨by norm_num, LipschitzWith.of_dist_le_mul fun x z => ?_⟩
    simpa only [dist_sub_left] using hul.dist_le_mul x z
  let G (y : E) := ContractingWith.fixedPoint (fun x => y - u x) (hcontract y)
  have hFG (y : E) : F (G y) = y := by
    have he := (hcontract y).fixedPoint_isFixedPt
    change y - u (G y) = G y at he
    exact (sub_eq_iff_eq_add.mp he).symm
  have hGF (x : E) : G (F x) = x := hanti.injective (hFG (F x))
  let H : E ≃ₜ E :=
    { toEquiv := ⟨F, G, hGF, hFG⟩
      continuous_toFun := continuous_id.add hul.continuous
      continuous_invFun := (hanti.to_rightInverse hFG).continuous }
  refine ⟨H, ?_, ?_, ?_, ?_⟩
  · intro a
    change ambientGridPoint h a + u (ambientGridPoint h a) = w a
    rw [huvertex, add_sub_cancel]
  · intro x
    change dist (x + u x) x ≤ _
    simpa only [dist_eq_norm, add_sub_cancel_left] using husmall x
  · change LipschitzWith (1 / 4 : NNReal) (fun x : E => x + u x - x)
    simpa only [add_sub_cancel_left] using hul
  · intro z pi
    refine ⟨AffineMap.id Real E + A ⟨z, pi⟩, ?_⟩
    intro x hx
    change x + u x = x + A ⟨z, pi⟩ x
    rw [hueq ⟨z, pi⟩ x hx]

set_option maxHeartbeats 4000000 in

theorem exists_perturbed_ambient_grid_complex (h : Real) (hh : 0 < h)
    (B : Nat) (hB : 0 < B)
    (H : EuclideanSpace Real (Fin N) ≃ₜ EuclideanSpace Real (Fin N))
    (hH : LipschitzWith (1 / 4 : NNReal) (fun x => H x - x))
    (haff : ∀ z pi, ∃ A : EuclideanSpace Real (Fin N) →ᵃ[Real]
        EuclideanSpace Real (Fin N),
      ∀ x ∈ convexHull Real (ambientGridSimplex (N := N) h z pi :
        Set (EuclideanSpace Real (Fin N))), H x = A x) :
    ∃ K : Geometry.SimplicialComplex Real (EuclideanSpace Real (Fin N)),
      K.faces = {s | ∃ t ∈ ambientGridFaces h B, s = t.image H} ∧
      Set.Finite K.faces ∧
      K.space = H '' {x | ∀ i : Fin N,
        -(B : Real) * h ≤ x i ∧ x i ≤ (B : Real) * h} ∧
      (∀ s ∈ K.faces, s.card ≤ N + 1 ∧
        Metric.diam (convexHull Real (s : Set (EuclideanSpace Real (Fin N)))) ≤
          2 * (N + 1 : Real) * h ∧
        (2 ≤ s.card → ∀ v ∈ s,
          h / 4 ≤ Metric.infDist v
            (affineSpan Real ((s.erase v : Finset (EuclideanSpace Real (Fin N))) :
              Set (EuclideanSpace Real (Fin N))) : Set (EuclideanSpace Real (Fin N))))) ∧
      (∀ v ∈ K.vertices,
        Set.ncard {s | s ∈ K.faces ∧ v ∈ s} ≤ ambientGridStarBound N) := by
  classical
  let E := EuclideanSpace Real (Fin N)
  have hglobal : LipschitzWith (5 / 4 : NNReal) H := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have hd := hH.dist_le_mul x y
    have he : H x - H y = (x - y) + ((H x - x) - (H y - y)) := by abel
    have hn := norm_add_le (x - y) ((H x - x) - (H y - y))
    rw [← he] at hn
    simp only [← dist_eq_norm] at hn
    change dist (H x - x) (H y - y) ≤ (1 / 4 : Real) * dist x y at hd
    change dist (H x) (H y) ≤ (5 / 4 : Real) * dist x y
    linarith

  have hlinear (z : Fin N → Int) (pi : Equiv.Perm (Fin N)) (A : E →ᵃ[Real] E)
      (hA : ∀ x ∈ convexHull Real (ambientGridSimplex h z pi : Set E), H x = A x) :
      ∀ v : E, ‖A.linear v - v‖ ≤ (1 / 4 : Real) * ‖v‖ := by
    let c := ambientGridCorner h z pi
    let b (i : Fin N) : E →ᵃ[Real] Real :=
      (EuclideanSpace.projₗ (pi i)).toAffineMap - AffineMap.const Real E (h * (z (pi i) : Real))
    let L (k : Fin (N + 1)) : E →ᵃ[Real] Real :=
      (if hk : 0 < k.val then b ⟨k.val - 1, by omega⟩ else AffineMap.const Real E h) -
        (if hk : k.val < N then b ⟨k.val, hk⟩ else 0)
    have hbval (i : Fin N) (j : Fin (N + 1)) : b i (c j) = if i.val < j.val then h else 0 := by
      change h * ((z (pi i) + if (pi.symm (pi i)).val < j.val then 1 else 0 : Int) : Real) -
        h * (z (pi i) : Real) = _
      simp only [Equiv.symm_apply_apply]
      split_ifs <;> push_cast <;> ring
    have hcoeff (k j : Fin (N + 1)) :
        (if 0 < k.val then (if k.val - 1 < j.val then h else 0) else h) -
          (if k.val < N then (if k.val < j.val then h else 0) else 0) =
            if k = j then h else 0 := by
      by_cases hkj : k = j
      · subst j
        by_cases hk : 0 < k.val
        · have hp : k.val - 1 < k.val := by omega
          simp only [if_pos hk, if_pos hp, lt_self_iff_false, if_false,
            ite_self, if_true, sub_zero]
        · simp only [if_neg hk, lt_self_iff_false, if_false, ite_self, if_true, sub_zero]
      · have hne : k.val ≠ j.val := fun he => hkj (Fin.ext he)
        split_ifs <;> (try simp_all only [sub_zero, sub_self]) <;> omega
    have hL (k j : Fin (N + 1)) : L k (c j) = if k = j then h else 0 := by
      by_cases hp : 0 < k.val <;> by_cases hn : k.val < N
      · simpa only [L, dif_pos hp, dif_pos hn, AffineMap.coe_sub, Pi.sub_apply,
          hbval, Fin.val_mk, if_pos hp, if_pos hn] using hcoeff k j
      · simpa only [L, dif_pos hp, dif_neg hn, sub_zero, hbval, Fin.val_mk,
          if_pos hp, if_neg hn] using hcoeff k j
      · simpa only [L, dif_neg hp, dif_pos hn, AffineMap.coe_sub, Pi.sub_apply,
          AffineMap.const_apply, hbval, Fin.val_mk, if_neg hp, if_pos hn] using hcoeff k j
      · simpa only [L, dif_neg hp, dif_neg hn, sub_zero, AffineMap.const_apply,
          if_neg hp, if_neg hn] using hcoeff k j
    have hLd (k : Fin (N + 1)) (x y : E) : |L k x - L k y| ≤ 2 * dist x y := by
      have hb (i : Fin N) : |b i x - b i y| ≤ dist x y := by
        change |(x (pi i) - h * (z (pi i) : Real)) - (y (pi i) - h * (z (pi i) : Real))| ≤ _
        simpa only [sub_sub_sub_cancel_right, Real.dist_eq] using PiLp.dist_apply_le x y (pi i)
      by_cases hp : 0 < k.val <;> by_cases hn : k.val < N
      · simp only [L, dif_pos hp, dif_pos hn, AffineMap.coe_sub, Pi.sub_apply]
        rw [show (b ⟨k.val - 1, _⟩ x - b ⟨k.val, _⟩ x) -
            (b ⟨k.val - 1, _⟩ y - b ⟨k.val, _⟩ y) =
            (b ⟨k.val - 1, _⟩ x - b ⟨k.val - 1, _⟩ y) -
              (b ⟨k.val, _⟩ x - b ⟨k.val, _⟩ y) by ring]
        exact (abs_sub _ _).trans (by linarith [hb ⟨k.val - 1, by omega⟩, hb ⟨k.val, hn⟩])
      · simp only [L, dif_pos hp, dif_neg hn, sub_zero]
        exact (hb ⟨k.val - 1, by omega⟩).trans (by linarith [dist_nonneg (x := x) (y := y)])
      · simp only [L, dif_neg hp, dif_pos hn, AffineMap.coe_sub, Pi.sub_apply,
        AffineMap.const_apply]
        rw [sub_sub_sub_cancel_left, abs_sub_comm]
        exact (hb ⟨k.val, hn⟩).trans (by linarith [dist_nonneg (x := x) (y := y)])
      · simp only [L, dif_neg hp, dif_neg hn, sub_zero, AffineMap.const_apply, sub_self, abs_zero]
        positivity
    have htel (m : Nat) (a : Fin (m + 1) → Real) :
        (∑ k : Fin m, (a k.castSucc - a k.succ)) = a 0 - a (Fin.last m) := by
      rw [Finset.sum_sub_distrib]
      have h1 := Fin.sum_univ_succ a
      have h2 := Fin.sum_univ_castSucc a
      linarith
    have htail (m : Nat) (a : Fin (m + 1) → Real) (j : Fin m) :
        (∑ k : Fin m, if j < k then a k.castSucc - a k.succ else 0) =
          a j.succ - a (Fin.last m) := by
      let a' (k : Fin (m + 1)) := if k.val ≤ j.val then a j.succ else a k
      have he (k : Fin m) : a' k.castSucc - a' k.succ =
          if j < k then a k.castSucc - a k.succ else 0 := by
        dsimp only [a']
        simp only [Fin.val_castSucc, Fin.val_succ]
        by_cases hkj : k < j
        · have hle : k.val ≤ j.val := (show k.val < j.val from hkj).le
          have hle' : k.val + 1 ≤ j.val := by change k.val < j.val at hkj; omega
          simp only [if_pos hle, if_pos hle', if_neg (not_lt_of_ge hkj.le), sub_self]
        · by_cases heq : k = j
          · subst k
            simp
          · have hlt : j < k := lt_of_le_of_ne (le_of_not_gt hkj) (Ne.symm heq)
            have hn : ¬k.val ≤ j.val := not_le_of_gt hlt
            have hn' : ¬k.val + 1 ≤ j.val := by change j.val < k.val at hlt; omega
            simp only [if_neg hn, if_neg hn', if_pos hlt]
      have hg := htel m a'
      simp only [he] at hg
      simpa [a', show ¬m ≤ j.val by omega] using hg
    let a (x : E) (k : Fin (N + 2)) : Real :=
      if hk : k.val = 0 then h else
        if hk' : k.val ≤ N then b ⟨k.val - 1, by omega⟩ x else 0
    have ha0 (x : E) : a x 0 = h := by simp [a]
    have haN (x : E) : a x (Fin.last (N + 1)) = 0 := by simp [a]
    have hLa (x : E) (k : Fin (N + 1)) : L k x = a x k.castSucc - a x k.succ := by
      by_cases hk0 : k.val = 0
      · have hk : k = 0 := Fin.ext hk0
        subst k
        by_cases hn : 0 < N <;> simp [L, a, hn, Nat.succ_le_iff]
      · have hp : 0 < k.val := Nat.pos_of_ne_zero hk0
        have hkN : k.val ≤ N := by omega
        have hks : k.val + 1 ≠ 0 := by omega
        by_cases hn : k.val < N
        · have hsn : k.val + 1 ≤ N := by omega
          simp only [L, a, Fin.val_castSucc, Fin.val_succ, dif_pos hp, dif_pos hn,
            dif_neg hk0, dif_pos hkN, dif_neg hks, dif_pos hsn, Nat.add_sub_cancel,
            AffineMap.coe_sub, Pi.sub_apply]
        · have hsn : ¬k.val + 1 ≤ N := by omega
          simp only [L, a, Fin.val_castSucc, Fin.val_succ, dif_pos hp, dif_neg hn,
            dif_neg hk0, dif_pos hkN, dif_neg hks, dif_neg hsn, Nat.add_sub_cancel, sub_zero]
    have hLs (x : E) : ∑ k, L k x = h := by
      simp_rw [hLa]
      simpa only [ha0, haN, sub_zero] using htel (N + 1) (a x)
    have hLt (x : E) (i : Fin N) :
        (∑ k : Fin (N + 1), if (pi.symm i).val < k.val then L k x else 0) =
          x i - h * (z i : Real) := by
      simp_rw [hLa]
      have ht := htail (N + 1) (a x) (pi.symm i).castSucc
      have hproj (j : Fin N) : (EuclideanSpace.projₗ j) x = x j := rfl
      simpa [a, b, hproj, Fin.lt_def,
        show (pi.symm i).val + 1 ≠ 0 by omega,
        show (pi.symm i).val + 1 ≤ N by omega] using ht
    have hLx (x : E) : ∑ k, L k x • c k = h • x := by
      ext i
      change (EuclideanSpace.projₗ i) (∑ k, L k x • c k) = h * x i
      rw [map_sum]
      simp only [map_smul, smul_eq_mul]
      calc
        ∑ k, L k x * c k i = ∑ k,
            (h * (z i : Real) * L k x + h * (if (pi.symm i).val < k.val then L k x else 0)) := by
          apply Finset.sum_congr rfl
          intro k _
          change L k x * (h * ((z i + if (pi.symm i).val < k.val then 1 else 0 : Int) : Real)) = _
          split_ifs <;> push_cast <;> ring
        _ = h * x i := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hLs, hLt]
          ring
    have hmem (x : E) (hx : ∀ k, 0 ≤ L k x) :
        x ∈ convexHull Real (ambientGridSimplex h z pi : Set E) := by
      apply mem_convexHull_of_exists_fintype (fun k => h⁻¹ * L k x) c
      · intro k
        exact mul_nonneg (inv_nonneg.mpr hh.le) (hx k)
      · rw [← Finset.mul_sum, hLs, inv_mul_cancel₀ hh.ne']
      · intro k
        exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩
      · simp_rw [mul_smul]
        rw [← Finset.smul_sum, hLx, smul_smul, inv_mul_cancel₀ hh.ne', one_smul]
    let p := Finset.univ.affineCombination Real c (fun _ => 1 / (N + 1 : Real))
    have hmass : ∑ _k : Fin (N + 1), (1 / (N + 1 : Real)) = 1 := by
      simp [show (N : Real) + 1 ≠ 0 by positivity]
    have hLp (k : Fin (N + 1)) : L k p = h / (N + 1 : Real) := by
      rw [show p = Finset.univ.affineCombination Real c (fun _ => 1 / (N + 1 : Real)) from rfl,
        Finset.univ.map_affineCombination c _ hmass (L k),
        Finset.affineCombination_eq_linear_combination _ _ _ hmass]
      simp [Function.comp_apply, hL, smul_eq_mul, mul_ite]
      ring
    have hp : p ∈ convexHull Real (ambientGridSimplex h z pi : Set E) :=
      hmem p (fun k => by rw [hLp]; positivity)
    let r : Real := h / (4 * (N + 1 : Real))
    have hr : 0 < r := by dsimp [r]; positivity
    have hrid : 4 * r = h / (N + 1 : Real) := by dsimp [r]; field_simp
    intro v
    let e : Real := r / (‖v‖ + 1)
    have he : 0 < e := div_pos hr (by positivity)
    have her : e * (‖v‖ + 1) = r := div_mul_cancel₀ r (by positivity)
    have hd : dist (p + e • v) p < r := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos he]
      nlinarith
    have hp' : p + e • v ∈ convexHull Real (ambientGridSimplex h z pi : Set E) := by
      apply hmem
      intro k
      have hk := hLd k (p + e • v) p
      rw [hLp] at hk
      have hl := (abs_le.mp hk).1
      nlinarith
    have ha : A (p + e • v) = e • A.linear v + A p := by
      simpa only [vadd_eq_add, map_smul, add_comm] using A.map_vadd p (e • v)
    have hv := hH.dist_le_mul (p + e • v) p
    rw [hA _ hp', hA _ hp, dist_eq_norm] at hv
    have heq : (A (p + e • v) - (p + e • v)) - (A p - p) =
        e • (A.linear v - v) := by rw [ha, smul_sub]; abel
    rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos he] at hv
    simp only [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos he] at hv
    norm_num at hv
    nlinarith
  have hdata (s : Finset E) (hs : s ∈ ambientGridFaces h B) :
      ∃ A : E →ᵃ[Real] E, Function.Injective A ∧
        (∀ x ∈ convexHull Real (s : Set E), H x = A x) ∧
        ∀ x y : E, (3 / 4 : Real) * dist x y ≤ dist (A x) (A y) := by
    obtain ⟨_, z, pi, _, hsub⟩ := hs
    obtain ⟨A, hA⟩ := haff z pi
    have hd (x y : E) : (3 / 4 : Real) * dist x y ≤ dist (A x) (A y) := by
      have hl := hlinear z pi A hA (x - y)
      have hn := norm_sub_le (A.linear (x - y)) (A.linear (x - y) - (x - y))
      rw [sub_sub_cancel] at hn
      have he : A.linear (x - y) = A x - A y := A.linearMap_vsub x y
      have hnorm : (3 / 4 : Real) * ‖x - y‖ ≤ ‖A.linear (x - y)‖ := by linarith
      simpa only [he, dist_eq_norm] using hnorm
    refine ⟨A, ?_, fun x hx => hA x (convexHull_mono hsub hx), hd⟩
    intro x y hxy
    have hxy' := hd x y
    rw [hxy, dist_self] at hxy'
    exact dist_eq_zero.mp (by linarith [dist_nonneg (x := x) (y := y)])
  have hhull (s : Finset E) (hs : s ∈ ambientGridFaces h B) :
      convexHull Real (s.image H : Set E) = H '' convexHull Real (s : Set E) := by
    obtain ⟨A, _, hA, _⟩ := hdata s hs
    have he : A '' (s : Set E) = H '' (s : Set E) := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x, hx, hA x (subset_convexHull Real _ hx)⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x, hx, (hA x (subset_convexHull Real _ hx)).symm⟩
    have he' : A '' convexHull Real (s : Set E) = H '' convexHull Real (s : Set E) := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x, hx, hA x hx⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x, hx, (hA x hx).symm⟩
    rw [Finset.coe_image, ← he, ← A.image_convexHull, he']
  obtain ⟨K0, hfaces, hfinite, hspace⟩ := exists_ambient_grid_complex (N := N) h hh B hB
  have hdown (s t : Finset E) (hs : s ∈ ambientGridFaces h B) (hts : t ⊆ s)
      (ht : t.Nonempty) : t ∈ ambientGridFaces h B := by
    rw [← hfaces] at hs ⊢
    exact K0.down_closed hs hts ht
  let K : Geometry.SimplicialComplex Real E :=
    { faces := {s | ∃ t ∈ ambientGridFaces h B, s = t.image H}
      isRelLowerSet_faces := by
        rintro s ⟨t, ht, rfl⟩
        refine ⟨ht.1.image H, ?_⟩
        intro v hvt hv
        let u := v.image H.symm
        have hut : u ⊆ t := by
          intro x hx
          obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
          obtain ⟨z, hz, hzy⟩ := Finset.mem_image.mp (hvt hy)
          simpa only [← hzy, H.symm_apply_apply] using hz
        refine ⟨u, hdown t u ht hut (hv.image H.symm), ?_⟩
        simp [u, Finset.image_image, Function.comp_def]
      indep := by
        rintro s ⟨t, ht, rfl⟩
        obtain ⟨A, hAi, hA, _⟩ := hdata t ht
        obtain ⟨htn, z, pi, _, hsub⟩ := ht
        have hi := (ambient_grid_simplex_geometry h hh z pi t htn hsub).1
        apply (hi.map' A hAi).range.mono
        intro x hx
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
        exact ⟨⟨v, hv⟩, (hA v (subset_convexHull Real _ hv)).symm⟩
      inter_subset_convexHull := by
        rintro s t ⟨s0, hs, rfl⟩ ⟨t0, ht, rfl⟩ x ⟨hx, hy⟩
        rw [hhull s0 hs] at hx
        rw [hhull t0 ht] at hy
        obtain ⟨a, ha, rfl⟩ := hx
        obtain ⟨b, hb, he⟩ := hy
        have hba : b = a := H.injective he
        subst b
        have hi : a ∈ convexHull Real (s0 ∩ t0 : Set E) := by
          apply K0.inter_subset_convexHull (hfaces.symm ▸ hs) (hfaces.symm ▸ ht)
          exact ⟨ha, hb⟩
        have hne : (s0 ∩ t0).Nonempty := by
          obtain ⟨b, hb⟩ := convexHull_nonempty_iff.mp ⟨a, hi⟩
          exact ⟨b, Finset.mem_inter.mpr hb⟩
        have hst := hdown s0 (s0 ∩ t0) hs Finset.inter_subset_left hne
        have heq : (s0.image H : Set E) ∩ (t0.image H : Set E) =
            ((s0 ∩ t0).image H : Set E) := by
          ext y
          constructor
          · rintro ⟨hy, hy'⟩
            obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
            obtain ⟨w, hw, he⟩ := Finset.mem_image.mp hy'
            have hwv : w = v := H.injective he
            exact Finset.mem_image.mpr ⟨v, Finset.mem_inter.mpr ⟨hv, hwv ▸ hw⟩, rfl⟩
          · intro hy
            obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
            exact ⟨Finset.mem_image.mpr ⟨v, (Finset.mem_inter.mp hv).1, rfl⟩,
              Finset.mem_image.mpr ⟨v, (Finset.mem_inter.mp hv).2, rfl⟩⟩
        rw [heq, hhull _ hst]
        exact ⟨a, by simpa only [Finset.coe_inter] using hi, rfl⟩ }
  refine ⟨K, rfl, ?_, ?_, ?_, ?_⟩
  · apply (hfinite.image (fun t : Finset E => t.image H)).subset
    rintro s ⟨t, ht, rfl⟩
    exact ⟨t, hfaces.symm ▸ ht, rfl⟩
  · ext x
    rw [Geometry.SimplicialComplex.mem_space_iff]
    constructor
    · rintro ⟨s, ⟨t, ht, rfl⟩, hx⟩
      rw [hhull t ht] at hx
      obtain ⟨a, ha, rfl⟩ := hx
      refine ⟨a, ?_, rfl⟩
      rw [← hspace]
      exact Geometry.SimplicialComplex.mem_space_iff.mpr ⟨t, hfaces.symm ▸ ht, ha⟩
    · rintro ⟨a, ha, rfl⟩
      rw [← hspace] at ha
      obtain ⟨t, ht, hat⟩ := Geometry.SimplicialComplex.mem_space_iff.mp ha
      have ht' : t ∈ ambientGridFaces h B := hfaces ▸ ht
      refine ⟨t.image H, ⟨t, ht', rfl⟩, ?_⟩
      rw [hhull t ht']
      exact ⟨a, hat, rfl⟩
  · rintro s ⟨t, ht, rfl⟩
    obtain ⟨htn, z, pi, hz, hsub⟩ := ht
    have ht' : t ∈ ambientGridFaces h B := ⟨htn, z, pi, hz, hsub⟩
    have hg := ambient_grid_simplex_geometry h hh z pi t htn hsub
    have hcard : (t.image H).card = t.card := Finset.card_image_of_injective _ H.injective
    refine ⟨by rw [hcard]; exact hg.2.1, ?_, ?_⟩
    · rw [hhull t ht']
      have hd := hglobal.diam_image_le (convexHull Real (t : Set E))
        (t.finite_toSet.isCompact_convexHull Real).isBounded
      change Metric.diam (H '' convexHull Real (t : Set E)) ≤
        (5 / 4 : Real) * Metric.diam (convexHull Real (t : Set E)) at hd
      have hn : 0 ≤ (N + 1 : Real) * h := by positivity
      linarith [hg.2.2.1]
    · intro htwo v hv
      obtain ⟨v0, hv0, rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨A, _, hA, hAd⟩ := hdata t ht'
      have htwo' : 2 ≤ t.card := by rwa [hcard] at htwo
      have halt := hg.2.2.2 htwo' v0 hv0
      have hne : (t.erase v0).Nonempty := by
        rw [← Finset.card_pos, Finset.card_erase_of_mem hv0]
        omega
      have he : H '' (t.erase v0 : Set E) = A '' (t.erase v0 : Set E) := by
        ext y
        constructor
        · rintro ⟨x, hx, rfl⟩
          exact ⟨x, hx, (hA x (subset_convexHull Real _ (Finset.mem_erase.mp hx).2)).symm⟩
        · rintro ⟨x, hx, rfl⟩
          exact ⟨x, hx, hA x (subset_convexHull Real _ (Finset.mem_erase.mp hx).2)⟩
      have hspan : (affineSpan Real (((t.image H).erase (H v0) : Finset E) : Set E) : Set E) =
          A '' (affineSpan Real (t.erase v0 : Set E) : Set E) := by
        rw [← Finset.image_erase H.injective, Finset.coe_image, he,
          ← AffineSubspace.map_span, AffineSubspace.coe_map]
      obtain ⟨w0, hw0⟩ := hne
      have hwspan : w0 ∈ affineSpan Real (t.erase v0 : Set E) := subset_affineSpan Real _ hw0
      rw [hspan]
      apply (Metric.le_infDist (x := H v0) (r := h / 4)
        (s := A '' (affineSpan Real (t.erase v0 : Set E) : Set E))
        ⟨A w0, ⟨w0, hwspan, rfl⟩⟩).2
      rintro y ⟨x, hx, rfl⟩
      rw [hA v0 (subset_convexHull Real _ hv0)]
      have hd := hAd v0 x
      have hi := Metric.infDist_le_dist_of_mem (x := v0) hx
      nlinarith
  · intro v _
    let S := {s : Finset E | s.Nonempty ∧ H.symm v ∈ s ∧
      ∃ z pi, s ⊆ ambientGridSimplex h z pi}
    have hs := ambient_grid_star_count h hh (H.symm v)
    have hsub : {s : Finset E | s ∈ K.faces ∧ v ∈ s} ⊆ (fun t : Finset E => t.image H) '' S := by
      rintro s ⟨⟨t, ht, rfl⟩, hv⟩
      obtain ⟨a, ha, hav⟩ := Finset.mem_image.mp hv
      refine ⟨t, ?_, rfl⟩
      refine ⟨ht.1, ?_, ?_⟩
      · simpa only [← hav, H.symm_apply_apply] using ha
      · obtain ⟨_, z, pi, _, hsub⟩ := ht
        exact ⟨z, pi, hsub⟩
    exact (Set.ncard_le_ncard hsub (hs.1.image _)).trans ((Set.ncard_image_le hs.1).trans hs.2)

end PoincareConjecture.Proofs.M02.Topology
