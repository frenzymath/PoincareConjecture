import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Geometry.Euclidean.Projection
import Mathlib.Analysis.Convex.Join
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace Poincare.Topology

variable {N m : Nat}

noncomputable def ambientAvoidanceGridPoint
    (c : EuclideanSpace Real (Fin N)) (r : Real)
    (a : Fin N -> Fin (m + 1)) : EuclideanSpace Real (Fin N) :=
  c + (EuclideanSpace.equiv (Fin N) Real).symm (fun i =>
    r / (N + 1 : Real) *
      ((2 * ((a i).val : Real) + 1) / (m + 1 : Real) - 1))

set_option maxHeartbeats 2000000 in

theorem ambient_avoidance_grid_slab_count (hN : 0 < N)
    (c u : EuclideanSpace Real (Fin N)) (hu : ‖u‖ = 1)
    (r : Real) (hr : 0 < r) (b t : Real) (ht : 0 ≤ t)
    (ht' : t ≤ r / (4 * (N + 1 : Real) ^ 2 * (m + 1 : Real))) :
    Set.ncard {a : Fin N -> Fin (m + 1) |
      |inner Real u (ambientAvoidanceGridPoint c r a) - b| ≤ t} ≤
      (m + 1) ^ (N - 1) := by
  classical
  have _ := ht
  have hn : (0 : Real) < N + 1 := by positivity
  have hm : (0 : Real) < m + 1 := by positivity
  have hul1 : ‖u‖ ≤ ∑ i, |u i| := by
    have hs : (∑ i, EuclideanSpace.single i (u i)) = u := by
      ext i
      simp [EuclideanSpace.single]
    have hh := norm_sum_le Finset.univ (fun i => EuclideanSpace.single i (u i))
    simpa [hs, EuclideanSpace.single, PiLp.norm_single, Real.norm_eq_abs] using hh
  obtain ⟨j, hj⟩ : ∃ j : Fin N, 1 / (N + 1 : Real) ≤ |u j| := by
    by_contra! h
    have hh := Finset.sum_le_sum (fun i (_hi : i ∈ (Finset.univ : Finset (Fin N))) =>
      (h i).le)
    have hsum : (∑ i, |u i|) ≤ (N : Real) * (1 / (N + 1 : Real)) := by
      simpa using hh
    have hlt : (N : Real) * (1 / (N + 1 : Real)) < 1 := by
      rw [mul_one_div, div_lt_iff₀ hn]
      linarith
    linarith
  let A : Set (Fin N -> Fin (m + 1)) :=
    {a | |inner Real u (ambientAvoidanceGridPoint c r a) - b| ≤ t}
  let drop (a : Fin N -> Fin (m + 1)) : {i : Fin N // i ≠ j} -> Fin (m + 1) :=
    fun i => a i
  have hinj : Set.InjOn drop A := by
    intro a ha a' ha' haa'
    have hrest (i : Fin N) (hi : i ≠ j) : a i = a' i :=
      congrFun haa' ⟨i, hi⟩
    by_contra hne
    have hne' : a j ≠ a' j := by
      intro heq
      apply hne
      funext i
      by_cases hi : i = j
      · simpa [hi] using heq
      · exact hrest i hi
    have hone : (1 : Real) ≤ |((a j).val : Real) - ((a' j).val : Real)| := by
      have hv : (a j).val ≠ (a' j).val := fun h => hne' (Fin.ext h)
      rcases lt_or_gt_of_ne hv with hh | hh
      · have hc : ((a j).val : Real) + 1 ≤ ((a' j).val : Real) := by
          exact_mod_cast Nat.succ_le_of_lt hh
        linarith [neg_le_abs (((a j).val : Real) - ((a' j).val : Real))]
      · have hc : ((a' j).val : Real) + 1 ≤ ((a j).val : Real) := by
          exact_mod_cast Nat.succ_le_of_lt hh
        linarith [le_abs_self (((a j).val : Real) - ((a' j).val : Real))]
    let s : Real := r / (N + 1 : Real) * (2 / (m + 1 : Real))
    have hs : 0 < s := by dsimp [s]; positivity
    have hdiff : ambientAvoidanceGridPoint c r a - ambientAvoidanceGridPoint c r a' =
        EuclideanSpace.single j (s * (((a j).val : Real) - ((a' j).val : Real))) := by
      ext i
      simp only [EuclideanSpace.single, PiLp.single_apply]
      change (c i + r / (N + 1 : Real) *
          ((2 * ((a i).val : Real) + 1) / (m + 1 : Real) - 1)) -
          (c i + r / (N + 1 : Real) *
          ((2 * ((a' i).val : Real) + 1) / (m + 1 : Real) - 1)) =
        if i = j then s * (((a j).val : Real) - ((a' j).val : Real)) else 0
      by_cases hi : i = j
      · subst i
        simp only [ite_true]
        dsimp [s]
        ring
      · rw [if_neg hi, hrest i hi]
        ring
    have hgap : s * (1 / (N + 1 : Real)) ≤
        |inner Real u (ambientAvoidanceGridPoint c r a) -
          inner Real u (ambientAvoidanceGridPoint c r a')| := by
      calc
        s * (1 / (N + 1 : Real)) ≤ s * |u j| := mul_le_mul_of_nonneg_left hj hs.le
        _ ≤ s * |((a j).val : Real) - ((a' j).val : Real)| * |u j| := by
          simpa using mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hone hs.le) (abs_nonneg (u j))
        _ = |inner Real u (ambientAvoidanceGridPoint c r a) -
            inner Real u (ambientAvoidanceGridPoint c r a')| := by
          rw [← inner_sub_right, hdiff]
          simp [EuclideanSpace.inner_single_right, abs_mul, abs_of_pos hs]
    have hclose : |inner Real u (ambientAvoidanceGridPoint c r a) -
        inner Real u (ambientAvoidanceGridPoint c r a')| ≤ 2 * t := by
      calc
        _ = |(inner Real u (ambientAvoidanceGridPoint c r a) - b) -
            (inner Real u (ambientAvoidanceGridPoint c r a') - b)| := by congr 1; ring
        _ ≤ |inner Real u (ambientAvoidanceGridPoint c r a) - b| +
            |inner Real u (ambientAvoidanceGridPoint c r a') - b| := abs_sub _ _
        _ ≤ t + t := add_le_add ha ha'
        _ = 2 * t := by ring
    have heta : 0 < r / (4 * (N + 1 : Real) ^ 2 * (m + 1 : Real)) := by positivity
    have heq : s * (1 / (N + 1 : Real)) =
        8 * (r / (4 * (N + 1 : Real) ^ 2 * (m + 1 : Real))) := by
      dsimp [s]
      field_simp
      ring
    linarith
  have hcard : Fintype.card {i : Fin N // i ≠ j} = N - 1 := by
    simp
  calc
    A.ncard ≤ (Set.univ : Set ({i : Fin N // i ≠ j} -> Fin (m + 1))).ncard :=
      Set.ncard_le_ncard_of_injOn drop (fun _ _ => Set.mem_univ _) hinj
    _ = (m + 1) ^ (N - 1) := by simp [Nat.card_eq_fintype_card, hcard]

set_option maxHeartbeats 2000000 in

theorem exists_ball_point_avoiding_affine_planes (hN : 0 < N)
    (c : EuclideanSpace Real (Fin N)) (r : Real) (hr : 0 < r)
    (P : Fin m -> AffineSubspace Real (EuclideanSpace Real (Fin N)))
    (hP : ∀ i, (P i : Set (EuclideanSpace Real (Fin N))).Nonempty)
    (hdim : ∀ i, Module.finrank Real (P i).direction < N) :
    ∃ a : Fin N -> Fin (m + 1),
      let x := ambientAvoidanceGridPoint c r a
      x ∈ Metric.ball c r ∧
      ∀ i, r / (4 * (N + 1 : Real) ^ 2 * (m + 1 : Real)) <
        Metric.infDist x (P i : Set (EuclideanSpace Real (Fin N))) := by
  classical
  have hn : (0 : Real) < N + 1 := by positivity
  have hm : (0 : Real) < m + 1 := by positivity
  let eta : Real := r / (4 * (N + 1 : Real) ^ 2 * (m + 1 : Real))
  have heta : 0 < eta := by dsimp [eta]; positivity
  have normals (i : Fin m) : ∃ u : EuclideanSpace Real (Fin N),
      ‖u‖ = 1 ∧ u ∈ (P i).directionᗮ := by
    have hdim' : Module.finrank Real (P i).direction +
        Module.finrank Real ((P i).directionᗮ) = N := by
      simpa only [finrank_euclideanSpace_fin] using
        (P i).direction.finrank_add_finrank_orthogonal
    have hd : 0 < Module.finrank Real ((P i).directionᗮ) := by
      have hi := hdim i
      omega
    let : Nontrivial ((P i).directionᗮ) := Module.nontrivial_of_finrank_pos hd
    obtain ⟨v, hv⟩ := exists_ne (0 : (P i).directionᗮ)
    have hvo : (v : EuclideanSpace Real (Fin N)) ≠ 0 := fun h => hv (Subtype.ext h)
    refine ⟨‖(v : EuclideanSpace Real (Fin N))‖⁻¹ • (v : EuclideanSpace Real (Fin N)),
      ?_, (P i).directionᗮ.smul_mem _ v.property⟩
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hvo)]
  choose u hu huo using normals
  choose p hp using hP
  let b (i : Fin m) := inner Real (u i) (p i)
  have component (i : Fin m) (x : EuclideanSpace Real (Fin N)) :
      |inner Real (u i) x - b i| ≤
        Metric.infDist x (P i : Set (EuclideanSpace Real (Fin N))) := by
    apply (Metric.le_infDist ⟨p i, hp i⟩).mpr
    intro y hy
    have horth := Submodule.inner_left_of_mem_orthogonal
      ((P i).vsub_mem_direction hy (hp i)) (huo i)
    have hconstant : inner Real (u i) y = b i := by
      dsimp [b]
      simpa only [vsub_eq_sub, inner_sub_right, sub_eq_zero] using horth
    calc
      |inner Real (u i) x - b i| = |inner Real (u i) (x - y)| := by
        rw [inner_sub_right, hconstant]
      _ ≤ ‖u i‖ * ‖x - y‖ := abs_real_inner_le_norm _ _
      _ = dist x y := by rw [hu, one_mul, dist_eq_norm]
  let B (i : Fin m) : Finset (Fin N -> Fin (m + 1)) :=
    Finset.univ.filter (fun a => |inner Real (u i) (ambientAvoidanceGridPoint c r a) - b i| ≤ eta)
  have hB (i : Fin m) : (B i).card ≤ (m + 1) ^ (N - 1) := by
    calc
      (B i).card = Set.ncard {a : Fin N -> Fin (m + 1) |
          |inner Real (u i) (ambientAvoidanceGridPoint c r a) - b i| ≤ eta} := by
        rw [← Set.ncard_coe_finset]
        congr 1
        ext a
        simp [B]
      _ ≤ (m + 1) ^ (N - 1) :=
        ambient_avoidance_grid_slab_count hN c (u i) (hu i) r hr (b i) eta heta.le le_rfl
  let bad := Finset.univ.biUnion B
  have hbad : bad.card ≤ m * (m + 1) ^ (N - 1) := by
    calc
      bad.card ≤ ∑ i : Fin m, (B i).card := Finset.card_biUnion_le
      _ ≤ ∑ _i : Fin m, (m + 1) ^ (N - 1) := Finset.sum_le_sum (fun i _ => hB i)
      _ = m * (m + 1) ^ (N - 1) := by simp
  have hlt : m * (m + 1) ^ (N - 1) < (m + 1) ^ N := by
    calc
      m * (m + 1) ^ (N - 1) < (m + 1) * (m + 1) ^ (N - 1) :=
        Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self m) (pow_pos (Nat.zero_lt_succ m) _)
      _ = (m + 1) ^ N := by rw [← pow_succ', Nat.sub_add_cancel hN]
  have htotal : bad.card < (Finset.univ : Finset (Fin N -> Fin (m + 1))).card := by
    simpa using hbad.trans_lt hlt
  obtain ⟨a, _ha, habad⟩ := Finset.exists_mem_notMem_of_card_lt_card htotal
  refine ⟨a, ?_, ?_⟩
  · rw [Metric.mem_ball, dist_eq_norm]
    let v := ambientAvoidanceGridPoint c r a - c
    have hv (i : Fin N) : |v i| < r / (N + 1 : Real) := by
      have ha0 : (0 : Real) ≤ (a i).val := by positivity
      have ha1 : ((a i).val : Real) < m + 1 := by exact_mod_cast (a i).isLt
      have habs : |(2 * ((a i).val : Real) + 1) / (m + 1 : Real) - 1| < 1 := by
        rw [abs_lt]
        constructor
        · have hp : 0 < (2 * ((a i).val : Real) + 1) / (m + 1 : Real) := by positivity
          linarith
        · have ha2 : ((a i).val : Real) ≤ m := by exact_mod_cast Nat.le_of_lt_succ (a i).isLt
          have hp : (2 * ((a i).val : Real) + 1) / (m + 1 : Real) < 2 :=
            (div_lt_iff₀ hm).mpr (by linarith)
          linarith
      change |c i + r / (N + 1 : Real) *
          ((2 * ((a i).val : Real) + 1) / (m + 1 : Real) - 1) - c i| < _
      rw [add_sub_cancel_left, abs_mul, abs_of_pos (div_pos hr hn)]
      nlinarith [div_pos hr hn]
    have hl1 : ‖v‖ ≤ ∑ i, |v i| := by
      have hs : (∑ i, EuclideanSpace.single i (v i)) = v := by
        ext i
        simp [EuclideanSpace.single]
      have hh := norm_sum_le Finset.univ (fun i => EuclideanSpace.single i (v i))
      simpa [hs, EuclideanSpace.single, PiLp.norm_single, Real.norm_eq_abs] using hh
    have hsum : (∑ i, |v i|) ≤ (N : Real) * (r / (N + 1 : Real)) := by
      simpa using Finset.sum_le_sum (fun i (_hi : i ∈ (Finset.univ : Finset (Fin N))) => (hv i).le)
    have hnr : (N : Real) * (r / (N + 1 : Real)) < r := by
      rw [← mul_div_assoc, div_lt_iff₀ hn]
      nlinarith
    exact (hl1.trans hsum).trans_lt hnr
  · intro i
    have hi : ¬ |inner Real (u i) (ambientAvoidanceGridPoint c r a) - b i| ≤ eta := by
      intro hh
      apply habad
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, by simpa [B] using hh⟩
    exact (lt_of_not_ge hi).trans_le (component i _)

set_option maxHeartbeats 1000000 in

theorem affine_join_distance_lower_bound
    (P Pstar : AffineSubspace Real (EuclideanSpace Real (Fin N)))
    (hP : (P : Set (EuclideanSpace Real (Fin N))).Nonempty) (hPP : P ≤ Pstar)
    (Q : Finset (EuclideanSpace Real (Fin N))) (hQ : Q.Nonempty)
    (hQP : ∀ q ∈ Q, q ∈ Pstar)
    (z : EuclideanSpace Real (Fin N)) (d t D : Real)
    (hd : 0 < d) (ht : 0 < t) (hD : 0 < D)
    (hsep : ∀ q ∈ convexHull Real (Q : Set (EuclideanSpace Real (Fin N))),
      d ≤ Metric.infDist q (P : Set (EuclideanSpace Real (Fin N))))
    (hz : t ≤ Metric.infDist z (Pstar : Set (EuclideanSpace Real (Fin N))))
    (hdiam : ∀ q ∈ convexHull Real (Q : Set (EuclideanSpace Real (Fin N))),
      dist z q ≤ D) :
    ∀ x ∈ convexHull Real ((insert z Q : Finset (EuclideanSpace Real (Fin N))) :
      Set (EuclideanSpace Real (Fin N))),
      d * t / (D + t) ≤ Metric.infDist x (P : Set (EuclideanSpace Real (Fin N))) := by
  classical
  have _ := hd
  let : Nonempty Pstar := (hP.mono hPP).to_subtype
  let R : EuclideanSpace Real (Fin N) →ᵃ[Real] EuclideanSpace Real (Fin N) :=
    Pstar.subtype.comp (EuclideanGeometry.orthogonalProjection Pstar).toAffineMap
  have hR (y : EuclideanSpace Real (Fin N)) :
      dist y (R y) = Metric.infDist y (Pstar : Set (EuclideanSpace Real (Fin N))) :=
    EuclideanGeometry.dist_orthogonalProjection_eq_infDist Pstar y
  have hRh (q : EuclideanSpace Real (Fin N)) (hq : q ∈ Pstar) : R q = q :=
    EuclideanGeometry.orthogonalProjection_eq_self_iff.mpr hq
  have hconv : convexHull Real (Q : Set (EuclideanSpace Real (Fin N))) ⊆ Pstar :=
    convexHull_min hQP Pstar.convex
  intro x hx
  rw [Finset.coe_insert, convexHull_insert hQ] at hx
  obtain ⟨z', hz', q, hq, hx⟩ := mem_convexJoin.mp hx
  have hez : z' = z := hz'
  subst z'
  rw [segment_symm, segment_eq_image_lineMap] at hx
  obtain ⟨a, ha, rfl⟩ := hx
  have ha0 : 0 ≤ a := ha.1
  have hRq : R q = q := hRh q (hconv hq)
  have hdistance : Metric.infDist (AffineMap.lineMap q z a)
      (Pstar : Set (EuclideanSpace Real (Fin N))) =
      a * Metric.infDist z (Pstar : Set (EuclideanSpace Real (Fin N))) := by
    rw [← hR, R.apply_lineMap, hRq, ← hR z]
    simp only [dist_eq_norm, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
    have heq : a • (z - q) + q - (a • (R z - q) + q) = a • (z - R z) := by module
    rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg ha0]
  have hmono := Metric.infDist_le_infDist_of_subset
    (x := AffineMap.lineMap q z a) hPP hP
  have hfirst : a * t ≤ Metric.infDist (AffineMap.lineMap q z a)
      (P : Set (EuclideanSpace Real (Fin N))) := by
    calc
      a * t ≤ a * Metric.infDist z (Pstar : Set (EuclideanSpace Real (Fin N))) :=
        mul_le_mul_of_nonneg_left hz ha0
      _ = Metric.infDist (AffineMap.lineMap q z a) (Pstar : Set (EuclideanSpace Real (Fin N))) :=
        hdistance.symm
      _ ≤ _ := hmono
  have hqd : dist q (AffineMap.lineMap q z a) ≤ a * D := by
    rw [dist_left_lineMap, Real.norm_eq_abs, abs_of_nonneg ha0]
    exact mul_le_mul_of_nonneg_left (by simpa [dist_comm] using hdiam q hq) ha0
  have hsecond : d - a * D ≤ Metric.infDist (AffineMap.lineMap q z a)
      (P : Set (EuclideanSpace Real (Fin N))) := by
    have hh := Metric.infDist_le_infDist_add_dist
      (s := (P : Set (EuclideanSpace Real (Fin N)))) (x := q) (y := AffineMap.lineMap q z a)
    linarith [hsep q hq]
  have hdt : 0 < D + t := by positivity
  apply (div_le_iff₀ hdt).mpr
  by_cases h : d ≤ a * (D + t)
  · have hm := mul_le_mul_of_nonneg_right hfirst hdt.le
    nlinarith [mul_le_mul_of_nonneg_left h ht.le]
  · have hh : a * (D + t) < d := lt_of_not_ge h
    have hm := mul_le_mul_of_nonneg_right hsecond hdt.le
    nlinarith [mul_nonneg hD.le (sub_nonneg.mpr hh.le)]

end Poincare.Topology
