import PoincareConjecture.Proofs.M25.AppA_1_Necks.AxialLineContinuation
import PoincareConjecture.Proofs.M25.AppA_1_Necks.BufferedSliceHeight
import PoincareConjecture.Proofs.M25.AppA_1_Necks.AxialSignComposition
import PoincareConjecture.Proofs.M25.AppA_1_Necks.Reversal
import Mathlib.Topology.Connected.Basic

set_option autoImplicit false
open Set Topology
open scoped Manifold ContDiff ENNReal
universe u
namespace PoincareConjecture

theorem NeckOnlyCover.exists_local_return_center_alternative :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T3Space M] {g : RiemannianMetric 3 M},
      ∀ (H : NeckOnlyCover g), H.epsilon ≤ epsilon0 →
      ∀ (N : EpsilonNeck g), N.epsilon = H.epsilon →
      N.center ∈ H.X → ¬ H.X ⊆ N.carrier →
        let L := H.epsilon⁻¹
        let A := N.region (-L) (-(4 * L / 5))
        (∃ P ∈ H.necks, P.epsilon = H.epsilon ∧
          P.center ∈ H.X ∩ A) ∨
        (Disjoint H.X A ∧
          ∃ (P Q : EpsilonNeck g),
            P ∈ H.necks ∧ (Q = P ∨ Q = P.reverse) ∧
            P.epsilon = H.epsilon ∧ Q.epsilon = H.epsilon ∧
            Q.center ∈ H.X ∩ N.carrier ∧
            (N.coordinate_inverse Q.center).2 = 3 * L / 20 ∧
            N.carrier \ A ⊆ Q.region (-(49 * L / 50)) (49 * L / 50) ∧
            closure (Q.region (-L) (-(99 * L / 100))) ⊆
              N.region (-(9 * L / 10)) (-(4 * L / 5)) ∧
            ∀ V : Set M,
              H.X ∩ (N.carrier ∪ V) ⊆ Q.carrier ∪ V) := by
  obtain ⟨es, hsp, hscap, hscale⟩ :=
    EpsilonNeck.exists_intersecting_scale_control.{u} (α := (1 / 1000 : ℝ))
      (by norm_num)
  obtain ⟨el, hlp, _, runLine⟩ := EpsilonNeck.exists_signed_axial_line_control.{u}
  obtain ⟨ev, hvp, _, runSlice⟩ := EpsilonNeck.exists_buffered_slice_height_control.{u}
  obtain ⟨ep, hpp, _, composeSign⟩ := EpsilonNeck.exists_positive_cross_axis_composition.{u}
  let B0 : ℝ := Real.sqrt 2 * (Real.pi + 1)
  have hB0 : 0 < B0 := by dsimp only [B0]; positivity
  have hden : 0 < 10000 * (B0 + Real.pi + 1) := by positivity
  refine ⟨min es (min el (min ev (min ep
    (min (1 / 10000) (1 / (10000 * (B0 + Real.pi + 1))))))),
    by positivity, (min_le_left _ _).trans hscap, ?_⟩
  intro M _ _ _ _ _ _ g H heps N heN hcenter hnot
  classical
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
  let L : ℝ := H.epsilon⁻¹
  let A := N.region (-L) (-(4 * L / 5))
  let height (E : EpsilonNeck g) (x : M) : ℝ := (E.coordinate_inverse x).2
  let cross (E D : EpsilonNeck g) (x : M) : ℝ := D.scale *
    mvfderiv (𝓡 3) (fun y => (D.coordinate_inverse y).2) x (E.normalizedAxialVector x)
  let slab (E : EpsilonNeck g) (c d : ℝ) :=
    E.coordinate_map '' (univ ×ˢ Icc c d)
  dsimp only
  have hL : 0 < L := inv_pos.mpr H.epsilon_pos
  by_cases hmeet : (H.X ∩ A).Nonempty
  · left
    obtain ⟨x, hxX, hxA⟩ := hmeet
    obtain ⟨P, hP, hPc⟩ := H.pointwise_center_cover x hxX
    refine ⟨P, hP, H.neck_epsilon P hP, ?_⟩
    rw [hPc]
    exact ⟨hxX, hxA⟩
  right
  have havoid : Disjoint H.X A := Set.disjoint_left.mpr fun x hxX hxA =>
    hmeet ⟨x, hxX, hxA⟩
  refine ⟨havoid, ?_⟩
  rcases le_min_iff.mp heps with ⟨hes, heps⟩
  rcases le_min_iff.mp heps with ⟨hel, heps⟩
  rcases le_min_iff.mp heps with ⟨hev, heps⟩
  rcases le_min_iff.mp heps with ⟨hep, heps⟩
  rcases le_min_iff.mp heps with ⟨hesmall, henumeric⟩
  have small (E : EpsilonNeck g) (heE : E.epsilon = H.epsilon)
      {e : ℝ} (h : H.epsilon ≤ e) : E.epsilon ≤ e := by rw [heE]; exact h
  have interval (E : EpsilonNeck g) (heE : E.epsilon = H.epsilon)
      {s : ℝ} (hs : s ∈ Ioo (-L) L) : s ∈ Ioo (-E.epsilon⁻¹) E.epsilon⁻¹ := by
    simpa only [heE] using hs
  have coord (E : EpsilonNeck g) (heE : E.epsilon = H.epsilon)
      {x : M} (hx : x ∈ E.carrier) : height E x ∈ Ioo (-L) L := by
    simpa only [heE] using (E.coordinate_inverse_mem x hx).2
  have memSlab (E : EpsilonNeck g) {x : M} (hx : x ∈ E.carrier)
      {c d : ℝ} (hh : height E x ∈ Icc c d) : x ∈ slab E c d :=
    ⟨E.coordinate_inverse x, ⟨mem_univ _, hh⟩, E.coordinate_map_inverse hx⟩
  have slabInfo (E : EpsilonNeck g) (heE : E.epsilon = H.epsilon)
      {c d : ℝ} (hc : -L < c) (hd : d < L) :
      IsClosed (slab E c d) ∧
        ∀ x ∈ slab E c d, x ∈ E.carrier ∧ height E x ∈ Icc c d := by
    constructor
    · exact (E.isCompact_coordinate_slab (by rw [heE]; exact hc)
        (by rw [heE]; exact hd)).isClosed
    · rintro x ⟨z, hz, rfl⟩
      have hzE : z ∈ E.cylinderDomain :=
        ⟨mem_univ _, interval E heE ⟨hc.trans_le hz.2.1, hz.2.2.trans_lt hd⟩⟩
      refine ⟨E.coordinate_map_mem hzE, ?_⟩
      change (E.coordinate_inverse (E.coordinate_map z)).2 ∈ Icc c d
      rw [E.coordinate_inverse_coordinate_map hzE]
      exact hz.2

  have hyexists : ∃ y ∈ H.X ∩ N.carrier, height N y = 3 * L / 20 := by
    by_contra hnone
    let O := N.region (-(9 * L / 10)) (3 * L / 20)
    let K := slab N (-(9 * L / 10)) (3 * L / 20)
    have hK := slabInfo N heN (c := -(9 * L / 10)) (d := 3 * L / 20)
      (by linarith only [hL]) (by linarith only [hL])
    have hOK : O ⊆ K := fun x hx => memSlab N hx.1 ⟨hx.2.1.le, hx.2.2.le⟩
    have hclosureK : closure O ⊆ K := closure_minimal hOK hK.1
    have hside : closure O ∩ H.X ⊆ O := by
      intro x hx
      obtain ⟨hxN, hh⟩ := hK.2 x (hclosureK hx.1)
      have hlow : -(4 * L / 5) ≤ height N x := by
        by_contra h
        exact (Set.disjoint_left.mp havoid) hx.2
          ⟨hxN, (coord N heN hxN).1, lt_of_not_ge h⟩
      have hne : height N x ≠ 3 * L / 20 := fun h => hnone ⟨x, ⟨hx.2, hxN⟩, h⟩
      refine ⟨hxN, ?_, ?_⟩
      · change -(9 * L / 10) < height N x
        linarith only [hlow, hL]
      · rcases lt_or_eq_of_le hh.2 with hlt | heq
        · exact hlt
        · exact False.elim (hne heq)
    have hc := (N.mem_central_sphere_iff N.center).mp N.center_on_central_sphere
    have hcO : N.center ∈ O := by
      refine ⟨hc.1, ?_⟩
      rw [hc.2]
      constructor <;> linarith only [hL]
    have hXO : H.X ⊆ O := H.connected_X.isPreconnected.subset_of_closure_inter_subset
      (N.isOpen_region _ _) ⟨N.center, hcenter, hcO⟩ hside
    exact hnot (fun _ hx => (hXO hx).1)
  obtain ⟨y, hy, hNy⟩ := hyexists
  obtain ⟨P, hP, hPc⟩ := H.pointwise_center_cover y hy.1
  have heP : P.epsilon = H.epsilon := H.neck_epsilon P hP
  have hyP : y ∈ P.carrier := hPc ▸ P.central_sphere_subset P.center_on_central_sphere
  have hPzero : (P.coordinate_inverse y).2 = 0 := by
    rw [← hPc]
    exact ((P.mem_central_sphere_iff _).mp P.center_on_central_sphere).2
  have hbudget : (B0 + Real.pi + 1) * H.epsilon ≤ 1 / 10000 := by
    have h := (le_div_iff₀ hden).mp henumeric
    nlinarith only [h]
  have hnumeric : B0 ≤ L / 10000 ∧ Real.pi ≤ L / 10000 := by
    have h := (le_div_iff₀ H.epsilon_pos).mpr hbudget
    have heq : (1 / 10000 : ℝ) / H.epsilon = L / 10000 := by dsimp only [L]; ring
    rw [heq] at h
    constructor <;> linarith only [h, hB0, Real.pi_pos]
  have hsqlo : (999 : ℝ) / 1000 ≤ Real.sqrt (1 - H.epsilon) :=
    Real.le_sqrt_of_sq_le (by nlinarith only [hesmall])
  have hsqhi : Real.sqrt (1 + H.epsilon) ≤ (1001 : ℝ) / 1000 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by nlinarith only [hesmall]⟩
  have hsqpos : 0 < Real.sqrt (1 - H.epsilon) := by linarith only [hsqlo]
  let d := P.scale * Real.sqrt (1 - H.epsilon)
  have hdpos : 0 < d := mul_pos P.scale_pos hsqpos
  have hratio := (hscale P N (small P heP hes) (small N heN hes) ⟨y, hyP, hy.2⟩).2
  have hscaleNP : N.scale ≤ (1001 / 1000 : ℝ) * P.scale := by
    apply (div_le_iff₀ P.scale_pos).mp
    linarith only [(abs_lt.mp hratio).2]
  have hcoeff : N.scale * Real.sqrt (1 + H.epsilon) ≤ (101 / 100 : ℝ) * d := by
    calc
      _ ≤ ((1001 / 1000 : ℝ) * P.scale) * (1001 / 1000) :=
        mul_le_mul hscaleNP hsqhi (Real.sqrt_nonneg _)
          (mul_nonneg (by norm_num) P.scale_pos.le)
      _ ≤ _ := by
        have h := mul_le_mul_of_nonneg_left hsqlo P.scale_pos.le
        change P.scale * (999 / 1000 : ℝ) ≤ d at h
        linarith only [h, P.scale_pos]
  have hdepthy : P.axialDepth y = L := by
    simp only [EpsilonNeck.axialDepth, if_pos hyP, heP, hPzero, abs_zero, sub_zero]
    rfl
  have hretainP : N.carrier \ A ⊆ P.region (-(49 * L / 50)) (49 * L / 50) := by
    intro x hx
    have hxcoord := coord N heN hx.1
    have hlow : -(4 * L / 5) ≤ height N x := by
      by_contra h
      exact hx.2 ⟨hx.1, hxcoord.1, lt_of_not_ge h⟩
    have hdelta : |height N y - height N x| ≤ 19 * L / 20 := by
      rw [hNy]
      apply abs_le.mpr
      constructor <;> linarith only [hlow, hxcoord.2, hL]
    have hdist := N.edist_le_axial_add hx.1 hy.2
    rw [heN] at hdist
    have hupper : N.scale * Real.sqrt (1 + H.epsilon) *
        (|height N y - height N x| + B0) ≤ d * ((959601 / 1000000 : ℝ) * L) := by
      calc
        _ ≤ ((101 / 100 : ℝ) * d) * (|height N y - height N x| + B0) :=
          mul_le_mul_of_nonneg_right hcoeff (add_nonneg (abs_nonneg _) hB0.le)
        _ ≤ ((101 / 100 : ℝ) * d) * (19 * L / 20 + B0) :=
          mul_le_mul_of_nonneg_left (add_le_add hdelta le_rfl) (by positivity)
        _ ≤ ((101 / 100 : ℝ) * d) * (19 * L / 20 + L / 10000) :=
          mul_le_mul_of_nonneg_left (add_le_add le_rfl hnumeric.1) (by positivity)
        _ = _ := by ring
    have hdist' : g.edist x y < ENNReal.ofReal (d * (49 * L / 50)) := by
      apply (hdist.trans (ENNReal.ofReal_le_ofReal hupper)).trans_lt
      apply (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
      exact mul_lt_mul_of_pos_left (by linarith only [hL]) hdpos
    have hdepth := P.axialDepth_edist_le x y
    rw [heP, hdepthy] at hdepth
    change ENNReal.ofReal (d * |P.axialDepth x - L|) ≤ g.edist x y at hdepth
    have habs : |P.axialDepth x - L| < 49 * L / 50 := by
      have hh := (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mp
        (hdepth.trans_lt hdist')
      exact (mul_lt_mul_iff_right₀ hdpos).mp hh
    have hxP : x ∈ P.carrier := by
      by_contra hout
      have hh := habs
      simp only [EpsilonNeck.axialDepth, if_neg hout, zero_sub, abs_neg,
        abs_of_pos hL] at hh
      linarith only [hh, hL]
    have hform : P.axialDepth x - L = -|height P x| := by
      simp only [EpsilonNeck.axialDepth, if_pos hxP, heP]
      change L - |height P x| - L = -|height P x|
      ring
    rw [hform, abs_neg, abs_abs] at habs
    exact ⟨hxP, (abs_lt.mp habs).1, (abs_lt.mp habs).2⟩
  let qN := (N.coordinate_inverse y).1
  have hmapN : N.coordinate_map (qN, 3 * L / 20) = y := by
    rw [← hNy]
    exact N.coordinate_map_inverse hy.2
  obtain ⟨_, _, sigma, hsigma, hsig⟩ := runSlice N P (small N heN hev)
    (heP.trans heN.symm) qN (3 * L / 20)
    (interval N heN ⟨by linarith only [hL], by linarith only [hL]⟩)
    (by rw [hmapN]; exact hyP) (by rw [hmapN, hPzero, abs_zero, heP]; positivity)
  have hsigy : 0 < sigma * cross N P y := by
    have hh := (hsig qN).2
    change 0 < sigma * cross N P (N.coordinate_map (qN, 3 * L / 20)) at hh
    rw [hmapN] at hh
    exact hh
  obtain ⟨Q, hQP, heQ, hQc, hQsign⟩ :
      ∃ Q : EpsilonNeck g, (Q = P ∨ Q = P.reverse) ∧ Q.epsilon = H.epsilon ∧
        Q.center = y ∧ 0 < cross N Q y := by
    rcases hsigma with rfl | rfl
    · exact ⟨P, Or.inl rfl, heP, hPc, by simpa only [one_mul] using hsigy⟩
    · refine ⟨P.reverse, Or.inr rfl, heP, hPc, ?_⟩
      have hneg : cross N P.reverse y = -(cross N P y) := by
        change P.scale * mvfderiv (𝓡 3) (fun x => -(P.coordinate_inverse x).2) y
          (N.normalizedAxialVector y) = _
        rw [mvfderiv_fun_neg]
        simp only [neg_apply, mul_neg, cross]
      rw [hneg]
      simpa only [neg_one_mul] using hsigy
  have hyQ : y ∈ Q.carrier := hQc ▸ Q.central_sphere_subset Q.center_on_central_sphere
  have hQzero : (Q.coordinate_inverse y).2 = 0 := by
    rw [← hQc]
    exact ((Q.mem_central_sphere_iff _).mp Q.center_on_central_sphere).2
  have hreciprocal := (composeSign N N Q (small N heN hep) (small N heN hep)
    (small Q heQ hep) y hy.2 hy.2 hyQ
    (by simpa only [N.normalizedAxialVector_axial_mvfderiv hy.2] using
      (zero_lt_one : (0 : ℝ) < 1)) hQsign).2
  let qQ := (Q.coordinate_inverse y).1
  have hmapQ : Q.coordinate_map (qQ, 0) = y := by
    rw [← hQzero]
    exact Q.coordinate_map_inverse hyQ
  obtain ⟨hwhole, hosc, rho, hrho, hsign⟩ := runSlice Q N (small Q heQ hev)
    (heN.trans heQ.symm) qQ 0 (interval Q heQ ⟨by linarith only [hL], hL⟩)
    (by rw [hmapQ]; exact hy.2) (by
      rw [hmapQ, heN]
      change |height N y| ≤ (99 / 100 : ℝ) * L
      rw [hNy, abs_of_pos (by positivity : 0 < 3 * L / 20)]
      linarith only [hL])
  have hrhoOne : rho = 1 := by
    rcases hrho with rfl | rfl
    · rfl
    · have hbad := (hsign qQ).2
      rw [hmapQ] at hbad
      change 0 < (-1 : ℝ) * cross Q N y at hbad
      change 0 < cross Q N y at hreciprocal
      exfalso
      linarith only [hbad, hreciprocal]
  subst rho
  have hcentral (q : UnitTwoSphere) :
      Q.coordinate_map (q, 0) ∈ N.carrier ∧
        ((1499 / 10000 : ℝ) * L ≤ height N (Q.coordinate_map (q, 0)) ∧
          height N (Q.coordinate_map (q, 0)) ≤ (1501 / 10000 : ℝ) * L) ∧
        0 < cross Q N (Q.coordinate_map (q, 0)) := by
    refine ⟨hwhole q, ?_, by simpa only [one_mul, cross] using (hsign q).2⟩
    have hh := hosc qQ q
    change |height N (Q.coordinate_map (q, 0)) -
      height N (Q.coordinate_map (qQ, 0))| ≤ Real.pi at hh
    rw [hmapQ, hNy] at hh
    constructor <;> linarith only [(abs_le.mp hh).1, (abs_le.mp hh).2, hnumeric.2]
  have hretainQ : N.carrier \ A ⊆ Q.region (-(49 * L / 50)) (49 * L / 50) := by
    rcases hQP with h | h
    · rw [h]
      exact hretainP
    · rw [h, P.reverse_region]
      simpa only [neg_neg] using hretainP

  let Kneg := slab N (-(87 * L / 100)) (-(82 * L / 100))
  have hKneg := slabInfo N heN (c := -(87 * L / 100)) (d := -(82 * L / 100))
    (by linarith only [hL]) (by linarith only [hL])
  have htail : Q.region (-L) (-(99 * L / 100)) ⊆ Kneg := by
    intro x hx
    let q := (Q.coordinate_inverse x).1
    let s := height Q x
    have hs : s ∈ Ioo (-L) (-(99 * L / 100)) := hx.2
    have hsL : s ∈ Ioo (-L) L := ⟨hs.1, by linarith only [hs.2, hL]⟩
    have hmap : Q.coordinate_map (q, s) = x := Q.coordinate_map_inverse hx.1
    have hc := hcentral q
    have hline := runLine Q N (small Q heQ hel) (heN.trans heQ.symm)
      q 0 s 1 (-(87 * L / 100)) (L / 5)
      (interval Q heQ ⟨by linarith only [hL], hL⟩) (interval Q heQ hsL)
      (Or.inl rfl) hc.1 (by simpa only [one_mul, cross] using hc.2.2)
      (by rw [heN]; change -L < -(87 * L / 100); linarith only [hL])
      (by rw [heN]; change L / 5 < L; linarith only [hL]) (by
        intro t ht
        rw [uIcc_of_ge (by linarith only [hs.2, hL] : s ≤ 0)] at ht
        rw [sub_zero, one_mul, abs_of_nonpos ht.2]
        change -(87 * L / 100) ≤ height N (Q.coordinate_map (q, 0)) +
            t - (1 / 100 : ℝ) * (-t) ∧
          height N (Q.coordinate_map (q, 0)) + t + (1 / 100 : ℝ) * (-t) ≤ L / 5
        constructor <;> linarith only [hc.2.1.1, hc.2.1.2, ht.1, ht.2, hs.1, hL])
    have hend := hline s right_mem_uIcc
    have hxinN : x ∈ N.carrier := by simpa only [hmap] using hend.1
    have hh := hend.2.2.1
    rw [hmap, sub_zero, one_mul,
      abs_of_neg (by linarith only [hs.2, hL] : s < 0)] at hh
    change |height N x - height N (Q.coordinate_map (q, 0)) - s| ≤
      (1 / 100 : ℝ) * (-s) at hh
    apply memSlab N hxinN
    constructor <;> linarith only [(abs_le.mp hh).1, (abs_le.mp hh).2,
      hc.2.1.1, hc.2.1.2, hs.1, hs.2, hL]
  have htailclosure : closure (Q.region (-L) (-(99 * L / 100))) ⊆
      N.region (-(9 * L / 10)) (-(4 * L / 5)) := by
    intro x hx
    obtain ⟨hxN, hh⟩ := hKneg.2 x (closure_minimal htail hKneg.1 hx)
    refine ⟨hxN, ?_, ?_⟩
    · change -(9 * L / 10) < height N x
      linarith only [hh.1, hL]
    · change height N x < -(4 * L / 5)
      linarith only [hh.2, hL]
  refine ⟨P, Q, hP, hQP, heP, heQ, ?_, ?_, hretainQ, htailclosure, ?_⟩
  · rw [hQc]
    exact hy
  · rw [hQc]
    exact hNy
  · intro V x hx
    rcases hx.2 with hxN | hxV
    · exact Or.inl ((hretainQ ⟨hxN, fun hxA =>
        (Set.disjoint_left.mp havoid) hx.1 hxA⟩).1)
    · exact Or.inr hxV

end PoincareConjecture
