import PoincareConjecture.Proofs.M25.AppA_21_Local.LocalReturnSelection

set_option autoImplicit false
open Set Topology
open scoped Manifold ContDiff ENNReal
universe u
namespace PoincareConjecture













theorem NeckOnlyCover.exists_local_restart_with_protected_negative_end :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T3Space M] {g : RiemannianMetric 3 M},
      ∀ (H : NeckOnlyCover g), H.epsilon ≤ epsilon0 →
      ∀ (N : EpsilonNeck g), N.epsilon = H.epsilon →
        N.center ∈ H.X → ¬ H.X ⊆ N.carrier →
        let L := H.epsilon⁻¹
        Disjoint H.X (N.region (-L) (-(4 * L / 5))) →
        ∃ (P Q : EpsilonNeck g),
          P ∈ H.necks ∧ (Q = P ∨ Q = P.reverse) ∧
          Q.epsilon = H.epsilon ∧ Q.center ∈ H.X ∧
          Disjoint H.X (closure (Q.region (-L) (-(99 * L / 100)))) ∧
          (∀ V : Set M,
            H.X ∩ (N.carrier ∪ V) ⊆ Q.carrier ∪ V) ∧
          (H.X ⊆ Q.carrier ∨
            ∃ S ∈ H.necks,
              S.center ∈ H.X ∩ Q.region (-L) (-(4 * L / 5))) := by
  obtain ⟨es, hsp, hscap, select⟩ :=
    NeckOnlyCover.exists_local_return_center_alternative.{u}
  obtain ⟨el, hlp, _, runLine⟩ := EpsilonNeck.exists_signed_axial_line_control.{u}
  obtain ⟨ev, hvp, _, runSlice⟩ := EpsilonNeck.exists_buffered_slice_height_control.{u}
  obtain ⟨ep, hpp, _, composeSign⟩ := EpsilonNeck.exists_positive_cross_axis_composition.{u}
  have hden : 0 < 10000 * (Real.pi + 1) := by positivity
  refine ⟨min es (min el (min ev (min ep
    (min (1 / 10000) (1 / (10000 * (Real.pi + 1))))))),
    by positivity, (min_le_left _ _).trans hscap, ?_⟩
  intro M _ _ _ _ _ _ g H heps N heN hcenter hnot
  classical
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
  let L : ℝ := H.epsilon⁻¹
  let height (A : EpsilonNeck g) (x : M) : ℝ := (A.coordinate_inverse x).2
  let cross (A D : EpsilonNeck g) (x : M) : ℝ := D.scale *
    mvfderiv (𝓡 3) (fun y => (D.coordinate_inverse y).2) x (A.normalizedAxialVector x)
  let slab (A : EpsilonNeck g) (c d : ℝ) :=
    A.coordinate_map '' (univ ×ˢ Icc c d)
  dsimp only
  intro havoid
  have hL : 0 < L := inv_pos.mpr H.epsilon_pos
  rcases le_min_iff.mp heps with ⟨hes, heps⟩
  rcases le_min_iff.mp heps with ⟨hel, heps⟩
  rcases le_min_iff.mp heps with ⟨hev, heps⟩
  rcases le_min_iff.mp heps with ⟨hep, heps⟩
  rcases le_min_iff.mp heps with ⟨_, henumeric⟩
  have hbudget : (Real.pi + 1) * H.epsilon ≤ 1 / 10000 := by
    have h := (le_div_iff₀ hden).mp henumeric
    nlinarith only [h]
  have hpi : Real.pi ≤ L / 10000 := by
    have h := (le_div_iff₀ H.epsilon_pos).mpr hbudget
    have heq : (1 / 10000 : ℝ) / H.epsilon = L / 10000 := by
      dsimp only [L]
      ring
    rw [heq] at h
    linarith only [h]
  have small (A : EpsilonNeck g) (heA : A.epsilon = H.epsilon)
      {e : ℝ} (h : H.epsilon ≤ e) : A.epsilon ≤ e := by rw [heA]; exact h
  have interval (A : EpsilonNeck g) (heA : A.epsilon = H.epsilon)
      {s : ℝ} (hs : s ∈ Ioo (-L) L) : s ∈ Ioo (-A.epsilon⁻¹) A.epsilon⁻¹ := by
    simpa only [heA] using hs
  have coord (A : EpsilonNeck g) (heA : A.epsilon = H.epsilon)
      {x : M} (hx : x ∈ A.carrier) : height A x ∈ Ioo (-L) L := by
    simpa only [heA] using (A.coordinate_inverse_mem x hx).2
  have memSlab (A : EpsilonNeck g) {x : M} (hx : x ∈ A.carrier)
      {c d : ℝ} (hh : height A x ∈ Icc c d) : x ∈ slab A c d :=
    ⟨A.coordinate_inverse x, ⟨mem_univ _, hh⟩, A.coordinate_map_inverse hx⟩
  have slabInfo (A : EpsilonNeck g) (heA : A.epsilon = H.epsilon)
      {c d : ℝ} (hc : -L < c) (hd : d < L) :
      IsClosed (slab A c d) ∧
        ∀ x ∈ slab A c d, x ∈ A.carrier ∧ height A x ∈ Icc c d := by
    constructor
    · exact (A.isCompact_coordinate_slab (by rw [heA]; exact hc)
        (by rw [heA]; exact hd)).isClosed
    · rintro x ⟨z, hz, rfl⟩
      have hzA : z ∈ A.cylinderDomain :=
        ⟨mem_univ _, interval A heA ⟨hc.trans_le hz.2.1, hz.2.2.trans_lt hd⟩⟩
      refine ⟨A.coordinate_map_mem hzA, ?_⟩
      change (A.coordinate_inverse (A.coordinate_map z)).2 ∈ Icc c d
      rw [A.coordinate_inverse_coordinate_map hzA]
      exact hz.2

  have oneStep (A : EpsilonNeck g) (heA : A.epsilon = H.epsilon)
      (hcA : A.center ∈ H.X) (hnotA : ¬ H.X ⊆ A.carrier)
      (havoidA : Disjoint H.X (A.region (-L) (-(4 * L / 5)))) :
      ∃ (P E : EpsilonNeck g),
        P ∈ H.necks ∧ (E = P ∨ E = P.reverse) ∧ E.epsilon = H.epsilon ∧
        E.center ∈ H.X ∧
        Disjoint H.X (closure (E.region (-L) (-(99 * L / 100)))) ∧
        ∀ x ∈ H.X ∩ A.carrier,
          x ∈ E.carrier ∧ height E x ≤ height A x - 7 * L / 50 := by
    have hnegative : ¬ ∃ S ∈ H.necks, S.epsilon = H.epsilon ∧
        S.center ∈ H.X ∩ A.region (-L) (-(4 * L / 5)) := by
      rintro ⟨S, _, _, hS⟩
      exact (Set.disjoint_left.mp havoidA) hS.1 hS.2
    obtain ⟨_, P, Q0, hP, hQ0P, heP, _, hy0, hAy0, _, _, _⟩ :=
      (select H hes A heA hcA hnotA).resolve_left hnegative
    let y := Q0.center
    have hy : y ∈ H.X ∩ A.carrier := hy0
    have hAy : height A y = 3 * L / 20 := hAy0
    have hPc : P.center = y := by
      dsimp only [y]
      rcases hQ0P with rfl | rfl <;> rfl
    have hyP : y ∈ P.carrier := hPc ▸ P.central_sphere_subset P.center_on_central_sphere
    have hPzero : (P.coordinate_inverse y).2 = 0 := by
      rw [← hPc]
      exact ((P.mem_central_sphere_iff _).mp P.center_on_central_sphere).2
    let qA := (A.coordinate_inverse y).1
    have hmapA : A.coordinate_map (qA, 3 * L / 20) = y := by
      rw [← hAy]
      exact A.coordinate_map_inverse hy.2
    obtain ⟨_, _, sigma, hsigma, hsig⟩ := runSlice A P (small A heA hev)
      (heP.trans heA.symm) qA (3 * L / 20)
      (interval A heA ⟨by linarith only [hL], by linarith only [hL]⟩)
      (by rw [hmapA]; exact hyP) (by rw [hmapA, hPzero, abs_zero, heP]; positivity)
    have hsigy : 0 < sigma * cross A P y := by
      have hh := (hsig qA).2
      change 0 < sigma * cross A P (A.coordinate_map (qA, 3 * L / 20)) at hh
      rw [hmapA] at hh
      exact hh
    obtain ⟨E, hEP, heE, hEc, hEsign⟩ :
        ∃ E : EpsilonNeck g, (E = P ∨ E = P.reverse) ∧ E.epsilon = H.epsilon ∧
          E.center = y ∧ 0 < cross A E y := by
      rcases hsigma with rfl | rfl
      · exact ⟨P, Or.inl rfl, heP, hPc, by simpa only [one_mul] using hsigy⟩
      · refine ⟨P.reverse, Or.inr rfl, heP, hPc, ?_⟩
        have hneg : cross A P.reverse y = -(cross A P y) := by
          change P.scale * mvfderiv (𝓡 3) (fun x => -(P.coordinate_inverse x).2) y
            (A.normalizedAxialVector y) = _
          rw [mvfderiv_fun_neg]
          simp only [neg_apply, mul_neg, cross]
        rw [hneg]
        simpa only [neg_one_mul] using hsigy
    have hyE : y ∈ E.carrier := hEc ▸ E.central_sphere_subset E.center_on_central_sphere
    have hEzero : (E.coordinate_inverse y).2 = 0 := by
      rw [← hEc]
      exact ((E.mem_central_sphere_iff _).mp E.center_on_central_sphere).2
    have hretain (x : M) (hx : x ∈ H.X ∩ A.carrier) :
        x ∈ E.carrier ∧ height E x ≤ height A x - 7 * L / 50 := by
      let s := height A x
      let q := (A.coordinate_inverse x).1
      have hs : s ∈ Ioo (-L) L := coord A heA hx.2
      have hlow : -(4 * L / 5) ≤ s := by
        by_contra h
        exact (Set.disjoint_left.mp havoidA) hx.1
          ⟨hx.2, hs.1, lt_of_not_ge h⟩
      have hdelta : |s - 3 * L / 20| ≤ 19 * L / 20 := by
        apply abs_le.mpr
        constructor <;> linarith only [hlow, hs.2, hL]
      have hline := runLine A E (small A heA hel) (heE.trans heA.symm)
        qA (3 * L / 20) s 1 (-(97 * L / 100)) (87 * L / 100)
        (interval A heA ⟨by linarith only [hL], by linarith only [hL]⟩)
        (interval A heA hs) (Or.inl rfl)
        (by rw [hmapA]; exact hyE)
        (by rw [hmapA]; simpa only [one_mul, cross] using hEsign)
        (by rw [heE]; change -L < -(97 * L / 100); linarith only [hL])
        (by rw [heE]; change 87 * L / 100 < L; linarith only [hL]) (by
          intro t ht
          have htbox : -(4 * L / 5) ≤ t ∧ t ≤ L := by
            rcases le_total (3 * L / 20) s with h | h
            · rw [uIcc_of_le h] at ht
              constructor <;> linarith only [ht.1, ht.2, hs.2, hL]
            · rw [uIcc_of_ge h] at ht
              constructor <;> linarith only [ht.1, ht.2, hlow, hL]
          have htlen : |t - 3 * L / 20| ≤ 19 * L / 20 := by
            apply abs_le.mpr
            constructor <;> linarith only [htbox.1, htbox.2, hL]
          rw [hmapA, hEzero, zero_add, one_mul]
          constructor <;> linarith only [htbox.1, htbox.2, htlen, hL])
      have hend := hline s right_mem_uIcc
      have herr := hend.2.2.1
      rw [hmapA, hEzero, sub_zero, one_mul] at herr
      change |height E (A.coordinate_map (qA, s)) - (s - 3 * L / 20)| ≤
        (1 / 100 : ℝ) * |s - 3 * L / 20| at herr
      have hbuffer : |height E (A.coordinate_map (qA, s))| ≤ (99 / 100 : ℝ) * L := by
        apply abs_le.mpr
        constructor <;> linarith only [(abs_le.mp herr).1, (abs_le.mp herr).2,
          hdelta, hlow, hs.2, hL]
      obtain ⟨hwhole, hosc, _, _, _⟩ := runSlice A E (small A heA hev)
        (heE.trans heA.symm) qA s (interval A heA hs) hend.1 (by
          rw [heE]
          exact hbuffer)
      have hmapx : A.coordinate_map (q, s) = x := A.coordinate_map_inverse hx.2
      have hxE : x ∈ E.carrier := by simpa only [hmapx] using hwhole q
      have hh := hosc qA q
      change |height E (A.coordinate_map (q, s)) -
        height E (A.coordinate_map (qA, s))| ≤ Real.pi at hh
      rw [hmapx] at hh
      refine ⟨hxE, ?_⟩
      change height E x ≤ s - 7 * L / 50
      linarith only [(abs_le.mp hh).2, (abs_le.mp herr).2, hdelta, hpi, hL]
    have hreciprocal := (composeSign A A E (small A heA hep) (small A heA hep)
      (small E heE hep) y hy.2 hy.2 hyE
      (by simpa only [A.normalizedAxialVector_axial_mvfderiv hy.2] using
        (zero_lt_one : (0 : ℝ) < 1)) hEsign).2
    let qE := (E.coordinate_inverse y).1
    have hmapE : E.coordinate_map (qE, 0) = y := by
      rw [← hEzero]
      exact E.coordinate_map_inverse hyE
    obtain ⟨hwhole, hosc, rho, hrho, hsign⟩ := runSlice E A (small E heE hev)
      (heA.trans heE.symm) qE 0 (interval E heE ⟨by linarith only [hL], hL⟩)
      (by rw [hmapE]; exact hy.2) (by
        rw [hmapE, heA]
        change |height A y| ≤ (99 / 100 : ℝ) * L
        rw [hAy, abs_of_pos (by positivity : 0 < 3 * L / 20)]
        linarith only [hL])
    have hrhoOne : rho = 1 := by
      rcases hrho with rfl | rfl
      · rfl
      · have hbad := (hsign qE).2
        rw [hmapE] at hbad
        change 0 < (-1 : ℝ) * cross E A y at hbad
        change 0 < cross E A y at hreciprocal
        exfalso
        linarith only [hbad, hreciprocal]
    subst rho
    have hcentral (q : UnitTwoSphere) :
        E.coordinate_map (q, 0) ∈ A.carrier ∧
          ((1499 / 10000 : ℝ) * L ≤ height A (E.coordinate_map (q, 0)) ∧
            height A (E.coordinate_map (q, 0)) ≤ (1501 / 10000 : ℝ) * L) ∧
          0 < cross E A (E.coordinate_map (q, 0)) := by
      refine ⟨hwhole q, ?_, by simpa only [one_mul, cross] using (hsign q).2⟩
      have hh := hosc qE q
      change |height A (E.coordinate_map (q, 0)) -
        height A (E.coordinate_map (qE, 0))| ≤ Real.pi at hh
      rw [hmapE, hAy] at hh
      constructor <;> linarith only [(abs_le.mp hh).1, (abs_le.mp hh).2, hpi]
    let Kneg := slab A (-(87 * L / 100)) (-(82 * L / 100))
    have hKneg := slabInfo A heA (c := -(87 * L / 100)) (d := -(82 * L / 100))
      (by linarith only [hL]) (by linarith only [hL])
    have htail : E.region (-L) (-(99 * L / 100)) ⊆ Kneg := by
      intro x hx
      let q := (E.coordinate_inverse x).1
      let s := height E x
      have hs : s ∈ Ioo (-L) (-(99 * L / 100)) := hx.2
      have hsL : s ∈ Ioo (-L) L := ⟨hs.1, by linarith only [hs.2, hL]⟩
      have hmap : E.coordinate_map (q, s) = x := E.coordinate_map_inverse hx.1
      have hc := hcentral q
      have hline := runLine E A (small E heE hel) (heA.trans heE.symm)
        q 0 s 1 (-(87 * L / 100)) (L / 5)
        (interval E heE ⟨by linarith only [hL], hL⟩) (interval E heE hsL)
        (Or.inl rfl) hc.1 (by simpa only [one_mul, cross] using hc.2.2)
        (by rw [heA]; change -L < -(87 * L / 100); linarith only [hL])
        (by rw [heA]; change L / 5 < L; linarith only [hL]) (by
          intro t ht
          rw [uIcc_of_ge (by linarith only [hs.2, hL] : s ≤ 0)] at ht
          rw [sub_zero, one_mul, abs_of_nonpos ht.2]
          change -(87 * L / 100) ≤ height A (E.coordinate_map (q, 0)) +
              t - (1 / 100 : ℝ) * (-t) ∧
            height A (E.coordinate_map (q, 0)) + t + (1 / 100 : ℝ) * (-t) ≤ L / 5
          constructor <;> linarith only [hc.2.1.1, hc.2.1.2, ht.1, ht.2, hs.1, hL])
      have hend := hline s right_mem_uIcc
      have hxinA : x ∈ A.carrier := by simpa only [hmap] using hend.1
      have hh := hend.2.2.1
      rw [hmap, sub_zero, one_mul,
        abs_of_neg (by linarith only [hs.2, hL] : s < 0)] at hh
      change |height A x - height A (E.coordinate_map (q, 0)) - s| ≤
        (1 / 100 : ℝ) * (-s) at hh
      apply memSlab A hxinA
      constructor <;> linarith only [(abs_le.mp hh).1, (abs_le.mp hh).2,
        hc.2.1.1, hc.2.1.2, hs.1, hs.2, hL]
    have hprotected : Disjoint H.X (closure (E.region (-L) (-(99 * L / 100)))) := by
      apply Set.disjoint_left.mpr
      intro x hxX hx
      obtain ⟨hxA, hh⟩ := hKneg.2 x (closure_minimal htail hKneg.1 hx)
      apply (Set.disjoint_left.mp havoidA) hxX
      refine ⟨hxA, ?_, ?_⟩
      · change -L < height A x
        linarith only [hh.1, hL]
      · change height A x < -(4 * L / 5)
        linarith only [hh.2, hL]
    refine ⟨P, E, hP, hEP, heE, ?_, hprotected, hretain⟩
    rw [hEc]
    exact hy.1

  by_contra hfinish
  have noStop (P Q : EpsilonNeck g) (hP : P ∈ H.necks)
      (hQP : Q = P ∨ Q = P.reverse) (heQ : Q.epsilon = H.epsilon)
      (hcQ : Q.center ∈ H.X)
      (hprotected : Disjoint H.X (closure (Q.region (-L) (-(99 * L / 100)))))
      (hkeep : H.X ∩ N.carrier ⊆ Q.carrier) :
      ¬ H.X ⊆ Q.carrier ∧ Disjoint H.X (Q.region (-L) (-(4 * L / 5))) := by
    have hV (V : Set M) : H.X ∩ (N.carrier ∪ V) ⊆ Q.carrier ∪ V := by
      intro x hx
      rcases hx.2 with hxN | hxV
      · exact Or.inl (hkeep ⟨hx.1, hxN⟩)
      · exact Or.inr hxV
    constructor
    · intro hcovered
      exact hfinish ⟨P, Q, hP, hQP, heQ, hcQ, hprotected, hV, Or.inl hcovered⟩
    · apply Set.disjoint_left.mpr
      intro x hxX hxneg
      obtain ⟨S, hS, hSc⟩ := H.pointwise_center_cover x hxX
      apply hfinish
      refine ⟨P, Q, hP, hQP, heQ, hcQ, hprotected, hV, Or.inr ⟨S, hS, ?_⟩⟩
      rw [hSc]
      exact ⟨hxX, hxneg⟩
  let State (n : ℕ) : Prop := ∃ P Q : EpsilonNeck g,
    P ∈ H.necks ∧ (Q = P ∨ Q = P.reverse) ∧ Q.epsilon = H.epsilon ∧
      Q.center ∈ H.X ∧
      Disjoint H.X (closure (Q.region (-L) (-(99 * L / 100)))) ∧
      (H.X ∩ N.carrier ⊆ Q.carrier) ∧
      height Q N.center ≤ -(((n : ℝ) + 1) * (7 * L / 50))
  have hx0 : N.center ∈ H.X ∩ N.carrier :=
    ⟨hcenter, N.central_sphere_subset N.center_on_central_sphere⟩
  have hzero : height N N.center = 0 :=
    ((N.mem_central_sphere_iff _).mp N.center_on_central_sphere).2
  have states (n : ℕ) : State n := by
    induction n with
    | zero =>
      obtain ⟨P, Q, hP, hQP, heQ, hcQ, hprotected, hkeep⟩ :=
        oneStep N heN hcenter hnot havoid
      refine ⟨P, Q, hP, hQP, heQ, hcQ, hprotected, fun x hx => (hkeep x hx).1, ?_⟩
      have hh := (hkeep N.center hx0).2
      rw [hzero] at hh
      simpa only [Nat.cast_zero, zero_add, one_mul, zero_sub] using hh
    | succ n ih =>
      obtain ⟨P, Q, hP, hQP, heQ, hcQ, hprotected, hkeep, hbound⟩ := ih
      obtain ⟨hnQ, havQ⟩ := noStop P Q hP hQP heQ hcQ hprotected hkeep
      obtain ⟨P', E, hP', hEP', heE, hcE, hprotectedE, hstep⟩ :=
        oneStep Q heQ hcQ hnQ havQ
      refine ⟨P', E, hP', hEP', heE, hcE, hprotectedE,
        fun x hx => (hstep x ⟨hx.1, hkeep hx⟩).1, ?_⟩
      calc
        height E N.center ≤ height Q N.center - 7 * L / 50 :=
          (hstep N.center ⟨hcenter, hkeep hx0⟩).2
        _ ≤ -(((n : ℝ) + 1) * (7 * L / 50)) - 7 * L / 50 :=
          sub_le_sub_right hbound _
        _ = -((((n + 1 : ℕ) : ℝ) + 1) * (7 * L / 50)) := by
          rw [Nat.cast_add, Nat.cast_one]
          ring
  obtain ⟨P, Q, hP, hQP, heQ, hcQ, hprotected, hkeep, hbound⟩ := states 5
  have hxQ : N.center ∈ Q.carrier := hkeep hx0
  have hnegative : N.center ∈ Q.region (-L) (-(4 * L / 5)) := by
    refine ⟨hxQ, (coord Q heQ hxQ).1, ?_⟩
    change height Q N.center < -(4 * L / 5)
    norm_num only [Nat.cast_ofNat] at hbound
    linarith only [hbound, hL]
  exact (Set.disjoint_left.mp (noStop P Q hP hQP heQ hcQ hprotected hkeep).2)
    hcenter hnegative

end PoincareConjecture
