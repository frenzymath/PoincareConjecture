import PoincareConjecture.Proofs.M25.AppA_20_Fibration.ReturnOverlapGeometry

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

theorem BalancedNeckChain.exists_closing_strip_boundary_avoidance :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T3Space M] {g : RiemannianMetric 3 M} {epsilon : ℝ},
      ∀ (C : BalancedNeckChain g epsilon), epsilon ≤ epsilon0 →
      ∀ a b : ℤ, C.shape = ChainShape.finite a b →
        let L := epsilon⁻¹
        let N := C.neck a
        let B := C.neck b
        let U : Set M := ⋃ i ∈ C.shape.active, (C.neck i).carrier
        ∀ (Rh Q : EpsilonNeck g), Rh.epsilon = epsilon →
          Q.epsilon = epsilon →
          Rh.center ∈ closure (B.region 0 L) → Rh.center ∉ U →
          ∀ (f hN hR : UnitTwoSphere → ℝ),
            (∀ q, -(3 * L / 10) < f q ∧ f q < -(L / 5)) →
            (∀ q, -(9 * L / 10) < hN q ∧ hN q < -(4 * L / 5)) →
            (∀ q, -(L / 5) < hR q ∧ hR q < 19 * L / 20) →
            Set.range (fun q : UnitTwoSphere =>
              B.coordinate_map (q, 3 * L / 4)) =
              Set.range (fun q : UnitTwoSphere =>
                Rh.coordinate_map (q, f q)) →
            Set.range (fun q : UnitTwoSphere =>
              N.coordinate_map (q, hN q)) =
              Set.range (fun q : UnitTwoSphere => Q.coordinate_map (q, 0)) →
            Set.range (fun q : UnitTwoSphere =>
              Rh.coordinate_map (q, hR q)) =
              Set.range (fun q : UnitTwoSphere => Q.coordinate_map (q, -L / 4)) →
            (∀ q : UnitTwoSphere,
              0 < N.scale * mvfderiv (𝓡 3)
                (fun x => (N.coordinate_inverse x).2) (Q.coordinate_map (q, 0))
                (Q.normalizedAxialVector (Q.coordinate_map (q, 0)))) →
            (∀ q : UnitTwoSphere,
              0 < Rh.scale * mvfderiv (𝓡 3)
                (fun x => (Rh.coordinate_inverse x).2)
                (Q.coordinate_map (q, -L / 4))
                (Q.normalizedAxialVector (Q.coordinate_map (q, -L / 4)))) →
            Disjoint
              (Rh.coordinate_map ''
                {z : RoundCylinderSpace | f z.1 < z.2 ∧ z.2 < hR z.1})
              (Set.range (fun q : UnitTwoSphere => N.coordinate_map (q, hN q))) ∧
            Disjoint
              (Q.coordinate_map '' (Set.univ ×ˢ Set.Icc (-L / 4) 0))
              (Set.range (fun q : UnitTwoSphere =>
                B.coordinate_map (q, 3 * L / 4))) := by
  obtain ⟨ej, hjpos, hjcap, hj⟩ :=
    BalancedNeckChain.exists_oriented_frontier_initial_height_control.{u}
  obtain ⟨el, hlpos, _, runLine⟩ := EpsilonNeck.exists_signed_axial_line_control.{u}
  obtain ⟨ep, hppos, _, composeSign⟩ := EpsilonNeck.exists_positive_cross_axis_composition.{u}
  obtain ⟨eo, hopos, _, horient⟩ :=
    EpsilonNeck.exists_intersecting_coherent_orientation.{u} (η := (1 / 1000 : ℝ))
      (by constructor <;> norm_num)
  refine ⟨min ej (min el (min ep eo)),
    lt_min hjpos (lt_min hlpos (lt_min hppos hopos)), (min_le_left _ _).trans hjcap, ?_⟩
  intro M _ _ _ _ _ _ g epsilon C hepsilon a b hshape
  classical
  rcases le_min_iff.mp hepsilon with ⟨hej, hepsilon⟩
  rcases le_min_iff.mp hepsilon with ⟨hel, hepsilon⟩
  rcases le_min_iff.mp hepsilon with ⟨hep, heo⟩
  let L : ℝ := epsilon⁻¹
  let N := C.neck a
  let B := C.neck b
  let U : Set M := ⋃ i ∈ C.shape.active, (C.neck i).carrier
  let height (A : EpsilonNeck g) (x : M) : ℝ := (A.coordinate_inverse x).2
  let cross (A D : EpsilonNeck g) (x : M) : ℝ := D.scale *
    mvfderiv (𝓡 3) (fun y => (D.coordinate_inverse y).2) x (A.normalizedAxialVector x)
  let F : M → ℝ := fun x => if x ∈ N.carrier then height N x else L
  dsimp only
  intro Rh Q heRh heQ hy hout f hN hR hf hhN hhR hgraph hSm hS2 hsignN hsignR
  have hactive (i : ℤ) : i ∈ C.shape.active ↔ i ∈ Icc a b := by rw [hshape]; rfl
  have hab : a ≤ b := by
    obtain ⟨i, hi⟩ := C.active_nonempty
    exact ((hactive i).mp hi).1.trans ((hactive i).mp hi).2
  have ha : a ∈ C.shape.active := (hactive a).mpr ⟨le_rfl, hab⟩
  have heN : N.epsilon = epsilon := C.epsilon_eq a ha
  have hepos : 0 < epsilon := heN ▸ N.epsilon_pos
  have hL : 0 < L := inv_pos.mpr hepos
  have small (A : EpsilonNeck g) (heA : A.epsilon = epsilon)
      {e : ℝ} (he : epsilon ≤ e) : A.epsilon ≤ e := by rw [heA]; exact he
  have interval (A : EpsilonNeck g) (heA : A.epsilon = epsilon)
      {s : ℝ} (hs : s ∈ Ioo (-L) L) : s ∈ Ioo (-A.epsilon⁻¹) A.epsilon⁻¹ := by
    simpa only [heA] using hs
  have dom (A : EpsilonNeck g) (heA : A.epsilon = epsilon)
      {q : UnitTwoSphere} {s : ℝ} (hs : s ∈ Ioo (-L) L) :
      (q, s) ∈ A.cylinderDomain := ⟨mem_univ _, interval A heA hs⟩
  have heightAt (A : EpsilonNeck g) (heA : A.epsilon = epsilon)
      (q : UnitTwoSphere) {s : ℝ} (hs : s ∈ Ioo (-L) L) :
      height A (A.coordinate_map (q, s)) = s :=
    congrArg Prod.snd (A.coordinate_inverse_map (q, s) (interval A heA hs))
  have hfdom (q : UnitTwoSphere) : f q ∈ Ioo (-L) L :=
    ⟨by linarith only [hL, (hf q).1], by linarith only [hL, (hf q).2]⟩
  have hNdom (q : UnitTwoSphere) : hN q ∈ Ioo (-L) L :=
    ⟨by linarith only [hL, (hhN q).1], by linarith only [hL, (hhN q).2]⟩
  have hRdom (q : UnitTwoSphere) : hR q ∈ Ioo (-L) L :=
    ⟨by linarith only [hL, (hhR q).1], by linarith only [hL, (hhR q).2]⟩
  have hzero : (0 : ℝ) ∈ Ioo (-L) L := ⟨neg_lt_zero.mpr hL, hL⟩
  have hquarter : -L / 4 ∈ Ioo (-L) L :=
    ⟨by linarith only [hL], by linarith only [hL]⟩
  have pointSign (A D : EpsilonNeck g) (heA : A.epsilon = epsilon)
      (heD : D.epsilon = epsilon) (x : M) (hxA : x ∈ A.carrier) (hxD : x ∈ D.carrier) :
      ∃ sigma : ℝ, (sigma = 1 ∨ sigma = -1) ∧ 0 < sigma * cross A D x := by
    obtain ⟨sigma, hsigma, hc⟩ := horient A D (small A heA heo) (small D heD heo)
      {A.coordinate_inverse x} isPreconnected_singleton (by
        intro z hz
        rw [mem_singleton_iff.mp hz]
        refine ⟨A.coordinate_inverse_mem x hxA, ?_⟩
        change A.coordinate_map (A.coordinate_inverse x) ∈ D.carrier
        rw [A.coordinate_map_inverse hxA]
        exact hxD)
    have h := hc (A.coordinate_inverse x) (mem_singleton _)
    rw [A.coordinate_map_inverse hxA] at h
    have hh : |1 - sigma * cross A D x| < (1 / 1000 : ℝ) := by
      simpa only [cross, mul_assoc] using h
    exact ⟨sigma, hsigma, by linarith only [(abs_lt.mp hh).2]⟩
  have signOne {sigma v : ℝ} (hsigma : sigma = 1 ∨ sigma = -1)
      (hv : 0 < v) (hsv : 0 < sigma * v) : sigma = 1 := by
    rcases hsigma with rfl | rfl
    · rfl
    · norm_num at hsv
      linarith only [hv, hsv]
  have selfSign (A : EpsilonNeck g) {x : M} (hx : x ∈ A.carrier) :
      0 < cross A A x := by
    dsimp only [cross]
    rw [A.normalizedAxialVector_axial_mvfderiv hx]
    exact zero_lt_one
  let line (A D : EpsilonNeck g) (heA : A.epsilon = epsilon)
      (heD : D.epsilon = epsilon) := runLine A D (small A heA hel) (heD.trans heA.symm)
  have hJtop : ∀ q : UnitTwoSphere, 7 * L / 10 < F (B.coordinate_map (q, 3 * L / 4)) :=
    (hj C hej a b hshape Rh heRh hy hout f hf hgraph).1
  have hgraphHeight (q : UnitTwoSphere) : 7 * L / 10 < F (Rh.coordinate_map (q, f q)) := by
    have hm : Rh.coordinate_map (q, f q) ∈
        range (fun p : UnitTwoSphere => B.coordinate_map (p, 3 * L / 4)) := by
      rw [hgraph]
      exact mem_range_self q
    obtain ⟨p, hp⟩ := hm
    rw [← hp]
    exact hJtop p

  have hclosed :
      Disjoint (Q.coordinate_map '' (univ ×ˢ Icc (-L / 4) 0))
        (range (fun q : UnitTwoSphere => B.coordinate_map (q, 3 * L / 4))) := by
    apply disjoint_left.mpr
    rintro x ⟨⟨q, s⟩, ⟨_, hslo, hshi⟩, rfl⟩ hxSp
    have hs : s ∈ Ioo (-L) L :=
      ⟨by linarith only [hL, hslo], by linarith only [hL, hshi]⟩
    have hxQ : Q.coordinate_map (q, s) ∈ Q.carrier := Q.coordinate_map_mem (dom Q heQ hs)
    have hxGraph : Q.coordinate_map (q, s) ∈
        range (fun p : UnitTwoSphere => Rh.coordinate_map (p, f p)) := by
      rw [← hgraph]
      exact hxSp
    obtain ⟨p, hp⟩ := hxGraph
    have hxRh : Q.coordinate_map (q, s) ∈ Rh.carrier := by
      rw [← hp]
      exact Rh.coordinate_map_mem (dom Rh heRh (hfdom p))
    have hv : -(3 * L / 10) < height Rh (Q.coordinate_map (q, s)) ∧
        height Rh (Q.coordinate_map (q, s)) < -(L / 5) := by
      rw [← hp, heightAt Rh heRh p (hfdom p)]
      exact hf p
    obtain ⟨sigma, hsigma, hsig⟩ := pointSign Q Rh heQ heRh _ hxQ hxRh
    have hline := line Q Rh heQ heRh q s (-L / 4) sigma (-(14 * L / 25)) (3 * L / 50)
      (interval Q heQ hs) (interval Q heQ hquarter) hsigma hxRh hsig
      (by rw [heRh]; change -L < _; linarith only [hL])
      (by rw [heRh]; change _ < L; linarith only [hL]) (by
        intro t ht
        rw [uIcc_of_ge hslo] at ht
        change -(14 * L / 25) ≤ height Rh (Q.coordinate_map (q, s)) +
            sigma * (t - s) - (1 / 100 : ℝ) * |t - s| ∧
          height Rh (Q.coordinate_map (q, s)) + sigma * (t - s) +
            (1 / 100 : ℝ) * |t - s| ≤ 3 * L / 50
        rw [abs_of_nonpos (sub_nonpos.mpr ht.2)]
        rcases hsigma with heq | heq <;> rw [heq] <;>
          constructor <;> linarith only [hL, hv.1, hv.2, ht.1, ht.2, hslo, hshi])
    have hend := hline (-L / 4) right_mem_uIcc
    have hsigOne : sigma = 1 := signOne hsigma (hsignR q) hend.2.2.2
    have herr := hend.2.2.1
    change |height Rh (Q.coordinate_map (q, -L / 4)) -
      height Rh (Q.coordinate_map (q, s)) - sigma * (-L / 4 - s)| ≤
        (1 / 100 : ℝ) * |-L / 4 - s| at herr
    rw [hsigOne, one_mul, abs_of_nonpos (by linarith only [hslo] : -L / 4 - s ≤ 0)] at herr
    have htGraph : Q.coordinate_map (q, -L / 4) ∈
        range (fun p : UnitTwoSphere => Rh.coordinate_map (p, hR p)) := by
      rw [hS2]
      exact mem_range_self q
    obtain ⟨p', hp'⟩ := htGraph
    have htlow : -(L / 5) < height Rh (Q.coordinate_map (q, -L / 4)) := by
      rw [← hp', heightAt Rh heRh p' (hRdom p')]
      exact (hhR p').1
    linarith only [htlow, hv.2, hslo, (abs_le.mp herr).2]
  refine ⟨?_, hclosed⟩
  apply disjoint_left.mpr
  rintro x ⟨⟨q, r⟩, hz, rfl⟩ hxSm
  change f q < r ∧ r < hR q at hz
  have hr : r ∈ Ioo (-L) L :=
    ⟨by linarith only [hL, (hf q).1, hz.1],
      by linarith only [hL, (hhR q).2, hz.2]⟩
  have hxRh : Rh.coordinate_map (q, r) ∈ Rh.carrier :=
    Rh.coordinate_map_mem (dom Rh heRh hr)
  have hxQgraph : Rh.coordinate_map (q, r) ∈
      range (fun p : UnitTwoSphere => Q.coordinate_map (p, 0)) := by
    rw [← hSm]
    exact hxSm
  obtain ⟨p, hp⟩ := hxSm
  have hxN : Rh.coordinate_map (q, r) ∈ N.carrier := by
    rw [← hp]
    exact N.coordinate_map_mem (dom N heN (hNdom p))
  have hv : -(9 * L / 10) < height N (Rh.coordinate_map (q, r)) ∧
      height N (Rh.coordinate_map (q, r)) < -(4 * L / 5) := by
    rw [← hp, heightAt N heN p (hNdom p)]
    exact hhN p
  obtain ⟨p0, hp0⟩ := hxQgraph
  have hxQ : Rh.coordinate_map (q, r) ∈ Q.carrier := by
    rw [← hp0]
    exact Q.coordinate_map_mem (dom Q heQ hzero)
  have hQx : height Q (Rh.coordinate_map (q, r)) = 0 := by
    rw [← hp0]
    exact heightAt Q heQ p0 hzero

  have hRN : 0 < cross Rh N (Rh.coordinate_map (q, r)) := by
    obtain ⟨sigma, hsigma, hsig⟩ := pointSign Rh N heRh heN _ hxRh hxN
    rcases hsigma with rfl | rfl
    · simpa only [one_mul] using hsig
    · have hline := line Rh N heRh heN q r (f q) (-1) (-(9 * L / 10)) (47 * L / 100)
        (interval Rh heRh hr) (interval Rh heRh (hfdom q)) (Or.inr rfl) hxN hsig
        (by rw [heN]; change -L < _; linarith only [hL])
        (by rw [heN]; change _ < L; linarith only [hL]) (by
          intro t ht
          rw [uIcc_of_ge hz.1.le] at ht
          change -(9 * L / 10) ≤ height N (Rh.coordinate_map (q, r)) +
              (-1) * (t - r) - (1 / 100 : ℝ) * |t - r| ∧
            height N (Rh.coordinate_map (q, r)) + (-1) * (t - r) +
              (1 / 100 : ℝ) * |t - r| ≤ 47 * L / 100
          rw [abs_of_nonpos (sub_nonpos.mpr ht.2)]
          constructor <;>
            linarith only [hL, hv.1, hv.2, (hf q).1, (hhR q).2, hz.2, ht.1, ht.2])
      have hend := hline (f q) right_mem_uIcc
      have hhigh := hgraphHeight q
      simp only [F, if_pos hend.1] at hhigh
      linarith only [hhigh, hend.2.1.2, hL]
  have hQN : 0 < cross Q N (Rh.coordinate_map (q, r)) := by
    rw [← hp0]
    exact hsignN p0
  have hNQ := (composeSign Q Q N (small Q heQ hep) (small Q heQ hep)
    (small N heN hep) _ hxQ hxQ hxN (selfSign Q hxQ) hQN).2
  have hRQ := (composeSign Rh N Q (small Rh heRh hep) (small N heN hep)
    (small Q heQ hep) _ hxRh hxN hxQ hRN hNQ).1
  have hyRh : Rh.coordinate_map (q, hR q) ∈ Rh.carrier :=
    Rh.coordinate_map_mem (dom Rh heRh (hRdom q))
  have hyGraph : Rh.coordinate_map (q, hR q) ∈
      range (fun p : UnitTwoSphere => Q.coordinate_map (p, -L / 4)) := by
    rw [← hS2]
    exact mem_range_self q
  obtain ⟨p1, hp1⟩ := hyGraph
  have hyQ : Rh.coordinate_map (q, hR q) ∈ Q.carrier := by
    rw [← hp1]
    exact Q.coordinate_map_mem (dom Q heQ hquarter)
  have hQy : height Q (Rh.coordinate_map (q, hR q)) = -L / 4 := by
    rw [← hp1]
    exact heightAt Q heQ p1 hquarter
  have hQRy : 0 < cross Q Rh (Rh.coordinate_map (q, hR q)) := by
    rw [← hp1]
    exact hsignR p1
  have hRQy := (composeSign Q Q Rh (small Q heQ hep) (small Q heQ hep)
    (small Rh heRh hep) _ hyQ hyQ hyRh (selfSign Q hyQ) hQRy).2
  let m := (r + hR q) / 2
  have hrm : r < m := by dsimp only [m]; linarith only [hz.2]
  have hmh : m < hR q := by dsimp only [m]; linarith only [hz.2]
  have hm : m ∈ Ioo (-L) L := ⟨hr.1.trans hrm, hmh.trans (hRdom q).2⟩

  have hup := line Rh Q heRh heQ q r m 1 0 (16 * L / 25)
    (interval Rh heRh hr) (interval Rh heRh hm) (Or.inl rfl) hxQ
    (by simpa only [one_mul] using hRQ)
    (by rw [heQ]; change -L < 0; exact neg_lt_zero.mpr hL)
    (by rw [heQ]; change _ < L; linarith only [hL]) (by
      intro t ht
      rw [uIcc_of_le hrm.le] at ht
      change 0 ≤ height Q (Rh.coordinate_map (q, r)) + 1 * (t - r) -
          (1 / 100 : ℝ) * |t - r| ∧
        height Q (Rh.coordinate_map (q, r)) + 1 * (t - r) +
          (1 / 100 : ℝ) * |t - r| ≤ 16 * L / 25
      rw [hQx, one_mul, abs_of_nonneg (sub_nonneg.mpr ht.1)]
      dsimp only [m] at ht
      constructor <;> linarith only [hL, (hf q).1, hz.1, (hhR q).2, ht.1, ht.2])
  have hdown := line Rh Q heRh heQ q (hR q) m 1 (-(9 * L / 10)) (-L / 4)
    (interval Rh heRh (hRdom q)) (interval Rh heRh hm) (Or.inl rfl) hyQ
    (by simpa only [one_mul] using hRQy)
    (by rw [heQ]; change -L < _; linarith only [hL])
    (by rw [heQ]; change _ < L; linarith only [hL]) (by
      intro t ht
      rw [uIcc_of_ge hmh.le] at ht
      change -(9 * L / 10) ≤ height Q (Rh.coordinate_map (q, hR q)) +
          1 * (t - hR q) - (1 / 100 : ℝ) * |t - hR q| ∧
        height Q (Rh.coordinate_map (q, hR q)) + 1 * (t - hR q) +
          (1 / 100 : ℝ) * |t - hR q| ≤ -L / 4
      rw [hQy, one_mul, abs_of_nonpos (sub_nonpos.mpr ht.2)]
      dsimp only [m] at ht
      constructor <;> linarith only [hL, (hf q).1, hz.1, (hhR q).2, ht.1, ht.2])
  have heup := (hup m right_mem_uIcc).2.2.1
  change |height Q (Rh.coordinate_map (q, m)) -
    height Q (Rh.coordinate_map (q, r)) - 1 * (m - r)| ≤
      (1 / 100 : ℝ) * |m - r| at heup
  rw [hQx, sub_zero, one_mul, abs_of_nonneg (sub_nonneg.mpr hrm.le)] at heup
  have hedown := (hdown m right_mem_uIcc).2.2.1
  change |height Q (Rh.coordinate_map (q, m)) -
    height Q (Rh.coordinate_map (q, hR q)) - 1 * (m - hR q)| ≤
      (1 / 100 : ℝ) * |m - hR q| at hedown
  rw [hQy, one_mul, abs_of_nonpos (sub_nonpos.mpr hmh.le)] at hedown
  linarith only [hL, hrm, hmh, (abs_le.mp heup).1, (abs_le.mp hedown).2]

end PoincareConjecture
