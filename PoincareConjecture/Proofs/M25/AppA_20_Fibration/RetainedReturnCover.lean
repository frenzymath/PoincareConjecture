import PoincareConjecture.Proofs.M25.AppA_20_Fibration.FrontierInitialHeight
import PoincareConjecture.Proofs.M25.AppA_1_Necks.OrientedFrontierGraph
import PoincareConjecture.Proofs.M25.AppA_1_Necks.AxialLineContinuation
import PoincareConjecture.Proofs.M25.AppA_1_Necks.BufferedSliceHeight
import PoincareConjecture.Proofs.M25.AppA_1_Necks.AxialSignComposition










set_option autoImplicit false

open Set
open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareConjecture




theorem NeckOnlyCover.exists_retained_return_cover :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T3Space M] {g : RiemannianMetric 3 M},
      ∀ (H : NeckOnlyCover g), H.epsilon ≤ epsilon0 →
      H.X = Set.univ →
      ∀ (C : BalancedNeckChain g H.epsilon),
      ∀ a b : ℤ, C.shape = ChainShape.finite a b →
        let L := H.epsilon⁻¹
        let U : Set M := ⋃ i ∈ C.shape.active, (C.neck i).carrier
        let q0 := ((C.neck a).coordinate_inverse (C.neck a).center).1
        ∀ (R : EpsilonNeck g), R.epsilon = H.epsilon →
          R.center ∈ closure ((C.neck b).region 0 L) →
          R.center ∉ U →
          (∀ c ∈ Set.Ioo (-L) 0,
            ¬ Disjoint R.carrier ((C.neck a).region (-L) c)) →
          ∃ (P Q : EpsilonNeck g) (lo : ℤ → ℝ) (rlo rhi : ℝ),
            P ∈ H.necks ∧ (Q = P ∨ Q = P.reverse) ∧
            Q.epsilon = H.epsilon ∧
            Q.center = (C.neck a).coordinate_map (q0, -(17 * L / 20)) ∧
            (∀ i ∈ C.shape.active, -L < lo i ∧ lo i ≤ -L / 2) ∧
            lo a = -L / 2 ∧
            -L < rlo ∧ rlo ≤ rhi ∧ rhi < L ∧
            (U ∪ R.carrier) ∪ Q.carrier =
              ((⋃ i ∈ C.shape.active,
                (C.neck i).coordinate_map ''
                  (Set.univ ×ˢ Set.Icc (lo i) (3 * L / 4))) ∪
                R.coordinate_map '' (Set.univ ×ˢ Set.Icc rlo rhi)) ∪
                Q.coordinate_map ''
                  (Set.univ ×ˢ Set.Icc (-L / 2) (19 * L / 20)) := by
  obtain ⟨ej, hjp, hjcap, hj⟩ :=
    BalancedNeckChain.exists_oriented_frontier_initial_height_control.{u}
  obtain ⟨ek, hkp, _, hk⟩ := BalancedNeckChain.exists_finite_retained_core_cover.{u}
  obtain ⟨eg, hgp, _, hg⟩ := EpsilonNeck.exists_oriented_positive_frontier_graph.{u}
  obtain ⟨el, hlp, _, runLine⟩ := EpsilonNeck.exists_signed_axial_line_control.{u}
  obtain ⟨ev, hvp, _, runSlice⟩ := EpsilonNeck.exists_buffered_slice_height_control.{u}
  obtain ⟨ep, hpp, _, composeSign⟩ := EpsilonNeck.exists_positive_cross_axis_composition.{u}
  obtain ⟨es, hsp, _, hscale⟩ :=
    EpsilonNeck.exists_intersecting_scale_control.{u} (α := (1 / 1000 : ℝ)) (by norm_num)
  obtain ⟨eo, hop, _, horient⟩ :=
    EpsilonNeck.exists_intersecting_coherent_orientation.{u} (η := (1 / 1000 : ℝ))
      (by constructor <;> norm_num)
  obtain ⟨eh, hhp, _, hhorizontal⟩ :=
    EpsilonNeck.exists_intersecting_transition_height_horizontal_bound.{u}
      (α := (1 : ℝ)) (by norm_num)
  let B0 : ℝ := Real.sqrt 2 * (Real.pi + 1)
  have hB0 : 0 < B0 := by dsimp only [B0]; positivity
  refine ⟨min ej (min ek (min eg (min el (min ev (min ep (min es
    (min eo (min eh (min (1 / 10000) (1 / (10000 * (B0 + Real.pi + 1)))))))))))),
    by positivity, (min_le_left _ _).trans hjcap, ?_⟩
  intro M _ _ _ _ _ _ g H hepsilon hwhole C a b hshape
  classical
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
  let : ConnectedSpace UnitTwoSphere := by
    apply isConnected_iff_connectedSpace.mp
    exact isConnected_sphere (by rw [← Module.finrank_eq_rank]; norm_num) 0 (by norm_num)
  rcases le_min_iff.mp hepsilon with ⟨hej, hepsilon⟩
  rcases le_min_iff.mp hepsilon with ⟨hek, hepsilon⟩
  rcases le_min_iff.mp hepsilon with ⟨heg, hepsilon⟩
  rcases le_min_iff.mp hepsilon with ⟨hel, hepsilon⟩
  rcases le_min_iff.mp hepsilon with ⟨hev, hepsilon⟩
  rcases le_min_iff.mp hepsilon with ⟨hep, hepsilon⟩
  rcases le_min_iff.mp hepsilon with ⟨hes, hepsilon⟩
  rcases le_min_iff.mp hepsilon with ⟨heo, hepsilon⟩
  rcases le_min_iff.mp hepsilon with ⟨heh, hepsilon⟩
  rcases le_min_iff.mp hepsilon with ⟨hesmall, henumeric⟩
  let L : ℝ := H.epsilon⁻¹
  let N := C.neck a
  let B := C.neck b
  let U : Set M := ⋃ i ∈ C.shape.active, (C.neck i).carrier
  let q0 := (N.coordinate_inverse N.center).1
  let height (A : EpsilonNeck g) (x : M) : ℝ := (A.coordinate_inverse x).2
  let cross (A D : EpsilonNeck g) (x : M) : ℝ := D.scale *
    mvfderiv (𝓡 3) (fun y => (D.coordinate_inverse y).2) x (A.normalizedAxialVector x)
  let slab (A : EpsilonNeck g) (c d : ℝ) : Set M :=
    A.coordinate_map '' (univ ×ˢ Icc c d)
  let F : M → ℝ := fun x => if x ∈ N.carrier then height N x else L
  dsimp only
  intro R heR hy hout hreturn
  have hL : 0 < L := inv_pos.mpr H.epsilon_pos
  have hactive (i : ℤ) : i ∈ C.shape.active ↔ i ∈ Icc a b := by rw [hshape]; rfl
  have hab : a ≤ b := by
    obtain ⟨i, hi⟩ := C.active_nonempty
    exact ((hactive i).mp hi).1.trans ((hactive i).mp hi).2
  have ha : a ∈ C.shape.active := (hactive a).mpr ⟨le_rfl, hab⟩
  have hb : b ∈ C.shape.active := (hactive b).mpr ⟨hab, le_rfl⟩
  have heN : N.epsilon = H.epsilon := C.epsilon_eq a ha
  have heB : B.epsilon = H.epsilon := C.epsilon_eq b hb
  have small (A : EpsilonNeck g) (heA : A.epsilon = H.epsilon)
      {e : ℝ} (h : H.epsilon ≤ e) : A.epsilon ≤ e := by rw [heA]; exact h
  have dom (A : EpsilonNeck g) (heA : A.epsilon = H.epsilon)
      {q : UnitTwoSphere} {s : ℝ} (hs : s ∈ Ioo (-L) L) : (q, s) ∈ A.cylinderDomain :=
    ⟨mem_univ _, by simpa only [heA] using hs⟩
  have interval (A : EpsilonNeck g) (heA : A.epsilon = H.epsilon)
      {s : ℝ} (hs : s ∈ Ioo (-L) L) : s ∈ Ioo (-A.epsilon⁻¹) A.epsilon⁻¹ := by
    simpa only [heA] using hs
  have coord (A : EpsilonNeck g) (heA : A.epsilon = H.epsilon)
      {x : M} (hx : x ∈ A.carrier) : height A x ∈ Ioo (-L) L := by
    simpa only [heA] using (A.coordinate_inverse_mem x hx).2
  have memSlab (A : EpsilonNeck g) {x : M} (hx : x ∈ A.carrier)
      {c d : ℝ} (hs : height A x ∈ Icc c d) : x ∈ slab A c d :=
    ⟨A.coordinate_inverse x, ⟨mem_univ _, hs⟩, A.coordinate_map_inverse hx⟩
  have slabSub (A : EpsilonNeck g) (heA : A.epsilon = H.epsilon)
      {c d : ℝ} (hc : -L < c) (hd : d < L) : slab A c d ⊆ A.carrier := by
    rintro x ⟨z, hz, rfl⟩
    exact A.coordinate_map_mem (dom A heA ⟨hc.trans_le hz.2.1, hz.2.2.trans_lt hd⟩)
  have hbudget : (B0 + Real.pi + 1) * H.epsilon ≤ 1 / 10000 := by
    have h := (le_div_iff₀ (by positivity : 0 < 10000 * (B0 + Real.pi + 1))).mp henumeric
    nlinarith only [h]
  have hnumeric : B0 ≤ L / 10000 ∧ Real.pi ≤ L / 10000 := by
    have h := (le_div_iff₀ H.epsilon_pos).mpr hbudget
    have heq : (1 / 10000 : ℝ) / H.epsilon = L / 10000 := by dsimp only [L]; ring
    rw [heq] at h
    constructor <;> linarith only [h, hB0, Real.pi_pos]
  have pointSign (A D : EpsilonNeck g) (heA : A.epsilon = H.epsilon)
      (heD : D.epsilon = H.epsilon) (x : M) (hxA : x ∈ A.carrier) (hxD : x ∈ D.carrier) :
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
    change |1 - sigma * D.scale * _| < (1 / 1000 : ℝ) at h
    have hh : |1 - sigma * cross A D x| < (1 / 1000 : ℝ) := by
      simpa only [cross, mul_assoc] using h
    exact ⟨sigma, hsigma, by linarith only [hL, (abs_lt.mp hh).2]⟩
  have signOne {sigma v : ℝ} (hsigma : sigma = 1 ∨ sigma = -1)
      (hv : 0 < v) (hsv : 0 < sigma * v) : sigma = 1 := by
    rcases hsigma with rfl | rfl
    · rfl
    · norm_num at hsv
      linarith only [hv, hsv]
  have sliceAt (A D : EpsilonNeck g) (heA : A.epsilon = H.epsilon)
      (heD : D.epsilon = H.epsilon) (p : UnitTwoSphere) (s : ℝ)
      (hs : s ∈ Ioo (-L) L) (hx : A.coordinate_map (p, s) ∈ D.carrier)
      (hh : |height D (A.coordinate_map (p, s))| ≤ (99 / 100 : ℝ) * L)
      (hp : 0 < cross A D (A.coordinate_map (p, s))) :
      ∀ q : UnitTwoSphere, A.coordinate_map (q, s) ∈ D.carrier ∧
        |height D (A.coordinate_map (q, s)) - height D (A.coordinate_map (p, s))| ≤
          Real.pi ∧ 0 < cross A D (A.coordinate_map (q, s)) := by
    obtain ⟨hm, ho, sigma, hsigma, hc⟩ := runSlice A D (small A heA hev)
      (heD.trans heA.symm) p s (interval A heA hs) hx (by simpa only [heD] using hh)
    have hsig : sigma = 1 := signOne hsigma hp (hc p).2
    subst sigma
    exact fun q => ⟨hm q, ho p q, by simpa only [one_mul] using (hc q).2⟩
  let line (A D : EpsilonNeck g) (heA : A.epsilon = H.epsilon)
      (heD : D.epsilon = H.epsilon) := runLine A D (small A heA hel) (heD.trans heA.symm)
  have hBU : B.carrier ⊆ U := fun _ hx => mem_iUnion₂.mpr ⟨b, hb, hx⟩
  obtain ⟨Rh, f, hRh, _, hfdom, hf0, hgraph0⟩ := hg B R (small B heB heg)
    (heR.trans heB.symm) (by simpa only [heB] using hy) (fun hx => hout (hBU hx))
  have heRh : Rh.epsilon = H.epsilon := by rcases hRh with rfl | rfl <;> exact heR
  have hcRh : Rh.carrier = R.carrier := by rcases hRh with rfl | rfl <;> rfl
  have hyRh : Rh.center = R.center := by rcases hRh with rfl | rfl <;> rfl
  have hf (q : UnitTwoSphere) : -(3 * L / 10) < f q ∧ f q < -(L / 5) := by
    simpa only [heB] using hf0 q
  have hgraph : range (fun q => B.coordinate_map (q, 3 * L / 4)) =
      range (fun q => Rh.coordinate_map (q, f q)) := by simpa only [heB] using hgraph0
  have hJ := hj C hej a b hshape Rh heRh (by rw [hyRh]; exact hy)
    (by rw [hyRh]; exact hout) f hf hgraph
  change (∀ q, 7 * L / 10 < F (B.coordinate_map (q, 3 * L / 4))) ∧
    (∀ q s, -L < s → s ≤ -(L / 20) →
      Rh.coordinate_map (q, s) ∈ U ∧ -(L / 5) < F (Rh.coordinate_map (q, s))) at hJ
  have hgraphHeight (q : UnitTwoSphere) : 7 * L / 10 < F (Rh.coordinate_map (q, f q)) := by
    have hm : Rh.coordinate_map (q, f q) ∈ range (fun p => B.coordinate_map (p, 3 * L / 4)) := by
      rw [hgraph]
      exact mem_range_self q
    obtain ⟨p, hp⟩ := hm
    rw [← hp]
    exact hJ.1 p
  obtain ⟨lo, hlo, hloa, _, hcover⟩ := hk C hek a b hshape
  let K : Set M := ⋃ i ∈ C.shape.active, slab (C.neck i) (lo i) (3 * L / 4)
  change U = (K ∪ N.region (-L) (lo a)) ∪ B.region (3 * L / 4) L at hcover
  rw [hloa] at hcover
  have hKsub : K ⊆ U := by intro x hx; rw [hcover]; exact Or.inl (Or.inl hx)
  obtain ⟨w, hwR, hwN, hu0, hu1⟩ := Set.not_disjoint_iff.mp
    (hreturn (-(199 * L / 200))
      ⟨by linarith only [hL], by linarith only [hL]⟩)
  change w ∈ N.carrier at hwN
  have hwRh : w ∈ Rh.carrier := hcRh.symm ▸ hwR
  let r0 := height Rh w
  let qr := (Rh.coordinate_inverse w).1
  let u := height N w
  change -L < u at hu0
  change u < -(199 * L / 200) at hu1
  have hRw : Rh.coordinate_map (qr, r0) = w := Rh.coordinate_map_inverse hwRh
  have hr0 : r0 ∈ Ioo (-(L / 20)) L := by
    refine ⟨?_, (coord Rh heRh hwRh).2⟩
    by_contra hnot
    have hh := (hJ.2 qr r0 (coord Rh heRh hwRh).1 (le_of_not_gt hnot)).2
    rw [hRw] at hh
    simp only [F, if_pos hwN] at hh
    linarith only [hh, hu1, hL]
  have hreturnSign : 0 < cross Rh N w := by
    obtain ⟨sigma, hsigma, hs⟩ := pointSign Rh N heRh heN w hwRh hwN
    rcases hsigma with rfl | rfl
    · simpa only [one_mul] using hs
    · have hsft : f qr ≤ r0 := by linarith only [(hf qr).2, hr0.1, hL]
      have ht0 := coord Rh heRh hwRh
      have hline := line Rh N heRh heN qr r0 (f qr) (-1) u (8 * L / 25)
        (interval Rh heRh ht0) (hfdom qr) (Or.inr rfl) (by rw [hRw]; exact hwN)
        (by
          change 0 < (-1 : ℝ) * cross Rh N (Rh.coordinate_map (qr, r0))
          rw [hRw]
          exact hs) (by rw [heN]; exact hu0)
        (by rw [heN]; change _ < L; linarith only [hL]) (by
          intro t ht
          rw [uIcc_of_ge hsft] at ht
          rw [hRw]
          change u ≤ u + (-1) * (t - r0) - (1 / 100 : ℝ) * |t - r0| ∧
            u + (-1) * (t - r0) + (1 / 100 : ℝ) * |t - r0| ≤ 8 * L / 25
          rw [abs_of_nonpos (sub_nonpos.mpr ht.2)]
          constructor <;> nlinarith only [(hf qr).1, hr0.2, ht.1, ht.2, hu1, hL])
      have hend := hline (f qr) right_mem_uIcc
      have hh := hgraphHeight qr
      simp only [F, if_pos hend.1] at hh
      linarith only [hh, hend.2.1.2, hL]
  let z := N.coordinate_map (q0, -(17 * L / 20))
  have hz0 : -(17 * L / 20) ∈ Ioo (-L) L :=
    ⟨by linarith only [hL], by linarith only [hL]⟩
  have hzN : z ∈ N.carrier := N.coordinate_map_mem (dom N heN hz0)
  obtain ⟨P, hP, hPcenter⟩ := H.pointwise_center_cover z (by rw [hwhole]; exact mem_univ _)
  have heP : P.epsilon = H.epsilon := H.neck_epsilon P hP
  have hzP : z ∈ P.carrier := hPcenter ▸ P.central_sphere_subset P.center_on_central_sphere
  obtain ⟨sigma, hsigma, hsig⟩ := pointSign N P heN heP z hzN hzP
  obtain ⟨Q, hQP, heQ, hQcenter, hQsign⟩ :
      ∃ Q : EpsilonNeck g, (Q = P ∨ Q = P.reverse) ∧ Q.epsilon = H.epsilon ∧
        Q.center = z ∧ 0 < cross N Q z := by
    rcases hsigma with rfl | rfl
    · exact ⟨P, Or.inl rfl, heP, hPcenter, by simpa only [one_mul] using hsig⟩
    · refine ⟨P.reverse, Or.inr rfl, heP, hPcenter, ?_⟩
      have hneg : cross N P.reverse z = -(cross N P z) := by
        change P.scale * mvfderiv (𝓡 3) (fun y => -(P.coordinate_inverse y).2) z
          (N.normalizedAxialVector z) = _
        rw [mvfderiv_fun_neg]
        simp only [neg_apply, mul_neg, cross]
      rw [hneg]
      simpa only [neg_one_mul] using hsig
  have hzQ : z ∈ Q.carrier := hQcenter ▸ Q.central_sphere_subset Q.center_on_central_sphere
  have hQ0 : height Q z = 0 := by
    rw [← hQcenter]
    exact ((Q.mem_central_sphere_iff _).mp Q.center_on_central_sphere).2
  have hNz : height N z = -(17 * L / 20) :=
    congrArg Prod.snd (N.coordinate_inverse_map (q0, -(17 * L / 20)) (interval N heN hz0))

  have calibration (t : ℝ) (ht : t ∈ Ioo (-L) (-(2 * L / 5))) :
      ∀ q : UnitTwoSphere, N.coordinate_map (q, t) ∈ Q.carrier ∧
        0 < cross N Q (N.coordinate_map (q, t)) ∧
        |height Q (N.coordinate_map (q, t)) - (t + 17 * L / 20)| ≤
          (1 / 100 : ℝ) * |t + 17 * L / 20| + Real.pi := by
    have htL : t ∈ Ioo (-L) L := ⟨ht.1, by linarith only [hL, ht.2]⟩
    have hbase := line N Q heN heQ q0 (-(17 * L / 20)) t 1 (-L / 2) (L / 2)
      (interval N heN hz0) (interval N heN htL) (Or.inl rfl) hzQ
      (by simpa only [cross, one_mul] using hQsign)
      (by rw [heQ]; change -L < -L / 2; linarith only [hL])
      (by rw [heQ]; change L / 2 < L; linarith only [hL]) (by
        intro r hr
        have hrange : -L < r ∧ r < -(2 * L / 5) := by
          rcases le_total (-(17 * L / 20)) t with hst | hts
          · rw [uIcc_of_le hst] at hr
            constructor <;> linarith only [hL, hr.1, hr.2, ht.2]
          · rw [uIcc_of_ge hts] at hr
            constructor <;> linarith only [hL, hr.1, hr.2, ht.1]
        change -L / 2 ≤ height Q z + 1 * (r - -(17 * L / 20)) - _ ∧
          height Q z + 1 * (r - -(17 * L / 20)) + _ ≤ L / 2
        rw [hQ0]
        by_cases hnonneg : 0 ≤ r - -(17 * L / 20)
        · rw [abs_of_nonneg hnonneg]
          constructor <;> linarith only [hL, hrange.1, hrange.2]
        · rw [abs_of_neg (lt_of_not_ge hnonneg)]
          constructor <;> linarith only [hL, hrange.1, hrange.2])
    have hb := hbase t right_mem_uIcc
    have habs : |height Q (N.coordinate_map (q0, t))| ≤ (99 / 100 : ℝ) * L := by
      apply abs_le.mpr
      constructor <;> linarith only [hL, hb.2.1.1, hb.2.1.2]
    have hs := sliceAt N Q heN heQ q0 t htL hb.1 habs
      (by simpa only [one_mul] using hb.2.2.2)
    have herr : |height Q (N.coordinate_map (q0, t)) - (t + 17 * L / 20)| ≤
        (1 / 100 : ℝ) * |t + 17 * L / 20| := by
      have h := hb.2.2.1
      change |height Q (N.coordinate_map (q0, t)) - height Q z -
        1 * (t - -(17 * L / 20))| ≤ _ at h
      simpa only [hQ0, sub_zero, one_mul, sub_neg_eq_add] using h
    intro q
    have hosc : |height Q (N.coordinate_map (q, t)) -
        height Q (N.coordinate_map (q0, t))| ≤ Real.pi := by
      simpa only [one_mul] using EpsilonNeck.sphere_height_oscillation_of_intrinsic_slope
        (N.contMDiff_transition_height_slice Q (interval N heN htL) (fun p => (hs p).1))
        (α := (1 : ℝ)) (by norm_num) (fun p v =>
          hhorizontal N Q (small N heN heh) (small Q heQ heh)
            (p, t) (dom N heN htL) (hs p).1 v) q0 q
    refine ⟨(hs q).1, (hs q).2.2, ?_⟩
    exact (abs_sub_le (height Q (N.coordinate_map (q, t)))
      (height Q (N.coordinate_map (q0, t))) (t + 17 * L / 20)).trans
        (by linarith only [hosc, herr])
  have hNneg : N.region (-L) (-L / 2) ⊆ slab Q (-L / 2) (19 * L / 20) := by
    intro x hx
    have hc := calibration (height N x) ⟨hx.2.1, by linarith only [hL, hx.2.2]⟩
      (N.coordinate_inverse x).1
    rw [N.coordinate_map_inverse hx.1] at hc
    have ht : |height N x + 17 * L / 20| ≤ 7 * L / 20 := by
      apply abs_le.mpr
      constructor <;> linarith only [hL, hx.2.1, hx.2.2]
    apply memSlab Q hc.1
    have he := abs_le.mp hc.2.2
    constructor <;> nlinarith only [hL, he.1, he.2, ht, hnumeric.2, hx.2.1, hx.2.2]
  have hwcal := calibration u ⟨hu0, by linarith only [hL, hu1]⟩ (N.coordinate_inverse w).1
  rw [N.coordinate_map_inverse hwN] at hwcal
  have hwQ : w ∈ Q.carrier := hwcal.1
  let t0 := height Q w
  have ht0 : -(4 * L / 25) < t0 ∧ t0 < -(7 * L / 50) := by
    have ht : |u + 17 * L / 20| ≤ 3 * L / 20 := by
      apply abs_le.mpr
      constructor <;> linarith only [hu0, hu1, hL]
    have he := abs_le.mp hwcal.2.2
    constructor <;> nlinarith only [hL, he.1, he.2, ht, hu0, hu1, hnumeric.2]
  have hsigns := composeSign Rh N Q (small Rh heRh hep) (small N heN hep)
    (small Q heQ hep) w hwRh hwN hwQ hreturnSign hwcal.2.1
  have hzSign := (composeSign N N Q (small N heN hep) (small N heN hep)
    (small Q heQ hep) z hzN hzN hzQ
    (by simpa only [N.normalizedAxialVector_axial_mvfderiv hzN] using
      (zero_lt_one : (0 : ℝ) < 1)) hQsign).2
  let qz := (Q.coordinate_inverse z).1
  have hQz : Q.coordinate_map (qz, 0) = z := by
    change Q.coordinate_map ((Q.coordinate_inverse z).1, 0) = z
    rw [← hQ0]
    exact Q.coordinate_map_inverse hzQ
  have hcentral := sliceAt Q N heQ heN qz 0 ⟨by linarith only [hL], hL⟩
    (by rw [hQz]; exact hzN)
    (by
      rw [hQz, hNz, abs_neg, abs_of_pos (by positivity : 0 < 17 * L / 20)]
      linarith only [hL])
    (by rw [hQz]; exact hzSign)
  have hcentralHeight (q : UnitTwoSphere) :
      -(43 * L / 50) < height N (Q.coordinate_map (q, 0)) ∧
        height N (Q.coordinate_map (q, 0)) < -(21 * L / 25) := by
    have hh := (hcentral q).2.1
    rw [hQz, hNz] at hh
    constructor <;> linarith only [hL, (abs_le.mp hh).1, (abs_le.mp hh).2, hnumeric.2]
  have hQpos : Q.region (L / 2) L ⊆ K := by
    intro x hx
    let q := (Q.coordinate_inverse x).1
    let s := height Q x
    have hmap : Q.coordinate_map (q, s) = x := Q.coordinate_map_inverse hx.1
    have hline := line Q N heQ heN q 0 s 1 (-(43 * L / 50)) (9 * L / 50)
      (interval Q heQ ⟨by linarith only [hL], hL⟩) (interval Q heQ (coord Q heQ hx.1))
      (Or.inl rfl) (hcentral q).1 (by simpa only [one_mul] using (hcentral q).2.2)
      (by rw [heN]; change -L < _; linarith only [hL])
      (by rw [heN]; change _ < L; linarith only [hL]) (by
        intro r hr
        rw [uIcc_of_le (by linarith only [hL, hx.2.1] : 0 ≤ s)] at hr
        rw [sub_zero, one_mul, abs_of_nonneg hr.1]
        constructor <;> linarith only [hL, (hcentralHeight q).1,
          (hcentralHeight q).2, hr.1, hr.2, hx.2.2])
    have hh := hline s right_mem_uIcc
    rw [hmap] at hh
    have herr := abs_le.mp hh.2.2.1
    have hs : height N x ∈ Icc (-L / 2) (3 * L / 4) := by
      have habs : |s - 0| = s := by
        rw [sub_zero, abs_of_pos (by linarith only [hL, hx.2.1] : 0 < s)]
      rw [habs] at herr
      constructor <;> linarith only [hL, herr.1, herr.2, (hcentralHeight q).1, hx.2.1, hh.2.1.2]
    apply mem_iUnion₂.mpr
    refine ⟨a, ha, ?_⟩
    rw [hloa]
    exact memSlab N hh.1 hs
  have hRbase := sliceAt Rh Q heRh heQ qr r0 (coord Rh heRh hwRh)
    (by rw [hRw]; exact hwQ)
    (by rw [hRw]; apply abs_le.mpr; constructor <;> linarith only [hL, ht0.1, ht0.2])
    (by rw [hRw]; exact hsigns.1)
  have hRbaseHeight (q : UnitTwoSphere) :
      -(17 * L / 100) < height Q (Rh.coordinate_map (q, r0)) ∧
        height Q (Rh.coordinate_map (q, r0)) < -(13 * L / 100) := by
    have hh := (hRbase q).2.1
    rw [hRw] at hh
    constructor <;> linarith only [hL, (abs_le.mp hh).1, (abs_le.mp hh).2, ht0.1, ht0.2, hnumeric.2]
  have hRpos (x : M) (hx : x ∈ Rh.carrier) (hxs : r0 ≤ height Rh x) :
      x ∈ slab Q (-L / 2) (19 * L / 20) := by
    let q := (Rh.coordinate_inverse x).1
    let s := height Rh x
    have hmap : Rh.coordinate_map (q, s) = x := Rh.coordinate_map_inverse hx
    have hline := line Rh Q heRh heQ q r0 s 1 (-(9 * L / 50)) (19 * L / 20)
      (interval Rh heRh (coord Rh heRh hwRh)) (interval Rh heRh (coord Rh heRh hx))
      (Or.inl rfl) (hRbase q).1 (by simpa only [one_mul] using (hRbase q).2.2)
      (by rw [heQ]; change -L < _; linarith only [hL])
      (by rw [heQ]; change _ < L; linarith only [hL]) (by
        intro r hr
        rw [uIcc_of_le hxs] at hr
        rw [one_mul, abs_of_nonneg (sub_nonneg.mpr hr.1)]
        constructor <;> linarith only [hL, (hRbaseHeight q).1, (hRbaseHeight q).2,
          hr.1, hr.2, hr0.1, (coord Rh heRh hx).2])
    have hh := hline s right_mem_uIcc
    rw [hmap] at hh
    exact memSlab Q hh.1 ⟨by linarith only [hL, hh.2.1.1], hh.2.1.2⟩
  let qw := (Q.coordinate_inverse w).1
  have hQw : Q.coordinate_map (qw, t0) = w := Q.coordinate_map_inverse hwQ
  have hdown := line Q Rh heQ heRh qw t0 (-L / 4) 1 (-(17 * L / 100)) r0
    (interval Q heQ (coord Q heQ hwQ))
    (interval Q heQ ⟨by linarith only [hL], by linarith only [hL]⟩)
    (Or.inl rfl) (by rw [hQw]; exact hwRh)
    (by
      change 0 < (1 : ℝ) * cross Q Rh (Q.coordinate_map (qw, t0))
      rw [hQw, one_mul]
      exact hsigns.2)
    (by rw [heRh]; change -L < _; linarith only [hL])
    (by rw [heRh]; exact hr0.2) (by
      intro r hr
      rw [uIcc_of_ge (by linarith only [hL, ht0.1] : -L / 4 ≤ t0)] at hr
      rw [hQw, one_mul, abs_of_nonpos (sub_nonpos.mpr hr.2)]
      constructor <;> linarith only [hL, hr.1, hr.2, hr0.1, ht0.2])
  let v := Q.coordinate_map (qw, -L / 4)
  have hv := hdown (-L / 4) right_mem_uIcc
  have hvHeight : -(17 * L / 100) < height Rh v ∧ height Rh v < 23 * L / 25 := by
    have hh := hv.2.2.1
    rw [hQw, one_mul, abs_of_neg (by linarith only [hL, ht0.1] : -L / 4 - t0 < 0)] at hh
    constructor <;> linarith only [hL, (abs_le.mp hh).1, (abs_le.mp hh).2,
      ht0.1, ht0.2, hr0.1, hr0.2]
  have hQbase := sliceAt Q Rh heQ heRh qw (-L / 4)
    ⟨by linarith only [hL], by linarith only [hL]⟩ hv.1
    (by apply abs_le.mpr; constructor <;> linarith only [hL, hvHeight.1, hvHeight.2])
    (by simpa only [one_mul] using hv.2.2.2)
  have hQbaseHeight (q : UnitTwoSphere) :
      -(9 * L / 50) < height Rh (Q.coordinate_map (q, -L / 4)) ∧
        height Rh (Q.coordinate_map (q, -L / 4)) < 93 * L / 100 := by
    have hh := (hQbase q).2.1
    constructor <;> linarith only [hL, (abs_le.mp hh).1, (abs_le.mp hh).2,
      hvHeight.1, hvHeight.2, hnumeric.2]
  let m := max (19 * L / 20) r0
  have hm : m < L := max_lt (by linarith only [hL]) hr0.2
  have hm95 : 19 * L / 20 ≤ m := le_max_left _ _
  have hmr : r0 ≤ m := le_max_right _ _
  have hQneg : Q.region (-L) (-L / 2) ⊆ slab Rh (-(24 * L / 25)) m := by
    intro x hx
    let q := (Q.coordinate_inverse x).1
    let s := height Q x
    have hmap : Q.coordinate_map (q, s) = x := Q.coordinate_map_inverse hx.1
    have hline := line Q Rh heQ heRh q (-L / 4) s 1 (-(19 * L / 20)) (47 * L / 50)
      (interval Q heQ ⟨by linarith only [hL], by linarith only [hL]⟩)
      (interval Q heQ (coord Q heQ hx.1))
      (Or.inl rfl) (hQbase q).1 (by simpa only [one_mul] using (hQbase q).2.2)
      (by rw [heRh]; change -L < _; linarith only [hL])
      (by rw [heRh]; change _ < L; linarith only [hL]) (by
        intro r hr
        rw [uIcc_of_ge (by linarith only [hL, hx.2.2] : s ≤ -L / 4)] at hr
        rw [one_mul, abs_of_nonpos (sub_nonpos.mpr hr.2)]
        constructor <;> linarith only [hL, (hQbaseHeight q).1, (hQbaseHeight q).2,
          hr.1, hr.2, hx.2.1])
    have hh := hline s right_mem_uIcc
    rw [hmap] at hh
    exact memSlab Rh hh.1
      ⟨by linarith only [hL, hh.2.1.1], by linarith only [hm95, hL, hh.2.1.2]⟩

  have hRhCenter := (Rh.mem_central_sphere_iff Rh.center).mp Rh.center_on_central_sphere
  have hyB : Rh.center ∈ closure (B.region 0 B.epsilon⁻¹) := by
    simpa only [hyRh, heB] using hy
  have hyBout : Rh.center ∉ B.carrier := by rw [hyRh]; exact fun hx => hout (hBU hx)
  have hinter : (Rh.carrier ∩ B.carrier).Nonempty := by
    obtain ⟨x, hxRh, hxB⟩ := mem_closure_iff.mp hyB Rh.carrier Rh.carrier_open hRhCenter.1
    exact ⟨x, hxRh, hxB.1⟩
  have hratio := (hscale Rh B (small Rh heRh hes) (small B heB hes) hinter).2
  have hscaleBR : B.scale ≤ (1001 / 1000 : ℝ) * Rh.scale := by
    apply (div_le_iff₀ Rh.scale_pos).mp
    linarith only [hL, (abs_lt.mp hratio).2]
  have hsqlo : (999 : ℝ) / 1000 ≤ Real.sqrt (1 - H.epsilon) :=
    Real.le_sqrt_of_sq_le (by nlinarith only [hesmall])
  have hsqhi : Real.sqrt (1 + H.epsilon) ≤ (1001 : ℝ) / 1000 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by nlinarith only [hesmall]⟩
  have hcoef : B.scale * Real.sqrt (1 + H.epsilon) ≤
      (101 / 100 : ℝ) * (Rh.scale * Real.sqrt (1 - H.epsilon)) := by
    calc
      _ ≤ ((1001 / 1000 : ℝ) * Rh.scale) * (1001 / 1000) :=
        mul_le_mul hscaleBR hsqhi (Real.sqrt_nonneg _)
          (mul_nonneg (by norm_num) Rh.scale_pos.le)
      _ ≤ _ := by nlinarith only [hL, mul_le_mul_of_nonneg_left hsqlo Rh.scale_pos.le, Rh.scale_pos]
  have hlast (x : M) (hx : x ∈ B.region (3 * L / 4) L) :
      x ∈ Rh.carrier ∧ |height Rh x| < 27 * L / 100 := by
    let T := L - height B x + B0
    have hT : 0 < T := by dsimp only [T]; linarith only [hB0, hx.2.2]
    have hTbound : (101 / 100 : ℝ) * T < 27 * L / 100 := by
      dsimp only [T]
      linarith only [hL, hx.2.1, hnumeric.1]
    have hu := B.edist_le_positive_frontier hx.1 hyB hyBout
    have hu' : g.edist x Rh.center ≤
        ENNReal.ofReal (B.scale * Real.sqrt (1 + H.epsilon) * T) := by
      simpa only [heB, L, T, height, B0] using hu
    have hd := Rh.axialDepth_edist_le x Rh.center
    have hdc : Rh.axialDepth Rh.center = L := by
      simp only [EpsilonNeck.axialDepth, if_pos hRhCenter.1, hRhCenter.2,
        abs_zero, sub_zero, heRh, L]
    rw [heRh, hdc] at hd
    have hr := (ENNReal.ofReal_le_ofReal_iff
      (mul_nonneg (mul_nonneg B.scale_pos.le (Real.sqrt_nonneg _)) hT.le)).mp (hd.trans hu')
    have hmul := mul_le_mul_of_nonneg_right hcoef hT.le
    have hc : 0 < Rh.scale * Real.sqrt (1 - H.epsilon) :=
      mul_pos Rh.scale_pos (by linarith only [hsqlo])
    have hb : |Rh.axialDepth x - L| ≤ (101 / 100 : ℝ) * T := by
      apply (mul_le_mul_iff_left₀ hc).mp
      nlinarith only [hr, hmul]
    have hxRh : x ∈ Rh.carrier := by
      by_contra hxout
      simp only [EpsilonNeck.axialDepth, if_neg hxout, zero_sub, abs_neg,
        abs_of_pos hL] at hb
      linarith only [hb, hTbound, hL]
    refine ⟨hxRh, ?_⟩
    have hh : Rh.axialDepth x - L = -|height Rh x| := by
      simp only [EpsilonNeck.axialDepth, if_pos hxRh, heRh]
      change L - |height Rh x| - L = _
      ring
    rw [hh, abs_neg, abs_abs] at hb
    exact hb.trans_lt hTbound
  have hRhneg : Rh.region (-L) (-L / 2) ⊆ K := by
    intro x hx
    have hh := hJ.2 (Rh.coordinate_inverse x).1 (height Rh x) hx.2.1
      (by linarith only [hL, hx.2.2])
    rw [Rh.coordinate_map_inverse hx.1] at hh
    rw [hcover] at hh
    rcases hh.1 with (hxK | hxN) | hxB
    · exact hxK
    · have hb := hh.2
      simp only [F, if_pos hxN.1] at hb
      linarith only [hL, hb, hxN.2.2]
    · have hb := (hlast x hxB).2
      linarith only [hL, (abs_lt.mp hb).1, hx.2.2]
  have hretained : (U ∪ Rh.carrier) ∪ Q.carrier =
      (K ∪ slab Rh (-(24 * L / 25)) m) ∪ slab Q (-L / 2) (19 * L / 20) := by
    apply Subset.antisymm
    · intro x hx
      rcases hx with (hxU | hxRh) | hxQ
      · rw [hcover] at hxU
        rcases hxU with (hxK | hxN) | hxB
        · exact Or.inl (Or.inl hxK)
        · exact Or.inr (hNneg hxN)
        · have hh := hlast x hxB
          exact Or.inl (Or.inr (memSlab Rh hh.1
            ⟨by linarith only [hL, (abs_lt.mp hh.2).1],
              by linarith only [hm95, hL, (abs_lt.mp hh.2).2]⟩))
      · by_cases hlow : height Rh x < -L / 2
        · exact Or.inl (Or.inl (hRhneg ⟨hxRh, (coord Rh heRh hxRh).1, hlow⟩))
        · by_cases hhigh : height Rh x ≤ r0
          · exact Or.inl (Or.inr (memSlab Rh hxRh
              ⟨by linarith only [hL, le_of_not_gt hlow], hhigh.trans hmr⟩))
          · exact Or.inr (hRpos x hxRh (le_of_not_ge hhigh))
      · by_cases hlow : height Q x < -L / 2
        · exact Or.inl (Or.inr (hQneg ⟨hxQ, (coord Q heQ hxQ).1, hlow⟩))
        · by_cases hhigh : height Q x ≤ L / 2
          · exact Or.inr (memSlab Q hxQ
              ⟨le_of_not_gt hlow, by linarith only [hhigh, hL]⟩)
          · exact Or.inl (Or.inl (hQpos ⟨hxQ, lt_of_not_ge hhigh, (coord Q heQ hxQ).2⟩))
    · intro x hx
      rcases hx with (hxK | hxRh) | hxQ
      · exact Or.inl (Or.inl (hKsub hxK))
      · exact Or.inl (Or.inr (slabSub Rh heRh (by linarith only [hL]) hm hxRh))
      · exact Or.inr (slabSub Q heQ (by linarith only [hL]) (by linarith only [hL]) hxQ)
  rcases hRh with hRh | hRh
  · refine ⟨P, Q, lo, -(24 * L / 25), m, hP, hQP, heQ, hQcenter,
      hlo, hloa, by linarith only [hL], by linarith only [hm95, hL], hm, ?_⟩
    simpa only [hRh] using hretained
  · have hslab : slab Rh (-(24 * L / 25)) m = slab R (-m) (24 * L / 25) := by
      rw [hRh]
      apply Subset.antisymm
      · rintro x ⟨⟨q, s⟩, hs, rfl⟩
        exact ⟨(q, -s), ⟨mem_univ _, by linarith only [hL, hs.2.2],
          by linarith only [hL, hs.2.1]⟩, rfl⟩
      · rintro x ⟨⟨q, s⟩, hs, rfl⟩
        refine ⟨(q, -s), ⟨mem_univ _, by linarith only [hL, hs.2.2],
          by linarith only [hL, hs.2.1]⟩, ?_⟩
        change R.coordinate_map (q, - -s) = R.coordinate_map (q, s)
        rw [neg_neg]
    refine ⟨P, Q, lo, -m, 24 * L / 25, hP, hQP, heQ, hQcenter,
      hlo, hloa, by linarith only [hm], by linarith only [hm95, hL],
      by linarith only [hL], ?_⟩
    rw [hslab, hcRh] at hretained
    exact hretained

end PoincareConjecture
