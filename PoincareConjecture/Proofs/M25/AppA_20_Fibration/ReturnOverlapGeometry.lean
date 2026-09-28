import PoincareConjecture.Proofs.M25.AppA_20_Fibration.RetainedReturnCover
import Mathlib.Topology.OpenPartialHomeomorph.Composition

set_option autoImplicit false

open Set
open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareConjecture

theorem NeckOnlyCover.exists_closing_return_geometry :
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
        let N := C.neck a
        let B := C.neck b
        let U : Set M := ⋃ i ∈ C.shape.active, (C.neck i).carrier
        let q0 := (N.coordinate_inverse N.center).1
        ∀ (R : EpsilonNeck g), R.epsilon = H.epsilon →
          R.center ∈ closure (B.region 0 L) →
          R.center ∉ U →
          (∀ c ∈ Set.Ioo (-L) 0,
            ¬ Disjoint R.carrier (N.region (-L) c)) →
          ∃ (P Q Rh : EpsilonNeck g)
            (f hN hR : UnitTwoSphere → ℝ)
            (lo : ℤ → ℝ) (rlo rhi : ℝ),
            let TN := (Q.coordinatePartialHomeomorph.restr
              (Set.univ ×ˢ Set.Ioo (-L / 40) (L / 40))).trans
                N.coordinatePartialHomeomorph.symm
            let TR := (Q.coordinatePartialHomeomorph.restr
              (Set.univ ×ˢ Set.Ioo (-(13 * L / 50)) (-(6 * L / 25)))).trans
                Rh.coordinatePartialHomeomorph.symm
            P ∈ H.necks ∧ (Q = P ∨ Q = P.reverse) ∧
            (Rh = R ∨ Rh = R.reverse) ∧
            Q.epsilon = H.epsilon ∧ Rh.epsilon = H.epsilon ∧
            Q.center = N.coordinate_map (q0, -(17 * L / 20)) ∧
            ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f ∧
            (∀ q, -(3 * L / 10) < f q ∧ f q < -(L / 5)) ∧
            Set.range (fun q : UnitTwoSphere =>
              B.coordinate_map (q, 3 * L / 4)) =
              Set.range (fun q : UnitTwoSphere =>
                Rh.coordinate_map (q, f q)) ∧
            ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ hN ∧
            (∀ q, -(9 * L / 10) < hN q ∧ hN q < -(4 * L / 5)) ∧
            Set.range (fun q : UnitTwoSphere =>
              N.coordinate_map (q, hN q)) =
              Set.range (fun q : UnitTwoSphere => Q.coordinate_map (q, 0)) ∧
            ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ hR ∧
            (∀ q, -(L / 5) < hR q ∧ hR q < 19 * L / 20) ∧
            Set.range (fun q : UnitTwoSphere =>
              Rh.coordinate_map (q, hR q)) =
              Set.range (fun q : UnitTwoSphere => Q.coordinate_map (q, -L / 4)) ∧
            (∀ (q : UnitTwoSphere) (s : ℝ), s ∈ Set.Icc (-L / 40) (L / 40) →
              Q.coordinate_map (q, s) ∈ N.carrier ∧
              (N.coordinate_inverse (Q.coordinate_map (q, s))).2 ∈
                Set.Ioo (-(9 * L / 10)) (-(4 * L / 5)) ∧
              0 < N.scale * mvfderiv (𝓡 3)
                (fun x => (N.coordinate_inverse x).2) (Q.coordinate_map (q, s))
                (Q.normalizedAxialVector (Q.coordinate_map (q, s)))) ∧
            (∀ (q : UnitTwoSphere) (s : ℝ),
              s ∈ Set.Icc (-(13 * L / 50)) (-(6 * L / 25)) →
              Q.coordinate_map (q, s) ∈ Rh.carrier ∧
              (Rh.coordinate_inverse (Q.coordinate_map (q, s))).2 ∈
                Set.Ioo (-(L / 5)) (19 * L / 20) ∧
              0 < Rh.scale * mvfderiv (𝓡 3)
                (fun x => (Rh.coordinate_inverse x).2) (Q.coordinate_map (q, s))
                (Q.normalizedAxialVector (Q.coordinate_map (q, s)))) ∧
            TN.source = Set.univ ×ˢ Set.Ioo (-L / 40) (L / 40) ∧
            TN.target = N.coordinate_inverse '' Q.region (-L / 40) (L / 40) ∧
            ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞
              TN TN.source ∧
            ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞
              TN.symm TN.target ∧
            (∀ z ∈ TN.source, TN z = N.coordinate_inverse (Q.coordinate_map z)) ∧
            (∀ z ∈ TN.target,
              TN.symm z = Q.coordinate_inverse (N.coordinate_map z)) ∧
            TR.source = Set.univ ×ˢ
              Set.Ioo (-(13 * L / 50)) (-(6 * L / 25)) ∧
            TR.target = Rh.coordinate_inverse ''
              Q.region (-(13 * L / 50)) (-(6 * L / 25)) ∧
            ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞
              TR TR.source ∧
            ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞
              TR.symm TR.target ∧
            (∀ z ∈ TR.source, TR z = Rh.coordinate_inverse (Q.coordinate_map z)) ∧
            (∀ z ∈ TR.target,
              TR.symm z = Q.coordinate_inverse (Rh.coordinate_map z)) ∧
            (∀ i ∈ C.shape.active, -L < lo i ∧ lo i ≤ -L / 2) ∧
            lo a = -L / 2 ∧
            -L < rlo ∧ rlo ≤ rhi ∧ rhi < L ∧
            (U ∪ R.carrier) ∪ Q.carrier =
              ((⋃ i ∈ C.shape.active,
                (C.neck i).coordinate_map ''
                  (Set.univ ×ˢ Set.Icc (lo i) (3 * L / 4))) ∪
                R.coordinate_map '' (Set.univ ×ˢ Set.Icc rlo rhi)) ∪
                Q.coordinate_map ''
                  (Set.univ ×ˢ Set.Icc (-(19 * L / 20)) (19 * L / 20)) := by
  obtain ⟨ec, hcp, hccap, runCover⟩ := NeckOnlyCover.exists_retained_return_cover.{u}
  obtain ⟨ej, hjp, _, hj⟩ :=
    BalancedNeckChain.exists_oriented_frontier_initial_height_control.{u}
  obtain ⟨eg, hgp, _, hg⟩ := EpsilonNeck.exists_oriented_positive_frontier_graph.{u}
  obtain ⟨el, hlp, _, runLine⟩ := EpsilonNeck.exists_signed_axial_line_control.{u}
  obtain ⟨ev, hvp, _, runSlice⟩ := EpsilonNeck.exists_buffered_slice_height_control.{u}
  obtain ⟨ep, hpp, _, composeSign⟩ := EpsilonNeck.exists_positive_cross_axis_composition.{u}
  obtain ⟨eo, hop, _, horient⟩ :=
    EpsilonNeck.exists_intersecting_coherent_orientation.{u} (η := (1 / 1000 : ℝ))
      (by constructor <;> norm_num)
  obtain ⟨eh, hhp, _, hhorizontal⟩ :=
    EpsilonNeck.exists_intersecting_transition_height_horizontal_bound.{u}
      (α := (1 : ℝ)) (by norm_num)
  obtain ⟨et, htp, _, graphSlice⟩ := EpsilonNeck.exists_contained_slice_graph.{u}
  let B0 : ℝ := Real.sqrt 2 * (Real.pi + 1)
  have hB0 : 0 < B0 := by dsimp only [B0]; positivity
  refine ⟨min ec (min ej (min eg (min el (min ev (min ep (min eo
    (min eh (min et (min (1 / 10000) (1 / (10000 * (B0 + Real.pi + 1)))))))))))),
    by positivity, (min_le_left _ _).trans hccap, ?_⟩
  intro M _ _ _ _ _ _ g H hepsilon hwhole C a b hshape
  classical
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
  let : ConnectedSpace UnitTwoSphere := by
    apply isConnected_iff_connectedSpace.mp
    exact isConnected_sphere (by rw [← Module.finrank_eq_rank]; norm_num) 0 (by norm_num)
  rcases le_min_iff.mp hepsilon with ⟨hec, hepsilon⟩
  rcases le_min_iff.mp hepsilon with ⟨hej, hepsilon⟩
  rcases le_min_iff.mp hepsilon with ⟨heg, hepsilon⟩
  rcases le_min_iff.mp hepsilon with ⟨hel, hepsilon⟩
  rcases le_min_iff.mp hepsilon with ⟨hev, hepsilon⟩
  rcases le_min_iff.mp hepsilon with ⟨hep, hepsilon⟩
  rcases le_min_iff.mp hepsilon with ⟨heo, hepsilon⟩
  rcases le_min_iff.mp hepsilon with ⟨heh, hepsilon⟩
  rcases le_min_iff.mp hepsilon with ⟨het, hepsilon⟩
  rcases le_min_iff.mp hepsilon with ⟨_, henumeric⟩
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
  obtain ⟨P, Qold, lo, rlo, rhi, hP, hQold, _, hQoldcenter, hlo, hloa,
    hrlo, hrorder, hrhi, hcoverOld⟩ :=
    runCover H hec hwhole C a b hshape R heR hy hout hreturn
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
  obtain ⟨Rh, f, hRh, hfsmooth, hfdom, hf0, hgraph0⟩ := hg B R (small B heB heg)
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
  have hPcenter : P.center = z := by
    rcases hQold with h | h
    · simpa only [h] using hQoldcenter
    · have hcenter : P.reverse.center = P.center := rfl
      simpa only [h, hcenter] using hQoldcenter
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

  have bandFromSlice (D : EpsilonNeck g) (heD : D.epsilon = H.epsilon)
      (s0 delta a0 b0 c d : ℝ) (hs0 : s0 ∈ Ioo (-L) L)
      (hc : -L < c) (hd : d < L)
      (hlow : c < a0 - (101 / 100 : ℝ) * delta)
      (hupp : b0 + (101 / 100 : ℝ) * delta < d)
      (hstart : ∀ q : UnitTwoSphere, Q.coordinate_map (q, s0) ∈ D.carrier ∧
        a0 < height D (Q.coordinate_map (q, s0)) ∧
        height D (Q.coordinate_map (q, s0)) < b0 ∧
        0 < cross Q D (Q.coordinate_map (q, s0))) :
      ∀ (q : UnitTwoSphere) (s : ℝ), s ∈ Ioo (-L) L → |s - s0| ≤ delta →
        Q.coordinate_map (q, s) ∈ D.carrier ∧
        height D (Q.coordinate_map (q, s)) ∈ Ioo c d ∧
        0 < cross Q D (Q.coordinate_map (q, s)) := by
    intro q s hs hdelta
    have hd0 : 0 ≤ delta := (abs_nonneg _).trans hdelta
    have hprefix (t : ℝ) (ht : t ∈ uIcc s0 s) : |t - s0| ≤ delta := by
      have hbds := abs_le.mp hdelta
      apply abs_le.mpr
      rcases le_total s0 s with hle | hge
      · rw [uIcc_of_le hle] at ht
        constructor <;> linarith only [ht.1, ht.2, hbds.2, hd0]
      · rw [uIcc_of_ge hge] at ht
        constructor <;> linarith only [ht.1, ht.2, hbds.1, hd0]
    have hline := line Q D heQ heD q s0 s 1 c d
      (interval Q heQ hs0) (interval Q heQ hs) (Or.inl rfl) (hstart q).1
      (by simpa only [one_mul] using (hstart q).2.2.2)
      (by simpa only [heD] using hc) (by simpa only [heD] using hd) (by
        intro t ht
        have hp := hprefix t ht
        have hbds := abs_le.mp hp
        change c ≤ height D (Q.coordinate_map (q, s0)) +
            1 * (t - s0) - (1 / 100 : ℝ) * |t - s0| ∧
          height D (Q.coordinate_map (q, s0)) +
            1 * (t - s0) + (1 / 100 : ℝ) * |t - s0| ≤ d
        constructor <;> linarith only [hlow, hupp, (hstart q).2.1,
          (hstart q).2.2.1, hbds.1, hbds.2, hp])
    have hh := hline s right_mem_uIcc
    have he := abs_le.mp hh.2.2.1
    have hbds := abs_le.mp hdelta
    refine ⟨hh.1, ⟨?_, ?_⟩, by simpa only [one_mul] using hh.2.2.2⟩ <;>
      linarith only [hlow, hupp, (hstart q).2.1, (hstart q).2.2.1,
        hbds.1, hbds.2, hdelta, he.1, he.2]
  have bandN (q : UnitTwoSphere) (s : ℝ) (hs : s ∈ Icc (-L / 40) (L / 40)) :
      Q.coordinate_map (q, s) ∈ N.carrier ∧
      height N (Q.coordinate_map (q, s)) ∈ Ioo (-(9 * L / 10)) (-(4 * L / 5)) ∧
      0 < cross Q N (Q.coordinate_map (q, s)) := by
    apply bandFromSlice N heN 0 (L / 40) (-(43 * L / 50)) (-(21 * L / 25))
      (-(9 * L / 10)) (-(4 * L / 5))
      ⟨by linarith only [hL], hL⟩
      (by linarith only [hL]) (by linarith only [hL])
      (by linarith only [hL]) (by linarith only [hL])
      (fun p => ⟨(hcentral p).1, (hcentralHeight p).1,
        (hcentralHeight p).2, (hcentral p).2.2⟩) q s
      ⟨by linarith only [hL, hs.1], by linarith only [hL, hs.2]⟩
    exact abs_le.mpr ⟨by linarith only [hs.1], by linarith only [hs.2]⟩
  have bandR (q : UnitTwoSphere) (s : ℝ)
      (hs : s ∈ Icc (-(13 * L / 50)) (-(6 * L / 25))) :
      Q.coordinate_map (q, s) ∈ Rh.carrier ∧
      height Rh (Q.coordinate_map (q, s)) ∈ Ioo (-(L / 5)) (19 * L / 20) ∧
      0 < cross Q Rh (Q.coordinate_map (q, s)) := by
    apply bandFromSlice Rh heRh (-L / 4) (L / 100) (-(9 * L / 50)) (93 * L / 100)
      (-(L / 5)) (19 * L / 20)
      ⟨by linarith only [hL], by linarith only [hL]⟩
      (by linarith only [hL]) (by linarith only [hL])
      (by linarith only [hL]) (by linarith only [hL])
      (fun p => ⟨(hQbase p).1, (hQbaseHeight p).1,
        (hQbaseHeight p).2, (hQbase p).2.2⟩) q s
      ⟨by linarith only [hL, hs.1], by linarith only [hL, hs.2]⟩
    apply abs_le.mpr
    constructor <;> linarith only [hs.1, hs.2]
  have wholeGraph (D : EpsilonNeck g) (heD : D.epsilon = H.epsilon)
      (s c d : ℝ) (hs : s ∈ Ioo (-L) L)
      (hm : ∀ q : UnitTwoSphere, Q.coordinate_map (q, s) ∈ D.carrier)
      (hbnd : ∀ q : UnitTwoSphere, c < height D (Q.coordinate_map (q, s)) ∧
        height D (Q.coordinate_map (q, s)) < d) :
      ∃ h : UnitTwoSphere → ℝ, ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ h ∧
        (∀ q, c < h q ∧ h q < d) ∧
        range (fun q => D.coordinate_map (q, h q)) =
          range (fun q => Q.coordinate_map (q, s)) := by
    obtain ⟨⟨h, hsm, hdom, hgph⟩, _⟩ := graphSlice D Q
      (small D heD het) (small Q heQ het) s (interval Q heQ hs) hm
    refine ⟨h, hsm, ?_, hgph⟩
    intro q
    have hx : D.coordinate_map (q, h q) ∈ range (fun p => Q.coordinate_map (p, s)) := by
      rw [← hgph]
      exact mem_range_self q
    obtain ⟨p, hp⟩ := hx
    change Q.coordinate_map (p, s) = D.coordinate_map (q, h q) at hp
    have hbound := hbnd p
    rw [hp] at hbound
    simpa only [height, D.coordinate_inverse_map (q, h q) (hdom q)] using hbound
  have hzero : (0 : ℝ) ∈ Icc (-L / 40) (L / 40) := by
    constructor <;> linarith only [hL]
  have hquarter : -L / 4 ∈ Icc (-(13 * L / 50)) (-(6 * L / 25)) := by
    constructor <;> linarith only [hL]
  obtain ⟨hN, hNsmooth, hNbounds, hNgraph⟩ :=
    wholeGraph N heN 0 (-(9 * L / 10)) (-(4 * L / 5))
      ⟨by linarith only [hL], hL⟩ (fun q => (bandN q 0 hzero).1)
      (fun q => (bandN q 0 hzero).2.1)
  obtain ⟨hR, hRsmooth, hRbounds, hRgraph⟩ :=
    wholeGraph Rh heRh (-L / 4) (-(L / 5)) (19 * L / 20)
      ⟨by linarith only [hL], by linarith only [hL]⟩
      (fun q => (bandR q (-L / 4) hquarter).1)
      (fun q => (bandR q (-L / 4) hquarter).2.1)

  have transition (D : EpsilonNeck g) (c d : ℝ) (hc : -L < c) (hd : d < L)
      (hsub : ∀ (q : UnitTwoSphere) (s : ℝ), s ∈ Ioo c d →
        Q.coordinate_map (q, s) ∈ D.carrier) :
      let J := univ ×ˢ Ioo c d
      let T := (Q.coordinatePartialHomeomorph.restr J).trans
        D.coordinatePartialHomeomorph.symm
      T.source = J ∧ T.target = D.coordinate_inverse '' Q.region c d ∧
      ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ T T.source ∧
      ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ T.symm T.target ∧
      (∀ z ∈ T.source, T z = D.coordinate_inverse (Q.coordinate_map z)) ∧
      (∀ z ∈ T.target, T.symm z = Q.coordinate_inverse (D.coordinate_map z)) := by
    let J : Set RoundCylinderSpace := univ ×ˢ Ioo c d
    let T := (Q.coordinatePartialHomeomorph.restr J).trans
      D.coordinatePartialHomeomorph.symm
    change T.source = J ∧ T.target = D.coordinate_inverse '' Q.region c d ∧
      ContMDiffOn _ _ ∞ T T.source ∧ ContMDiffOn _ _ ∞ T.symm T.target ∧
      (∀ z ∈ T.source, T z = D.coordinate_inverse (Q.coordinate_map z)) ∧
      (∀ z ∈ T.target, T.symm z = Q.coordinate_inverse (D.coordinate_map z))
    have hJopen : IsOpen J := isOpen_univ.prod isOpen_Ioo
    have hJdom : J ⊆ Q.cylinderDomain := by
      intro z hz
      exact dom Q heQ ⟨hc.trans hz.2.1, hz.2.2.trans hd⟩
    have hsrc : T.source = J := by
      change ((Q.coordinatePartialHomeomorph.restr J).trans
        D.coordinatePartialHomeomorph.symm).source = J
      rw [OpenPartialHomeomorph.trans_source,
        Q.coordinatePartialHomeomorph.restr_source' J hJopen]
      apply Subset.antisymm
      · intro z hz
        exact hz.1.2
      · intro z hz
        exact ⟨⟨hJdom hz, hz⟩, hsub z.1 z.2 hz.2⟩
    have himg : Q.coordinate_map '' J = Q.region c d := by
      apply Subset.antisymm
      · rintro x ⟨z, hz, rfl⟩
        refine ⟨Q.coordinate_map_mem (hJdom hz), ?_⟩
        rw [Q.coordinate_inverse_coordinate_map (hJdom hz)]
        exact hz.2
      · intro x hx
        exact ⟨Q.coordinate_inverse x, ⟨mem_univ _, hx.2⟩,
          Q.coordinate_map_inverse hx.1⟩
    have htgt : T.target = D.coordinate_inverse '' Q.region c d := by
      rw [← T.image_source_eq_target, hsrc, ← himg]
      change (fun z => D.coordinate_inverse (Q.coordinate_map z)) '' J =
        D.coordinate_inverse '' (Q.coordinate_map '' J)
      exact (image_image _ _ _).symm
    have htarget (z : RoundCylinderSpace) (hz : z ∈ T.target) :
        z ∈ D.cylinderDomain ∧ D.coordinate_map z ∈ Q.carrier := by
      rw [htgt] at hz
      obtain ⟨x, hx, rfl⟩ := hz
      have hxD : x ∈ D.carrier := by
        have hm := hsub (Q.coordinate_inverse x).1 (Q.coordinate_inverse x).2 hx.2
        rwa [Q.coordinate_map_inverse hx.1] at hm
      exact ⟨D.coordinate_inverse_mem x hxD,
        by rw [D.coordinate_map_inverse hxD]; exact hx.1⟩
    refine ⟨hsrc, htgt, ?_, ?_, fun _ _ => rfl, fun _ _ => rfl⟩
    · rw [hsrc]
      exact D.coordinate_inverse_smooth.comp (Q.coordinate_map_smooth.mono hJdom)
        (fun z hz => hsub z.1 z.2 hz.2)
    · exact Q.coordinate_inverse_smooth.comp
        (D.coordinate_map_smooth.mono (fun z hz => (htarget z hz).1))
        (fun z hz => (htarget z hz).2)
  obtain ⟨hTNsource, hTNtarget, hTNsmooth, hTNinv, hTNmap, hTNsymm⟩ :=
    transition N (-L / 40) (L / 40)
      (by linarith only [hL]) (by linarith only [hL])
      (fun q s hs => (bandN q s ⟨hs.1.le, hs.2.le⟩).1)
  obtain ⟨hTRsource, hTRtarget, hTRsmooth, hTRinv, hTRmap, hTRsymm⟩ :=
    transition Rh (-(13 * L / 50)) (-(6 * L / 25))
      (by linarith only [hL]) (by linarith only [hL])
      (fun q s hs => (bandR q s ⟨hs.1.le, hs.2.le⟩).1)

  let K : Set M := ⋃ i ∈ C.shape.active, slab (C.neck i) (lo i) (3 * L / 4)
  change (U ∪ R.carrier) ∪ Qold.carrier =
    (K ∪ slab R rlo rhi) ∪ slab Qold (-L / 2) (19 * L / 20) at hcoverOld
  have hsame : Qold.carrier = Q.carrier := by
    rcases hQold with rfl | rfl <;> rcases hQP with rfl | rfl <;> rfl
  have oldSlab : slab Qold (-L / 2) (19 * L / 20) ⊆
      slab Q (-(19 * L / 20)) (19 * L / 20) := by
    rintro x ⟨⟨q, s⟩, hs, rfl⟩
    rcases hQold with rfl | rfl <;> rcases hQP with rfl | rfl
    · exact ⟨(q, s), ⟨mem_univ _, by
        constructor <;> linarith only [hL, hs.2.1, hs.2.2]⟩, rfl⟩
    · refine ⟨(q, -s), ⟨mem_univ _, ?_⟩, ?_⟩
      · constructor <;> linarith only [hL, hs.2.1, hs.2.2]
      · simp only [EpsilonNeck.reverse, neg_neg]
    · refine ⟨(q, -s), ⟨mem_univ _, ?_⟩, rfl⟩
      constructor <;> linarith only [hL, hs.2.1, hs.2.2]
    · exact ⟨(q, s), ⟨mem_univ _, by
        constructor <;> linarith only [hL, hs.2.1, hs.2.2]⟩, rfl⟩
  have hcover : (U ∪ R.carrier) ∪ Q.carrier =
      (K ∪ slab R rlo rhi) ∪ slab Q (-(19 * L / 20)) (19 * L / 20) := by
    apply Subset.antisymm
    · intro x hx
      have hxold : x ∈ (U ∪ R.carrier) ∪ Qold.carrier := by rwa [hsame]
      rw [hcoverOld] at hxold
      exact hxold.elim Or.inl (fun h => Or.inr (oldSlab h))
    · rintro x ((hx | hx) | hx)
      · obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
        exact Or.inl (Or.inl (mem_iUnion₂.mpr ⟨i, hi,
          slabSub (C.neck i) (C.epsilon_eq i hi) (hlo i hi).1
            (by linarith only [hL]) hxi⟩))
      · exact Or.inl (Or.inr (slabSub R heR hrlo hrhi hx))
      · exact Or.inr (slabSub Q heQ
          (by linarith only [hL]) (by linarith only [hL]) hx)
  exact ⟨P, Q, Rh, f, hN, hR, lo, rlo, rhi, hP, hQP, hRh, heQ, heRh, hQcenter,
    hfsmooth, hf, hgraph, hNsmooth, hNbounds, hNgraph, hRsmooth, hRbounds, hRgraph,
    bandN, bandR, hTNsource, hTNtarget, hTNsmooth, hTNinv, hTNmap, hTNsymm,
    hTRsource, hTRtarget, hTRsmooth, hTRinv, hTRmap, hTRsymm, hlo, hloa,
    hrlo, hrorder, hrhi, hcover⟩

end PoincareConjecture
