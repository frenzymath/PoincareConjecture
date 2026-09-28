import PoincareConjecture.Proofs.M25.AppA_20_Fibration.FrontierInitialHeight
import PoincareConjecture.Proofs.M25.AppA_1_Necks.OrientedFrontierGraph
import PoincareConjecture.Proofs.M25.AppA_1_Necks.AxialLineContinuation
import PoincareConjecture.Proofs.M25.AppA_1_Necks.BufferedSliceHeight
import PoincareConjecture.Proofs.M25.AppA_1_Necks.AxialSignComposition
import PoincareConjecture.Proofs.M25.AppA_20_Fibration.Cyclic

set_option autoImplicit false
open Set
open scoped Manifold ContDiff ENNReal
universe u
namespace PoincareConjecture










set_option maxHeartbeats 600000 in




theorem NeckOnlyCover.exists_local_negative_return_geometry :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T3Space M] {g : RiemannianMetric 3 M},
      ∀ (H : NeckOnlyCover g), H.epsilon ≤ epsilon0 →
      ∀ (C : BalancedNeckChain g H.epsilon),
      ∀ a b : ℤ, C.shape = ChainShape.finite a b →
        let L := H.epsilon⁻¹
        let N := C.neck a
        let B := C.neck b
        let U : Set M := ⋃ i ∈ C.shape.active, (C.neck i).carrier
        ∀ (R : EpsilonNeck g), R.epsilon = H.epsilon →
          R.center ∈ closure (B.region 0 L) → R.center ∉ U →
          (∀ t ∈ Set.Ioo (-L) 0,
            ¬ Disjoint R.carrier (N.region (-L) t)) →
          ∀ (P : EpsilonNeck g), P ∈ H.necks →
            P.center ∈ H.X ∩ N.region (-L) (-(4 * L / 5)) →
            let v := (N.coordinate_inverse P.center).2
            let c := -(17 * L / 20) - v
            ∃ (Q Rh : EpsilonNeck g) (w : M)
              (f hN hR : UnitTwoSphere → ℝ)
              (lo : ℤ → ℝ) (rlo rhi : ℝ),
              let V := (U ∪ R.carrier) ∪ Q.carrier
              (Q = P ∨ Q = P.reverse) ∧
              (Rh = R ∨ Rh = R.reverse) ∧
              Q.epsilon = H.epsilon ∧ Rh.epsilon = H.epsilon ∧
              w ∈ N.carrier ∩ Rh.carrier ∩ Q.carrier ∧
              (N.coordinate_inverse w).2 < -(999 * L / 1000) ∧
              -(L / 20) < (Rh.coordinate_inverse w).2 ∧
              |(Q.coordinate_inverse w).2 -
                ((N.coordinate_inverse w).2 - v)| ≤ 21 * L / 10000 ∧
              0 < N.scale * mvfderiv (𝓡 3)
                (fun x => (N.coordinate_inverse x).2) w
                (Rh.normalizedAxialVector w) ∧
              0 < Q.scale * mvfderiv (𝓡 3)
                (fun x => (Q.coordinate_inverse x).2) w
                (N.normalizedAxialVector w) ∧
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
                Set.range (fun q : UnitTwoSphere => Q.coordinate_map (q, c)) ∧
              ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ hR ∧
              (∀ q, -(L / 5) < hR q ∧ hR q < 19 * L / 20) ∧
              Set.range (fun q : UnitTwoSphere =>
                Rh.coordinate_map (q, hR q)) =
                Set.range (fun q : UnitTwoSphere =>
                  Q.coordinate_map (q, c - L / 4)) ∧
              (∀ (q : UnitTwoSphere) (s : ℝ),
                s ∈ Set.Icc (c - L / 40) (c + L / 40) →
                Q.coordinate_map (q, s) ∈ N.carrier ∧
                (N.coordinate_inverse (Q.coordinate_map (q, s))).2 ∈
                  Set.Ioo (-(9 * L / 10)) (-(4 * L / 5)) ∧
                0 < N.scale * mvfderiv (𝓡 3)
                  (fun x => (N.coordinate_inverse x).2) (Q.coordinate_map (q, s))
                  (Q.normalizedAxialVector (Q.coordinate_map (q, s)))) ∧
              (∀ (q : UnitTwoSphere) (s : ℝ),
                s ∈ Set.Icc (c - 13 * L / 50) (c - 6 * L / 25) →
                Q.coordinate_map (q, s) ∈ Rh.carrier ∧
                (Rh.coordinate_inverse (Q.coordinate_map (q, s))).2 ∈
                  Set.Ioo (-(L / 5)) (19 * L / 20) ∧
                0 < Rh.scale * mvfderiv (𝓡 3)
                  (fun x => (Rh.coordinate_inverse x).2) (Q.coordinate_map (q, s))
                  (Q.normalizedAxialVector (Q.coordinate_map (q, s)))) ∧
              (∀ i ∈ C.shape.active, -L < lo i ∧ lo i ≤ -L / 2) ∧
              lo a = -(19 * L / 20) ∧
              -L < rlo ∧ rlo ≤ rhi ∧ rhi < L ∧
              V =
                ((⋃ i ∈ C.shape.active,
                  (C.neck i).coordinate_map ''
                    (Set.univ ×ˢ Set.Icc (lo i) (3 * L / 4))) ∪
                  R.coordinate_map '' (Set.univ ×ˢ Set.Icc rlo rhi)) ∪
                  Q.coordinate_map ''
                    (Set.univ ×ˢ Set.Icc (-(19 * L / 20)) (19 * L / 20)) ∧
              IsCompact V ∧ V = connectedComponent P.center ∧ H.X ⊆ V := by
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
  obtain ⟨et, htp, _, graph⟩ := EpsilonNeck.exists_contained_slice_graph.{u}
  let B0 : ℝ := Real.sqrt 2 * (Real.pi + 1)
  have hB0 : 0 < B0 := by dsimp only [B0]; positivity
  refine ⟨min ej (min ek (min eg (min el (min ev (min ep (min es
    (min eo (min et (min (1 / 10000) (1 / (10000 * (B0 + Real.pi + 1)))))))))))),
    by positivity, (min_le_left _ _).trans hjcap, ?_⟩
  intro M _ _ _ _ _ _ g H hepsilon C a b hshape
  classical
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
  rcases le_min_iff.mp hepsilon with ⟨hej, hepsilon⟩
  rcases le_min_iff.mp hepsilon with ⟨hek, hepsilon⟩
  rcases le_min_iff.mp hepsilon with ⟨heg, hepsilon⟩
  rcases le_min_iff.mp hepsilon with ⟨hel, hepsilon⟩
  rcases le_min_iff.mp hepsilon with ⟨hev, hepsilon⟩
  rcases le_min_iff.mp hepsilon with ⟨hep, hepsilon⟩
  rcases le_min_iff.mp hepsilon with ⟨hes, hepsilon⟩
  rcases le_min_iff.mp hepsilon with ⟨heo, hepsilon⟩
  rcases le_min_iff.mp hepsilon with ⟨het, hepsilon⟩
  rcases le_min_iff.mp hepsilon with ⟨hesmall, henumeric⟩
  let L := H.epsilon⁻¹
  let N := C.neck a
  let B := C.neck b
  let U : Set M := ⋃ i ∈ C.shape.active, (C.neck i).carrier
  let height (A : EpsilonNeck g) (x : M) := (A.coordinate_inverse x).2
  let cross (A D : EpsilonNeck g) (x : M) := D.scale *
    mvfderiv (𝓡 3) (fun y => (D.coordinate_inverse y).2) x (A.normalizedAxialVector x)
  let slab (A : EpsilonNeck g) (c d : ℝ) := A.coordinate_map '' (univ ×ˢ Icc c d)
  let F : M → ℝ := fun x => if x ∈ N.carrier then height N x else L
  dsimp only
  intro R heR hy hout hreturn P hP hz
  let z := P.center
  let v := height N z
  let c := -(17 * L / 20) - v
  have hzN : z ∈ N.carrier := hz.2.1
  have hv : -L < v ∧ v < -(4 * L / 5) := hz.2.2
  have hL : 0 < L := inv_pos.mpr H.epsilon_pos
  have hactive (i : ℤ) : i ∈ C.shape.active ↔ i ∈ Icc a b := by rw [hshape]; rfl
  have hab : a ≤ b := by
    obtain ⟨i, hi⟩ := C.active_nonempty
    exact ((hactive i).mp hi).1.trans ((hactive i).mp hi).2
  have ha := (hactive a).mpr ⟨le_rfl, hab⟩
  have hb := (hactive b).mpr ⟨hab, le_rfl⟩
  have heN : N.epsilon = H.epsilon := C.epsilon_eq a ha
  have heB : B.epsilon = H.epsilon := C.epsilon_eq b hb
  have heP := H.neck_epsilon P hP
  have hNU : N.carrier ⊆ U := fun _ hx => mem_iUnion₂.mpr ⟨a, ha, hx⟩
  have hBU : B.carrier ⊆ U := fun _ hx => mem_iUnion₂.mpr ⟨b, hb, hx⟩
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
      {l r : ℝ} (hs : height A x ∈ Icc l r) : x ∈ slab A l r :=
    ⟨A.coordinate_inverse x, ⟨mem_univ _, hs⟩, A.coordinate_map_inverse hx⟩
  have slabSub (A : EpsilonNeck g) (heA : A.epsilon = H.epsilon)
      {l r : ℝ} (hl : -L < l) (hr : r < L) : slab A l r ⊆ A.carrier := by
    rintro x ⟨z, hz, rfl⟩
    exact A.coordinate_map_mem (dom A heA ⟨hl.trans_le hz.2.1, hz.2.2.trans_lt hr⟩)
  have slabCompact (A : EpsilonNeck g) (heA : A.epsilon = H.epsilon)
      {l r : ℝ} (hl : -L < l) (hr : r < L) : IsCompact (slab A l r) :=
    A.isCompact_coordinate_image_Icc l r (by simpa only [heA] using hl)
      (by simpa only [heA] using hr)
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
        exact ⟨A.coordinate_inverse_mem x hxA, by
          change A.coordinate_map (A.coordinate_inverse x) ∈ D.carrier
          rwa [A.coordinate_map_inverse hxA]⟩)
    have h := hc (A.coordinate_inverse x) (mem_singleton _)
    rw [A.coordinate_map_inverse hxA] at h
    have hh : |1 - sigma * cross A D x| < (1 / 1000 : ℝ) := by
      simpa only [cross, mul_assoc] using h
    exact ⟨sigma, hsigma, by linarith only [(abs_lt.mp hh).2]⟩
  have reciprocal (A D : EpsilonNeck g) (heA : A.epsilon = H.epsilon)
      (heD : D.epsilon = H.epsilon) {x : M} (hxA : x ∈ A.carrier)
      (hxD : x ∈ D.carrier) (hp : 0 < cross A D x) : 0 < cross D A x :=
    (composeSign A A D (small A heA hep) (small A heA hep) (small D heD hep)
      x hxA hxA hxD (by simpa only [cross, A.normalizedAxialVector_axial_mvfderiv hxA]
        using (zero_lt_one : (0 : ℝ) < 1)) hp).2
  have sliceAt (A D : EpsilonNeck g) (heA : A.epsilon = H.epsilon)
      (heD : D.epsilon = H.epsilon) (p : UnitTwoSphere) (s : ℝ)
      (hs : s ∈ Ioo (-L) L) (hx : A.coordinate_map (p, s) ∈ D.carrier)
      (hh : |height D (A.coordinate_map (p, s))| ≤ (99 / 100 : ℝ) * L)
      (hp : 0 < cross A D (A.coordinate_map (p, s))) :
      ∀ q, A.coordinate_map (q, s) ∈ D.carrier ∧
        |height D (A.coordinate_map (q, s)) - height D (A.coordinate_map (p, s))| ≤
          Real.pi ∧ 0 < cross A D (A.coordinate_map (q, s)) := by
    obtain ⟨hm, ho, sigma, hsigma, hc⟩ := runSlice A D (small A heA hev)
      (heD.trans heA.symm) p s (interval A heA hs) hx (by simpa only [heD] using hh)
    have hsig : sigma = 1 := by
      rcases hsigma with rfl | rfl
      · rfl
      · have hh := (hc p).2
        change 0 < (-1 : ℝ) * cross A D (A.coordinate_map (p, s)) at hh
        norm_num only [neg_one_mul] at hh
        linarith only [hp, hh]
    subst sigma
    exact fun q => ⟨hm q, ho p q, by simpa only [one_mul] using (hc q).2⟩
  let line (A D : EpsilonNeck g) (heA : A.epsilon = H.epsilon)
      (heD : D.epsilon = H.epsilon) := runLine A D (small A heA hel) (heD.trans heA.symm)

  have walk (A D : EpsilonNeck g) (heA : A.epsilon = H.epsilon)
      (heD : D.epsilon = H.epsilon) (q : UnitTwoSphere) (s t l r : ℝ)
      (hs : s ∈ Ioo (-L) L) (ht : t ∈ Ioo (-L) L)
      (hx : A.coordinate_map (q, s) ∈ D.carrier)
      (hp : 0 < cross A D (A.coordinate_map (q, s))) (hl : -L < l) (hr : r < L)
      (h0 : height D (A.coordinate_map (q, s)) ∈ Icc l r)
      (h1 : l ≤ height D (A.coordinate_map (q, s)) + (t - s) -
          (1 / 100 : ℝ) * |t - s| ∧
        height D (A.coordinate_map (q, s)) + (t - s) +
          (1 / 100 : ℝ) * |t - s| ≤ r) :
      A.coordinate_map (q, t) ∈ D.carrier ∧
        height D (A.coordinate_map (q, t)) ∈ Icc l r ∧
        |height D (A.coordinate_map (q, t)) - height D (A.coordinate_map (q, s)) -
          (t - s)| ≤ (1 / 100 : ℝ) * |t - s| ∧
        0 < cross A D (A.coordinate_map (q, t)) := by
    have hh := line A D heA heD q s t 1 l r (interval A heA hs) (interval A heA ht)
      (Or.inl rfl) hx (by simpa only [one_mul] using hp)
      (by simpa only [heD] using hl) (by simpa only [heD] using hr) (by
        intro v hv
        simp only [one_mul]
        rcases le_total s t with hst | hts
        · rw [uIcc_of_le hst] at hv
          rw [abs_of_nonneg (sub_nonneg.mpr hst)] at h1
          rw [abs_of_nonneg (sub_nonneg.mpr hv.1)]
          constructor <;> linarith only [h0.1, h0.2, h1.1, h1.2, hv.1, hv.2]
        · rw [uIcc_of_ge hts] at hv
          rw [abs_of_nonpos (sub_nonpos.mpr hts)] at h1
          rw [abs_of_nonpos (sub_nonpos.mpr hv.2)]
          constructor <;> linarith only [h0.1, h0.2, h1.1, h1.2, hv.1, hv.2])
    simpa only [one_mul] using hh t right_mem_uIcc
  obtain ⟨Rh, f, hRh, hfs, hfdom, hf0, hg0⟩ := hg B R (small B heB heg)
    (heR.trans heB.symm) (by simpa only [heB] using hy) (fun hx => hout (hBU hx))
  have heRh : Rh.epsilon = H.epsilon := by rcases hRh with rfl | rfl <;> exact heR
  have hcRh : Rh.carrier = R.carrier := by rcases hRh with rfl | rfl <;> rfl
  have hyRh : Rh.center = R.center := by rcases hRh with rfl | rfl <;> rfl
  have hf (q) : -(3 * L / 10) < f q ∧ f q < -(L / 5) := by
    simpa only [heB] using hf0 q
  have hgSp : range (fun q => B.coordinate_map (q, 3 * L / 4)) =
      range (fun q => Rh.coordinate_map (q, f q)) := by simpa only [heB] using hg0
  have hJ := hj C hej a b hshape Rh heRh (by rwa [hyRh]) (by rwa [hyRh]) f hf hgSp
  change (∀ q, 7 * L / 10 < F (B.coordinate_map (q, 3 * L / 4))) ∧
    (∀ q s, -L < s → s ≤ -(L / 20) →
      Rh.coordinate_map (q, s) ∈ U ∧ -(L / 5) < F (Rh.coordinate_map (q, s))) at hJ
  have hgraphHeight (q) : 7 * L / 10 < F (Rh.coordinate_map (q, f q)) := by
    obtain ⟨p, hp⟩ := hgSp.symm ▸ mem_range_self (f := fun q => Rh.coordinate_map (q, f q)) q
    rw [← hp]; exact hJ.1 p
  obtain ⟨w, hwR, hwN, hu0, hu1⟩ := Set.not_disjoint_iff.mp
    (hreturn (-(999 * L / 1000)) ⟨by linarith only [hL], by linarith only [hL]⟩)
  change w ∈ N.carrier at hwN
  have hwRh : w ∈ Rh.carrier := hcRh.symm ▸ hwR
  let u := height N w
  let r0 := height Rh w
  let qr := (Rh.coordinate_inverse w).1
  change -L < u at hu0
  change u < -(999 * L / 1000) at hu1
  have hRw : Rh.coordinate_map (qr, r0) = w := Rh.coordinate_map_inverse hwRh
  have hr0 : -(L / 20) < r0 ∧ r0 < L := by
    refine ⟨?_, (coord Rh heRh hwRh).2⟩
    by_contra h
    have hh := (hJ.2 qr r0 (coord Rh heRh hwRh).1 (le_of_not_gt h)).2
    rw [hRw] at hh; simp only [F, if_pos hwN] at hh
    linarith only [hh, hu1, hL]
  have hreturnSign : 0 < cross Rh N w := by
    obtain ⟨sigma, hsigma, hs⟩ := pointSign Rh N heRh heN w hwRh hwN
    rcases hsigma with rfl | rfl
    · simpa only [one_mul] using hs
    · have hline := line Rh N heRh heN qr r0 (f qr) (-1) u (8 * L / 25)
        (interval Rh heRh (coord Rh heRh hwRh)) (hfdom qr) (Or.inr rfl)
        (by rwa [hRw]) (by change 0 < -1 * cross Rh N _; rwa [hRw])
        (by simpa only [heN] using hu0) (by rw [heN]; linarith only [hL]) (by
          intro t ht
          rw [uIcc_of_ge (by linarith only [(hf qr).2, hr0.1, hL] : f qr ≤ r0)] at ht
          rw [hRw, abs_of_nonpos (sub_nonpos.mpr ht.2)]
          constructor <;> linarith only [(hf qr).1, hr0.2, ht.1, ht.2, hu1, hL])
      have hend := hline (f qr) right_mem_uIcc
      have hh := hgraphHeight qr; simp only [F, if_pos hend.1] at hh
      linarith only [hh, hend.2.1.2, hL]
  have hzP : z ∈ P.carrier := P.central_sphere_subset P.center_on_central_sphere
  obtain ⟨sigma, hsigma, hsig⟩ := pointSign N P heN heP z hzN hzP
  obtain ⟨Q, hQP, heQ, hQc, hQsign⟩ : ∃ Q : EpsilonNeck g,
      (Q = P ∨ Q = P.reverse) ∧ Q.epsilon = H.epsilon ∧ Q.center = z ∧
        0 < cross N Q z := by
    rcases hsigma with rfl | rfl
    · exact ⟨P, Or.inl rfl, heP, rfl, by simpa only [one_mul] using hsig⟩
    · refine ⟨P.reverse, Or.inr rfl, heP, rfl, ?_⟩
      change 0 < P.scale * mvfderiv (𝓡 3) (fun y => -(P.coordinate_inverse y).2) z _
      rw [mvfderiv_fun_neg]
      simpa only [neg_apply, mul_neg, neg_one_mul, cross] using hsig
  have hzQ : z ∈ Q.carrier := hQc ▸ Q.central_sphere_subset Q.center_on_central_sphere
  have hQzero : height Q z = 0 := by
    rw [← hQc]; exact ((Q.mem_central_sphere_iff _).mp Q.center_on_central_sphere).2
  let qz := (N.coordinate_inverse z).1
  have hNz : N.coordinate_map (qz, v) = z := N.coordinate_map_inverse hzN
  have calibration (t : ℝ) (ht : t ∈ Ioo (-L) (-(2 * L / 5))) (q : UnitTwoSphere) :
      N.coordinate_map (q, t) ∈ Q.carrier ∧ 0 < cross N Q (N.coordinate_map (q, t)) ∧
        |height Q (N.coordinate_map (q, t)) - (t - v)| ≤
          (1 / 100 : ℝ) * |t - v| + Real.pi := by
    have htL : t ∈ Ioo (-L) L := ⟨ht.1, by linarith only [ht.2, hL]⟩
    have hh := walk N Q heN heQ qz v t (-(21 * L / 100)) (61 * L / 100)
      (coord N heN hzN) htL (by rwa [hNz]) (by rwa [hNz])
      (by linarith only [hL]) (by linarith only [hL])
      (by rw [hNz, hQzero]; constructor <;> linarith only [hL]) (by
        rw [hNz, hQzero]
        rcases le_total v t with h | h
        · rw [abs_of_nonneg (sub_nonneg.mpr h)]
          constructor <;> linarith only [hv.1, hv.2, ht.1, ht.2, h, hL]
        · rw [abs_of_nonpos (sub_nonpos.mpr h)]
          constructor <;> linarith only [hv.1, hv.2, ht.1, ht.2, h, hL])
    have hs := sliceAt N Q heN heQ qz t htL hh.1
      (by apply abs_le.mpr; constructor <;> linarith only [hh.2.1.1, hh.2.1.2, hL]) hh.2.2.2 q
    have he := hh.2.2.1; rw [hNz, hQzero, sub_zero] at he
    refine ⟨hs.1, hs.2.2, ?_⟩
    simpa only [add_comm] using (abs_sub_le _ _ _).trans (add_le_add hs.2.1 he)
  have hwcal := calibration u ⟨hu0, by linarith only [hu1, hL]⟩ (N.coordinate_inverse w).1
  rw [N.coordinate_map_inverse hwN] at hwcal
  have hwQ := hwcal.1
  let t0 := height Q w
  let qw := (Q.coordinate_inverse w).1
  have hQw : Q.coordinate_map (qw, t0) = w := Q.coordinate_map_inverse hwQ
  have he : |t0 - (u - v)| ≤ 21 * L / 10000 := by
    have hdelta : |u - v| ≤ L / 5 :=
      abs_le.mpr ⟨by linarith only [hu0, hv.2], by linarith only [hu1, hv.1, hL]⟩
    linarith only [hwcal.2.2, hdelta, hnumeric.2]
  have ht0 : -(203 * L / 1000) < t0 ∧ t0 < L / 500 := by
    constructor
    · linarith only [(abs_le.mp he).1, hu0, hv.2, hL]
    · have hh := (abs_le.mp hwcal.2.2).2
      rcases le_total v u with h | h
      · rw [abs_of_nonneg (sub_nonneg.mpr h)] at hh
        linarith only [hh, hu1, hv.1, hnumeric.2, hL]
      · rw [abs_of_nonpos (sub_nonpos.mpr h)] at hh
        linarith only [hh, h, hnumeric.2, hL]
  have hc : -(L / 20) < c ∧ c < 3 * L / 20 := by
    dsimp only [c]; constructor <;> linarith only [hv.1, hv.2]
  have hd : 1469 * L / 10000 < c - t0 ∧ c - t0 < 1521 * L / 10000 := by
    dsimp only [c]; constructor <;> linarith only [(abs_le.mp he).1, (abs_le.mp he).2, hu0, hu1]
  have signs := composeSign Rh N Q (small Rh heRh hep) (small N heN hep)
    (small Q heQ hep) w hwRh hwN hwQ hreturnSign hwcal.2.1
  have hQN := reciprocal N Q heN heQ hwN hwQ hwcal.2.1
  have up := walk Q N heQ heN qw t0 c u (-(21 * L / 25))
    (coord Q heQ hwQ) ⟨by linarith only [hc.1, hL], by linarith only [hc.2, hL]⟩
    (by rwa [hQw]) (by rwa [hQw]) hu0 (by linarith only [hL])
    (by rw [hQw]; exact ⟨le_rfl, by linarith only [hu1, hL]⟩) (by
      rw [hQw, abs_of_pos (by linarith only [hd.1, hL] : 0 < c - t0)]
      constructor <;> linarith only [hd.1, hd.2, hu1, hL])
  have hn0 : -(171 * L / 200) < height N (Q.coordinate_map (qw, c)) ∧
      height N (Q.coordinate_map (qw, c)) < -(169 * L / 200) := by
    have hh := up.2.2.1
    rw [hQw, abs_of_pos (by linarith only [hd.1, hL] : 0 < c - t0)] at hh
    constructor <;> linarith only [(abs_le.mp hh).1, (abs_le.mp hh).2, hd.1, hd.2, hu0, hu1]
  have hNbase := sliceAt Q N heQ heN qw c
    ⟨by linarith only [hc.1, hL], by linarith only [hc.2, hL]⟩ up.1
    (by apply abs_le.mpr; constructor <;> linarith only [hn0.1, hn0.2, hL]) up.2.2.2
  have hNb (q) : -(43 * L / 50) < height N (Q.coordinate_map (q, c)) ∧
      height N (Q.coordinate_map (q, c)) < -(21 * L / 25) := by
    have hh := abs_le.mp (hNbase q).2.1
    constructor <;> linarith only [hh.1, hh.2, hn0.1, hn0.2, hnumeric.2, hL]
  let cR := c - L / 4
  have hcR : -(3 * L / 10) < cR ∧ cR < -(L / 10) := by
    dsimp only [cR]; constructor <;> linarith only [hc.1, hc.2]
  have hdt : -(1031 * L / 10000) < cR - t0 ∧ cR - t0 < -(979 * L / 10000) := by
    dsimp only [cR]; constructor <;> linarith only [hd.1, hd.2]
  have down := walk Q Rh heQ heRh qw t0 cR (-(4 * L / 25)) r0
    (coord Q heQ hwQ) ⟨by linarith only [hcR.1, hL], by linarith only [hcR.2, hL]⟩
    (by rwa [hQw]) (by rw [hQw]; exact signs.2) (by linarith only [hL]) hr0.2
    (by rw [hQw]; exact ⟨by linarith only [hr0.1, hL], le_rfl⟩) (by
      rw [hQw, abs_of_neg (by linarith only [hdt.2, hL] : cR - t0 < 0)]
      constructor <;> linarith only [hdt.1, hdt.2, hr0.1, hL])
  have hde := down.2.2.1
  rw [hQw, abs_of_neg (by linarith only [hdt.2, hL] : cR - t0 < 0)] at hde
  have hRbase := sliceAt Q Rh heQ heRh qw cR
    ⟨by linarith only [hcR.1, hL], by linarith only [hcR.2, hL]⟩ down.1
    (by apply abs_le.mpr; constructor <;>
      linarith only [(abs_le.mp hde).1, (abs_le.mp hde).2, hdt.1, hdt.2, hr0.1, hr0.2, hL])
    down.2.2.2
  have hRsharp (q) : r0 - 104231 * L / 1000000 < height Rh (Q.coordinate_map (q, cR)) ∧
      height Rh (Q.coordinate_map (q, cR)) < r0 - 96821 * L / 1000000 := by
    have hh := abs_le.mp (hRbase q).2.1
    constructor <;> linarith only [hh.1, hh.2, (abs_le.mp hde).1,
      (abs_le.mp hde).2, hdt.1, hdt.2, hnumeric.2]
  have hRb (q) : -(4 * L / 25) < height Rh (Q.coordinate_map (q, cR)) ∧
      height Rh (Q.coordinate_map (q, cR)) < 91 * L / 100 := by
    constructor <;> linarith only [(hRsharp q).1, (hRsharp q).2, hr0.1, hr0.2, hL]
  have bandN (q) (s : ℝ) (hs : s ∈ Icc (c - L / 40) (c + L / 40)) :
      Q.coordinate_map (q, s) ∈ N.carrier ∧ height N (Q.coordinate_map (q, s)) ∈
        Ioo (-(9 * L / 10)) (-(4 * L / 5)) ∧ 0 < cross Q N (Q.coordinate_map (q, s)) := by
    have habs : |s - c| ≤ L / 40 :=
      abs_le.mpr ⟨by linarith only [hs.1], by linarith only [hs.2]⟩
    have hh := walk Q N heQ heN q c s (-(89 * L / 100)) (-(81 * L / 100))
      ⟨by linarith only [hc.1, hL], by linarith only [hc.2, hL]⟩
      ⟨by linarith only [hc.1, hs.1, hL], by linarith only [hc.2, hs.2, hL]⟩
      (hNbase q).1 (hNbase q).2.2 (by linarith only [hL]) (by linarith only [hL])
      (by constructor <;> linarith only [(hNb q).1, (hNb q).2, hL])
      (by constructor <;> linarith only [(hNb q).1, (hNb q).2, hs.1, hs.2, habs, hL])
    exact ⟨hh.1, ⟨by linarith only [hh.2.1.1, hL],
      by linarith only [hh.2.1.2, hL]⟩, hh.2.2.2⟩
  have bandR (q) (s : ℝ) (hs : s ∈ Icc (c - 13 * L / 50) (c - 6 * L / 25)) :
      Q.coordinate_map (q, s) ∈ Rh.carrier ∧ height Rh (Q.coordinate_map (q, s)) ∈
        Ioo (-(L / 5)) (19 * L / 20) ∧ 0 < cross Q Rh (Q.coordinate_map (q, s)) := by
    have habs : |s - cR| ≤ L / 100 := by
      dsimp only [cR]; exact abs_le.mpr ⟨by linarith only [hs.1], by linarith only [hs.2]⟩
    have hh := walk Q Rh heQ heRh q cR s (-(9 * L / 50)) (93 * L / 100)
      ⟨by linarith only [hcR.1, hL], by linarith only [hcR.2, hL]⟩
      ⟨by linarith only [hc.1, hs.1, hL], by linarith only [hc.2, hs.2, hL]⟩
      (hRbase q).1 (hRbase q).2.2 (by linarith only [hL]) (by linarith only [hL])
      (by constructor <;> linarith only [(hRb q).1, (hRb q).2, hL]) (by
        have hh := abs_le.mp habs
        constructor <;> linarith only [(hRb q).1, (hRb q).2, hh.1, hh.2, habs, hL])
    exact ⟨hh.1, ⟨by linarith only [hh.2.1.1, hL],
      by linarith only [hh.2.1.2, hL]⟩, hh.2.2.2⟩
  have graphAt (D : EpsilonNeck g) (heD : D.epsilon = H.epsilon) (s l r : ℝ)
      (hs : s ∈ Ioo (-L) L) (hm : ∀ q, Q.coordinate_map (q, s) ∈ D.carrier)
      (hb : ∀ q, height D (Q.coordinate_map (q, s)) ∈ Ioo l r) :
      ∃ h : UnitTwoSphere → ℝ, ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ h ∧
        (∀ q, h q ∈ Ioo l r) ∧ range (fun q => D.coordinate_map (q, h q)) =
          range (fun q => Q.coordinate_map (q, s)) := by
    obtain ⟨h, hh, hdom, hg⟩ :=
      (graph D Q (small D heD het) (small Q heQ het) s (interval Q heQ hs) hm).1
    refine ⟨h, hh, ?_, hg⟩
    intro q
    obtain ⟨p, hp⟩ := hg ▸ mem_range_self (f := fun q => D.coordinate_map (q, h q)) q
    change Q.coordinate_map (p, s) = D.coordinate_map (q, h q) at hp
    have hbq := hb p; rw [hp] at hbq
    change (D.coordinate_inverse (D.coordinate_map (q, h q))).2 ∈ Ioo l r at hbq
    rwa [D.coordinate_inverse_map (q, h q) (hdom q)] at hbq
  obtain ⟨hN, hhN, bhN, ghN⟩ := graphAt N heN c (-(9 * L / 10)) (-(4 * L / 5))
    ⟨by linarith only [hc.1, hL], by linarith only [hc.2, hL]⟩ (fun q => (hNbase q).1)
    (fun q => ⟨by linarith only [(hNb q).1, hL], by linarith only [(hNb q).2, hL]⟩)
  obtain ⟨hR, hhR, bhR, ghR⟩ := graphAt Rh heRh cR (-(L / 5)) (19 * L / 20)
    ⟨by linarith only [hcR.1, hL], by linarith only [hcR.2, hL]⟩ (fun q => (hRbase q).1)
    (fun q => ⟨by linarith only [(hRb q).1, hL], by linarith only [(hRb q).2, hL]⟩)
  obtain ⟨l, hl, hla, _, hcover⟩ := hk C hek a b hshape
  let K0 : Set M := ⋃ i ∈ C.shape.active, slab (C.neck i) (l i) (3 * L / 4)
  change U = (K0 ∪ N.region (-L) (l a)) ∪ B.region (3 * L / 4) L at hcover
  rw [hla] at hcover
  let lo : ℤ → ℝ := fun i => if i = a then -(19 * L / 20) else l i
  let K : Set M := ⋃ i ∈ C.shape.active, slab (C.neck i) (lo i) (3 * L / 4)
  have hlo (i) (hi : i ∈ C.shape.active) : -L < lo i ∧ lo i ≤ -L / 2 := by
    by_cases h : i = a
    · simp only [lo, if_pos h]; constructor <;> linarith only [hL]
    · simpa only [lo, if_neg h] using hl i hi
  have hloa : lo a = -(19 * L / 20) := by simp only [lo, if_pos rfl]
  have hK0K : K0 ⊆ K := by
    intro x hx; obtain ⟨i, hi, z, hz, rfl⟩ := mem_iUnion₂.mp hx
    refine mem_iUnion₂.mpr ⟨i, hi, z, ⟨hz.1, ?_, hz.2.2⟩, rfl⟩
    by_cases h : i = a
    · subst i; rw [hloa]; rw [hla] at hz; linarith only [hz.2.1, hL]
    · simpa only [lo, if_neg h] using hz.2.1
  have hNK : slab N (-(19 * L / 20)) (3 * L / 4) ⊆ K := by
    intro x hx
    exact mem_iUnion₂.mpr ⟨a, ha, by simpa only [hloa] using hx⟩
  have hKsub : K ⊆ U := by
    intro x hx; obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
    exact mem_iUnion₂.mpr ⟨i, hi, slabSub _ (C.epsilon_eq i hi) (hlo i hi).1
      (by linarith only [hL]) hxi⟩
  have hKcompact : IsCompact K := by
    have hfinite : C.shape.active.Finite := by rw [hshape]; exact Set.finite_Icc a b
    exact hfinite.isCompact_biUnion fun i hi =>
      slabCompact _ (C.epsilon_eq i hi) (hlo i hi).1 (by linarith only [hL])

  have hcenter := (Rh.mem_central_sphere_iff Rh.center).mp Rh.center_on_central_sphere
  have hyB : Rh.center ∈ closure (B.region 0 B.epsilon⁻¹) := by
    simpa only [hyRh, heB] using hy
  have hyBout : Rh.center ∉ B.carrier := by rw [hyRh]; exact fun hx => hout (hBU hx)
  have hinter : (Rh.carrier ∩ B.carrier).Nonempty := by
    obtain ⟨x, hxRh, hxB⟩ := mem_closure_iff.mp hyB Rh.carrier Rh.carrier_open hcenter.1
    exact ⟨x, hxRh, hxB.1⟩
  have hratio := (hscale Rh B (small Rh heRh hes) (small B heB hes) hinter).2
  have hscaleBR : B.scale ≤ (1001 / 1000 : ℝ) * Rh.scale := by
    apply (div_le_iff₀ Rh.scale_pos).mp; linarith only [(abs_lt.mp hratio).2]
  have hsqlo : (999 : ℝ) / 1000 ≤ Real.sqrt (1 - H.epsilon) :=
    Real.le_sqrt_of_sq_le (by nlinarith only [hesmall])
  have hsqhi : Real.sqrt (1 + H.epsilon) ≤ (1001 : ℝ) / 1000 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by nlinarith only [hesmall]⟩
  have hcoef : B.scale * Real.sqrt (1 + H.epsilon) ≤
      (101 / 100 : ℝ) * (Rh.scale * Real.sqrt (1 - H.epsilon)) := by
    have hmul := mul_le_mul hscaleBR hsqhi (Real.sqrt_nonneg _)
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1001 / 1000) Rh.scale_pos.le)
    nlinarith only [hmul, mul_le_mul_of_nonneg_left hsqlo Rh.scale_pos.le, Rh.scale_pos]
  have hlast (x : M) (hx : x ∈ B.region (3 * L / 4) L) :
      x ∈ Rh.carrier ∧ |height Rh x| < 27 * L / 100 := by
    let T := L - height B x + B0
    have hT : 0 < T := by dsimp only [T]; linarith only [hB0, hx.2.2]
    have hbT : (101 / 100 : ℝ) * T < 27 * L / 100 := by
      dsimp only [T]; linarith only [hL, hx.2.1, hnumeric.1]
    have hu : g.edist x Rh.center ≤
        ENNReal.ofReal (B.scale * Real.sqrt (1 + H.epsilon) * T) := by
      simpa only [heB, L, T, height, B0] using B.edist_le_positive_frontier hx.1 hyB hyBout
    have hd := Rh.axialDepth_edist_le x Rh.center
    have hdc : Rh.axialDepth Rh.center = L := by
      simp only [EpsilonNeck.axialDepth, if_pos hcenter.1, hcenter.2,
        abs_zero, sub_zero, heRh, L]
    rw [heRh, hdc] at hd
    have hr := (ENNReal.ofReal_le_ofReal_iff
      (mul_nonneg (mul_nonneg B.scale_pos.le (Real.sqrt_nonneg _)) hT.le)).mp (hd.trans hu)
    have hp : 0 < Rh.scale * Real.sqrt (1 - H.epsilon) :=
      mul_pos Rh.scale_pos (by linarith only [hsqlo])
    have hb : |Rh.axialDepth x - L| ≤ (101 / 100 : ℝ) * T := by
      apply (mul_le_mul_iff_left₀ hp).mp
      nlinarith only [hr, mul_le_mul_of_nonneg_right hcoef hT.le]
    have hm : x ∈ Rh.carrier := by
      by_contra h
      simp only [EpsilonNeck.axialDepth, if_neg h, zero_sub, abs_neg, abs_of_pos hL] at hb
      linarith only [hb, hbT, hL]
    refine ⟨hm, ?_⟩
    have hh : Rh.axialDepth x - L = -|height Rh x| := by
      simp only [EpsilonNeck.axialDepth, if_pos hm, heRh]; change L - _ - L = _; ring
    rw [hh, abs_neg, abs_abs] at hb
    exact hb.trans_lt hbT
  have hRhneg : Rh.region (-L) (-L / 2) ⊆ K := by
    intro x hx
    have hh := hJ.2 (Rh.coordinate_inverse x).1 (height Rh x) hx.2.1
      (by linarith only [hL, hx.2.2])
    rw [Rh.coordinate_map_inverse hx.1, hcover] at hh
    rcases hh.1 with (hxK | hxN) | hxB
    · exact hK0K hxK
    · have hb := hh.2; simp only [F, if_pos hxN.1] at hb
      linarith only [hL, hb, hxN.2.2]
    · linarith only [hL, (abs_lt.mp (hlast x hxB).2).1, hx.2.2]
  have retained : ∃ m : ℝ, 19 * L / 20 ≤ m ∧ m < L ∧
      (U ∪ Rh.carrier) ∪ Q.carrier =
        (K ∪ slab Rh (-(24 * L / 25)) m) ∪ slab Q (-(19 * L / 20)) (19 * L / 20) := by
    by_cases hearly : r0 ≤ 2 * L / 5
    · have hNw : N.coordinate_map ((N.coordinate_inverse w).1, u) = w :=
        N.coordinate_map_inverse hwN
      have baseN := sliceAt N Rh heN heRh (N.coordinate_inverse w).1 u
        (coord N heN hwN) (by rwa [hNw])
        (by rw [hNw]; apply abs_le.mpr; constructor <;> linarith only [hr0.1, hearly, hL])
        (by rw [hNw]; exact reciprocal Rh N heRh heN hwRh hwN hreturnSign)
      have bN (q) : -(501 * L / 10000) < height Rh (N.coordinate_map (q, u)) ∧
          height Rh (N.coordinate_map (q, u)) ≤ 4001 * L / 10000 := by
        have hh := (baseN q).2.1; rw [hNw] at hh
        constructor <;> linarith only [(abs_le.mp hh).1, (abs_le.mp hh).2,
          hr0.1, hearly, hnumeric.2]
      have hNneg : N.region (-L) (-L / 2) ⊆ slab Rh (-(24 * L / 25)) (19 * L / 20) := by
        intro x hx; let s := height N x
        have hh := walk N Rh heN heRh (N.coordinate_inverse x).1 u s
          (-(3 * L / 50)) (91 * L / 100) (coord N heN hwN) (coord N heN hx.1)
          (baseN _).1 (baseN _).2.2 (by linarith only [hL]) (by linarith only [hL])
          (by constructor <;> linarith only [(bN (N.coordinate_inverse x).1).1,
            (bN (N.coordinate_inverse x).1).2, hL]) (by
            rcases le_total u s with h | h
            · rw [abs_of_nonneg (sub_nonneg.mpr h)]
              constructor <;> linarith only [(bN (N.coordinate_inverse x).1).1,
                (bN (N.coordinate_inverse x).1).2, hx.2.1, hx.2.2, hu0, hu1, h, hL]
            · rw [abs_of_nonpos (sub_nonpos.mpr h)]
              constructor <;> linarith only [(bN (N.coordinate_inverse x).1).1,
                (bN (N.coordinate_inverse x).1).2, hx.2.1, hx.2.2, hu0, hu1, h, hL])
        rw [N.coordinate_map_inverse hx.1] at hh; exact memSlab Rh hh.1
          ⟨by linarith only [hh.2.1.1, hL], by linarith only [hh.2.1.2, hL]⟩
      have half := walk Rh N heRh heN qr r0 (L / 2) u (-(11 * L / 25))
        (coord Rh heRh hwRh) ⟨by linarith only [hL], by linarith only [hL]⟩
        (by rwa [hRw]) (by rwa [hRw]) hu0 (by linarith only [hL])
        (by rw [hRw]; exact ⟨le_rfl, by linarith only [hu1, hL]⟩) (by
          rw [hRw, abs_of_pos (by linarith only [hearly, hL] : 0 < L / 2 - r0)]
          constructor <;> linarith only [hearly, hr0.1, hu1, hL])
      have hhalf := half.2.2.1
      rw [hRw, abs_of_pos (by linarith only [hearly, hL] : 0 < L / 2 - r0)] at hhalf
      have baseR := sliceAt Rh N heRh heN qr (L / 2)
        ⟨by linarith only [hL], by linarith only [hL]⟩ half.1
        (by apply abs_le.mpr; constructor <;> linarith only [(abs_le.mp hhalf).1,
          (abs_le.mp hhalf).2, hearly, hr0.1, hu0, hu1, hL]) half.2.2.2
      have bR (q) : -(91 * L / 100) < height N (Rh.coordinate_map (q, L / 2)) ∧
          height N (Rh.coordinate_map (q, L / 2)) < -(11 * L / 25) := by
        have hh := abs_le.mp (baseR q).2.1
        constructor <;> linarith only [hh.1, hh.2, (abs_le.mp hhalf).1,
          (abs_le.mp hhalf).2, hearly, hr0.1, hu0, hu1, hnumeric.2, hL]
      have hRpos : Rh.region (L / 2) L ⊆ K := by
        intro x hx; let s := height Rh x
        have hh := walk Rh N heRh heN (Rh.coordinate_inverse x).1 (L / 2) s
          (-(23 * L / 25)) (7 * L / 100)
          ⟨by linarith only [hL], by linarith only [hL]⟩ (coord Rh heRh hx.1)
          (baseR _).1 (baseR _).2.2 (by linarith only [hL]) (by linarith only [hL])
          (by constructor <;> linarith only [(bR (Rh.coordinate_inverse x).1).1,
            (bR (Rh.coordinate_inverse x).1).2, hL]) (by
            rw [abs_of_pos (sub_pos.mpr hx.2.1)]
            constructor <;> linarith only [(bR (Rh.coordinate_inverse x).1).1,
              (bR (Rh.coordinate_inverse x).1).2, hx.2.1, hx.2.2, hL])
        rw [Rh.coordinate_map_inverse hx.1] at hh; exact hNK (memSlab N hh.1
          ⟨by linarith only [hh.2.1.1, hL], by linarith only [hh.2.1.2, hL]⟩)
      have hUR : U ∪ Rh.carrier = K ∪ slab Rh (-(24 * L / 25)) (19 * L / 20) := by
        apply Subset.antisymm
        · rintro x (hxU | hxR)
          · rw [hcover] at hxU
            rcases hxU with (hxK | hxN) | hxB
            · exact Or.inl (hK0K hxK)
            · exact Or.inr (hNneg hxN)
            · have hh := hlast x hxB
              exact Or.inr (memSlab Rh hh.1 ⟨by linarith only [(abs_lt.mp hh.2).1, hL],
                by linarith only [(abs_lt.mp hh.2).2, hL]⟩)
          · by_cases hl : height Rh x < -L / 2
            · exact Or.inl (hRhneg ⟨hxR, (coord Rh heRh hxR).1, hl⟩)
            · by_cases hh : height Rh x ≤ L / 2
              · exact Or.inr (memSlab Rh hxR ⟨by linarith only [hl, hL],
                  by linarith only [hh, hL]⟩)
              · exact Or.inl (hRpos ⟨hxR, lt_of_not_ge hh, (coord Rh heRh hxR).2⟩)
        · exact union_subset_union hKsub (slabSub Rh heRh
            (by linarith only [hL]) (by linarith only [hL]))
      have hclosed : IsClopen (U ∪ Rh.carrier) := ⟨(hUR.symm ▸ (hKcompact.union
        (slabCompact Rh heRh (by linarith only [hL]) (by linarith only [hL])))).isClosed,
        (isOpen_iUnion fun i => isOpen_iUnion fun _ =>
          (C.neck i).carrier_open).union Rh.carrier_open⟩
      have hQsub := Q.isConnected_carrier.isPreconnected.subset_isClopen hclosed
        ⟨z, hzQ, Or.inl (hNU hzN)⟩
      have hS : slab Q (-(19 * L / 20)) (19 * L / 20) ⊆
          K ∪ slab Rh (-(24 * L / 25)) (19 * L / 20) := by
        rw [← hUR]
        exact (slabSub Q heQ (by linarith only [hL]) (by linarith only [hL])).trans hQsub
      exact ⟨19 * L / 20, le_rfl, by linarith only [hL],
        (union_eq_left.mpr hQsub).trans (hUR.trans (union_eq_left.mpr hS).symm)⟩
    · have hlate : 2 * L / 5 < r0 := lt_of_not_ge hearly
      let m := max (19 * L / 20) r0
      have hm : m < L := max_lt (by linarith only [hL]) hr0.2
      have hm95 : 19 * L / 20 ≤ m := le_max_left _ _
      have hmr : r0 ≤ m := le_max_right _ _
      have hNneg : N.region (-L) (-L / 2) ⊆ slab Q (-(19 * L / 20)) (19 * L / 20) := by
        intro x hx
        have hh := calibration (height N x) ⟨hx.2.1, by linarith only [hx.2.2, hL]⟩
          (N.coordinate_inverse x).1
        rw [N.coordinate_map_inverse hx.1] at hh
        have hdelta : |height N x - v| ≤ L / 2 :=
          abs_le.mpr ⟨by linarith only [hx.2.1, hv.2, hL],
            by linarith only [hx.2.2, hv.1]⟩
        exact memSlab Q hh.1 ⟨by
          linarith only [(abs_le.mp hh.2.2).1, hx.2.1, hv.2, hdelta, hnumeric.2, hL], by
          linarith only [(abs_le.mp hh.2.2).2, hx.2.2, hv.1, hdelta, hnumeric.2, hL]⟩
      have baseR := sliceAt Rh Q heRh heQ qr r0 (coord Rh heRh hwRh)
        (by rwa [hRw]) (by rw [hRw]; apply abs_le.mpr; constructor <;>
          linarith only [ht0.1, ht0.2, hL])
        (by rw [hRw]; exact signs.1)
      have bR (q) : -(51 * L / 250) < height Q (Rh.coordinate_map (q, r0)) ∧
          height Q (Rh.coordinate_map (q, r0)) < 3 * L / 1000 := by
        have hh := (baseR q).2.1; rw [hRw] at hh
        constructor <;> linarith only [(abs_le.mp hh).1, (abs_le.mp hh).2,
          ht0.1, ht0.2, hnumeric.2, hL]
      have hRpos (x : M) (hx : x ∈ Rh.carrier) (hxs : r0 < height Rh x) :
          x ∈ slab Q (-(19 * L / 20)) (19 * L / 20) := by
        have hh := walk Rh Q heRh heQ (Rh.coordinate_inverse x).1 r0 (height Rh x)
          (-(21 * L / 100)) (31 * L / 50) (coord Rh heRh hwRh) (coord Rh heRh hx)
          (baseR _).1 (baseR _).2.2 (by linarith only [hL]) (by linarith only [hL])
          (by constructor <;> linarith only [(bR (Rh.coordinate_inverse x).1).1,
            (bR (Rh.coordinate_inverse x).1).2, hL]) (by
            rw [abs_of_pos (sub_pos.mpr hxs)]
            constructor <;> linarith only [(bR (Rh.coordinate_inverse x).1).1,
              (bR (Rh.coordinate_inverse x).1).2, (coord Rh heRh hx).2, hlate, hxs, hL])
        rw [Rh.coordinate_map_inverse hx] at hh; exact memSlab Q hh.1
          ⟨by linarith only [hh.2.1.1, hL], by linarith only [hh.2.1.2, hL]⟩
      have qp := walk Q N heQ heN qw t0 (7 * L / 10) u (11 * L / 50)
        (coord Q heQ hwQ) ⟨by linarith only [hL], by linarith only [hL]⟩
        (by rwa [hQw]) (by rwa [hQw]) hu0 (by linarith only [hL])
        (by rw [hQw]; exact ⟨le_rfl, by linarith only [hu1, hL]⟩) (by
          rw [hQw, abs_of_pos (by linarith only [ht0.2, hL] : 0 < 7 * L / 10 - t0)]
          constructor <;> linarith only [ht0.1, ht0.2, hu1, hL])
      have hqp := qp.2.2.1
      rw [hQw, abs_of_pos (by linarith only [ht0.2, hL] : 0 < 7 * L / 10 - t0)] at hqp
      have baseQ := sliceAt Q N heQ heN qw (7 * L / 10)
        ⟨by linarith only [hL], by linarith only [hL]⟩ qp.1
        (by apply abs_le.mpr; constructor <;> linarith only [(abs_le.mp hqp).1,
          (abs_le.mp hqp).2, hu0, hu1, ht0.1, ht0.2, hL]) qp.2.2.2
      have bQ (q) : -(31 * L / 100) < height N (Q.coordinate_map (q, 7 * L / 10)) ∧
          height N (Q.coordinate_map (q, 7 * L / 10)) < -(43 * L / 500) := by
        have hh := abs_le.mp (baseQ q).2.1
        constructor <;> linarith only [hh.1, hh.2, (abs_le.mp hqp).1,
          (abs_le.mp hqp).2, hu0, hu1, ht0.1, ht0.2, hnumeric.2, hL]
      have hQpos : Q.region (7 * L / 10) L ⊆ K := by
        intro x hx
        have hh := walk Q N heQ heN (Q.coordinate_inverse x).1 (7 * L / 10) (height Q x)
          (-(8 * L / 25)) (11 * L / 50)
          ⟨by linarith only [hL], by linarith only [hL]⟩ (coord Q heQ hx.1)
          (baseQ _).1 (baseQ _).2.2 (by linarith only [hL]) (by linarith only [hL])
          (by constructor <;> linarith only [(bQ (Q.coordinate_inverse x).1).1,
            (bQ (Q.coordinate_inverse x).1).2, hL]) (by
            rw [abs_of_pos (sub_pos.mpr hx.2.1)]
            constructor <;> linarith only [(bQ (Q.coordinate_inverse x).1).1,
              (bQ (Q.coordinate_inverse x).1).2, hx.2.1, hx.2.2, hL])
        rw [Q.coordinate_map_inverse hx.1] at hh; exact hNK (memSlab N hh.1
          ⟨by linarith only [hh.2.1.1, hL], by linarith only [hh.2.1.2, hL]⟩)
      have hQneg : Q.region (-L) (-L / 2) ⊆ slab Rh (-(24 * L / 25)) m := by
        intro x hx
        have hh := walk Q Rh heQ heRh (Q.coordinate_inverse x).1 cR (height Q x)
          (-(63 * L / 100)) (23 * L / 25)
          ⟨by linarith only [hcR.1, hL], by linarith only [hcR.2, hL]⟩ (coord Q heQ hx.1)
          (hRbase _).1 (hRbase _).2.2 (by linarith only [hL]) (by linarith only [hL])
          (by constructor <;> linarith only [(hRsharp (Q.coordinate_inverse x).1).1,
            (hRsharp (Q.coordinate_inverse x).1).2, hlate, hr0.2, hL]) (by
            rw [abs_of_neg (by linarith only [hx.2.2, hcR.1, hL] : height Q x - cR < 0)]
            constructor <;> linarith only [(hRsharp (Q.coordinate_inverse x).1).1,
              (hRsharp (Q.coordinate_inverse x).1).2, hx.2.1, hx.2.2, hcR.1, hcR.2,
              hlate, hr0.2, hL])
        rw [Q.coordinate_map_inverse hx.1] at hh; exact memSlab Rh hh.1
          ⟨by linarith only [hh.2.1.1, hL], by linarith only [hh.2.1.2, hm95, hL]⟩
      refine ⟨m, hm95, hm, Subset.antisymm ?_ ?_⟩
      · rintro x ((hxU | hxR) | hxQ)
        · rw [hcover] at hxU
          rcases hxU with (hxK | hxN) | hxB
          · exact Or.inl (Or.inl (hK0K hxK))
          · exact Or.inr (hNneg hxN)
          · have hh := hlast x hxB
            exact Or.inl (Or.inr (memSlab Rh hh.1 ⟨by linarith only [(abs_lt.mp hh.2).1, hL],
              by linarith only [(abs_lt.mp hh.2).2, hm95, hL]⟩))
        · by_cases hl : height Rh x < -L / 2
          · exact Or.inl (Or.inl (hRhneg ⟨hxR, (coord Rh heRh hxR).1, hl⟩))
          · by_cases hh : height Rh x ≤ r0
            · exact Or.inl (Or.inr (memSlab Rh hxR ⟨by linarith only [hl, hL], hh.trans hmr⟩))
            · exact Or.inr (hRpos x hxR (lt_of_not_ge hh))
        · by_cases hl : height Q x < -L / 2
          · exact Or.inl (Or.inr (hQneg ⟨hxQ, (coord Q heQ hxQ).1, hl⟩))
          · by_cases hh : height Q x ≤ 7 * L / 10
            · exact Or.inr (memSlab Q hxQ ⟨by linarith only [hl, hL],
                by linarith only [hh, hL]⟩)
            · exact Or.inl (Or.inl (hQpos ⟨hxQ, lt_of_not_ge hh, (coord Q heQ hxQ).2⟩))
      · exact union_subset_union (union_subset_union hKsub
          (slabSub Rh heRh (by linarith only [hL]) hm))
          (slabSub Q heQ (by linarith only [hL]) (by linarith only [hL]))
  obtain ⟨m, hm95, hm, hretained⟩ := retained
  obtain ⟨rlo, rhi, hrlo, hrorder, hrhi, hslab⟩ : ∃ rlo rhi : ℝ,
      -L < rlo ∧ rlo ≤ rhi ∧ rhi < L ∧
        slab Rh (-(24 * L / 25)) m = slab R rlo rhi := by
    rcases hRh with h | h
    · exact ⟨-(24 * L / 25), m, by linarith only [hL],
        by linarith only [hm95, hL], hm, by rw [h]⟩
    · refine ⟨-m, 24 * L / 25, by linarith only [hm],
        by linarith only [hm95, hL], by linarith only [hL], ?_⟩
      rw [h]; apply Subset.antisymm <;> rintro x ⟨⟨q, s⟩, hs, rfl⟩
      · exact ⟨(q, -s), ⟨mem_univ _,
          by linarith only [hs.2.2], by linarith only [hs.2.1]⟩, rfl⟩
      · refine ⟨(q, -s), ⟨mem_univ _,
          by linarith only [hs.2.2], by linarith only [hs.2.1]⟩, ?_⟩
        change R.coordinate_map (q, - -s) = _; rw [neg_neg]
  rw [hcRh, hslab] at hretained
  let V := (U ∪ R.carrier) ∪ Q.carrier
  have hVc : IsCompact V := by
    change IsCompact ((U ∪ R.carrier) ∪ Q.carrier)
    rw [hretained]
    exact (hKcompact.union (slabCompact R heR hrlo hrhi)).union
      (slabCompact Q heQ (by linarith only [hL]) (by linarith only [hL]))
  have hVo : IsOpen V :=
    ((isOpen_iUnion fun i => isOpen_iUnion fun _ => (C.neck i).carrier_open).union
      R.carrier_open).union Q.carrier_open
  have hUc : IsConnected U := by
    apply IsConnected.biUnion_of_chain C.active_nonempty
    · rw [hshape]; exact ordConnected_Icc
    · intro i _; exact (C.neck i).isConnected_carrier
    · intro i hi hn; change i + 1 ∈ C.shape.active at hn
      exact C.adjacent_overlap i hi hn
  have hVconn : IsConnected V := IsConnected.union
    ⟨z, Or.inl (hNU hzN), hzQ⟩
    (IsConnected.union ⟨w, hNU hwN, hwR⟩ hUc R.isConnected_carrier) Q.isConnected_carrier
  have hzV : z ∈ V := Or.inl (Or.inl (hNU hzN))
  exact ⟨Q, Rh, w, f, hN, hR, lo, rlo, rhi, hQP, hRh, heQ, heRh,
    ⟨⟨hwN, hwRh⟩, hwQ⟩, hu1, hr0.1, he, hreturnSign, hwcal.2.1,
    hfs, hf, hgSp, hhN, bhN, ghN, hhR, bhR, ghR, bandN, bandR, hlo, hloa,
    hrlo, hrorder, hrhi, hretained, hVc,
    Subset.antisymm (hVconn.subset_connectedComponent hzV)
      ((show IsClopen V from ⟨hVc.isClosed, hVo⟩).connectedComponent_subset hzV),
    H.connected_X.isPreconnected.subset_isClopen ⟨hVc.isClosed, hVo⟩ ⟨z, hz.1, hzV⟩⟩
end PoincareConjecture
