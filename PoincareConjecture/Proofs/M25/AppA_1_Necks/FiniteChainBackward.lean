import PoincareConjecture.Proofs.M25.AppA_1_Necks.FiniteChainClosedQuarters

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.BalancedNeckChain

theorem exists_finite_backward_extension_closed_quarters :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T3Space M] {g : RiemannianMetric 3 M} {epsilon : ℝ},
      ∀ (C : BalancedNeckChain g epsilon) {a b : ℤ},
      C.shape = ChainShape.finite a b →
      epsilon ≤ epsilon0 →
      (∀ i ∈ C.shape.active, (C.neck i).IsSeparating) →
      (∀ i ∈ C.shape.active, i + 1 ∈ C.shape.active →
        closure ((C.neck i).region (epsilon⁻¹ / 2) epsilon⁻¹) ⊆
            (C.neck (i + 1)).carrier ∧
          closure ((C.neck (i + 1)).region (-epsilon⁻¹) (-epsilon⁻¹ / 2)) ⊆
            (C.neck i).carrier) →
      ∀ (N' : EpsilonNeck g),
      N' ∈ C.source_necks →
      N'.epsilon = epsilon →
      N'.center ∈ closure ((C.neck a).region (-epsilon⁻¹) 0) →
      N'.center ∉ (⋃ i ∈ C.shape.active, (C.neck i).carrier) →
      ∃ (R : EpsilonNeck g) (D : BalancedNeckChain g epsilon),
        (R = N' ∨ R = N'.reverse) ∧
        R.SameUpToReversal N' ∧
        D.shape = ChainShape.finite (a - 1) b ∧
        D.source_necks = C.source_necks ∧
        D.neck = Function.update C.neck (a - 1) R ∧
        (∀ i ∈ D.shape.active, i + 1 ∈ D.shape.active →
          closure ((D.neck i).region (epsilon⁻¹ / 2) epsilon⁻¹) ⊆
              (D.neck (i + 1)).carrier ∧
            closure ((D.neck (i + 1)).region (-epsilon⁻¹) (-epsilon⁻¹ / 2)) ⊆
              (D.neck i).carrier) := by
  classical
  obtain ⟨epsilonP, hP, hPcap, hpair⟩ := EpsilonNeck.exists_ordered_frontier_neighbor.{u}
  obtain ⟨epsilonC, hC, _, hclosedPositive⟩ :=
    EpsilonNeck.exists_positive_frontier_closed_quarter_control.{u}
  obtain ⟨epsilonD, hD, _, hclosedNegative⟩ :=
    EpsilonNeck.exists_positive_frontier_closed_negative_quarter_control.{u}
  obtain ⟨epsilonS, hS, _, hscale⟩ :=
    EpsilonNeck.exists_intersecting_scale_control.{u} (α := 1 / 1000) (by norm_num)
  let B := Real.sqrt 2 * (Real.pi + 1)
  have hB : 0 < B := by dsimp only [B]; positivity
  have hden : 0 < 1000 * (B + 1) := by positivity
  refine ⟨min epsilonP (min epsilonC (min epsilonD (min epsilonS (1 / (1000 * (B + 1)))))),
    lt_min hP (lt_min hC (lt_min hD (lt_min hS (div_pos zero_lt_one hden)))),
    (min_le_left _ _).trans hPcap, ?_⟩
  intro M _ _ _ _ _ _ g epsilon C a b hshape he hsep hquarters
    N' hsource hepsilon hy hyout
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hcomm (x y : M) : g.edist x y = g.edist y x :=
    Manifold.riemannianEDist_comm
  have hactive (i : ℤ) : i ∈ C.shape.active ↔ i ∈ Icc a b := by
    rw [hshape]
    rfl
  obtain ⟨i0, hi0⟩ := C.active_nonempty
  have hab : a ≤ b := ((hactive i0).mp hi0).1.trans ((hactive i0).mp hi0).2
  have ha : a ∈ C.shape.active := (hactive a).mpr ⟨le_rfl, hab⟩
  let N := C.neck a
  have hNe : N.epsilon = epsilon := C.epsilon_eq a ha
  have hNsep : N.IsSeparating := hsep a ha
  have hepos : 0 < epsilon := hNe ▸ N.epsilon_pos
  let L := epsilon⁻¹
  have hL : 0 < L := inv_pos.mpr hepos
  have hr : 0 < N.scale := N.scale_pos
  have heP : epsilon ≤ epsilonP := he.trans (min_le_left _ _)
  have heC : epsilon ≤ epsilonC :=
    he.trans ((min_le_right _ _).trans (min_le_left _ _))
  have heD : epsilon ≤ epsilonD :=
    he.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have heS : epsilon ≤ epsilonS := he.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hsmall : epsilon ≤ 1 / (1000 * (B + 1)) := he.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  have hbudget := (le_div_iff₀ hden).mp hsmall
  have he1000 : epsilon ≤ 1 / 1000 := by nlinarith [mul_pos hepos hB]
  have hBL : B ≤ L / 1000 := by
    have hBe : B * epsilon ≤ 1 / 1000 := by nlinarith [hepos]
    calc
      B ≤ (1 / 1000) / epsilon := (le_div_iff₀ hepos).mpr hBe
      _ = L / 1000 := by dsimp only [L]; ring
  have hsqrtLower : (999 : ℝ) / 1000 ≤ Real.sqrt (1 - epsilon) :=
    Real.le_sqrt_of_sq_le (by nlinarith)
  have hsqrtUpper : Real.sqrt (1 + epsilon) ≤ (1001 : ℝ) / 1000 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by nlinarith⟩
  have hyoutN : N'.center ∉ N.carrier := by
    intro hx
    exact hyout (mem_iUnion₂.mpr ⟨a, ha, hx⟩)
  have hyrev : N'.center ∈ closure (N.reverse.region 0 N.reverse.epsilon⁻¹) := by
    change N'.center ∈ closure (N.reverse.region 0 N.epsilon⁻¹)
    simpa only [EpsilonNeck.reverse_region, neg_zero, hNe] using hy
  obtain ⟨T, hTchoice, hTselected, _, hTinter, hTquarter, hToverlap, _, _⟩ :=
    hpair N.reverse N' (by change N.epsilon ≤ epsilonP; rw [hNe]; exact heP)
      (hepsilon.trans hNe.symm) hNsep hyrev hyoutN
  obtain ⟨R, hchoice, hTregion⟩ : ∃ R : EpsilonNeck g,
      (R = N' ∨ R = N'.reverse) ∧
        ∀ p q : ℝ, T.region p q = R.region (-q) (-p) := by
    rcases hTchoice with h | h
    · refine ⟨N'.reverse, Or.inr rfl, ?_⟩
      intro p q
      rw [h, EpsilonNeck.reverse_region]
      simp only [neg_neg]
    · refine ⟨N', Or.inl rfl, ?_⟩
      intro p q
      rw [h]
      exact N'.reverse_region p q
  have hRc : R.center = N'.center := by rcases hchoice with rfl | rfl <;> rfl
  have hRr : R.scale = N'.scale := by rcases hchoice with rfl | rfl <;> rfl
  have hRu : R.carrier = N'.carrier := by rcases hchoice with rfl | rfl <;> rfl
  have hRe : R.epsilon = epsilon := by rcases hchoice with rfl | rfl <;> exact hepsilon
  have hTRu : T.carrier = R.carrier := hTselected.2.2.2.1.trans hRu.symm
  have hTc : T.center = N'.center := hTselected.2.2.1
  have hTe : T.epsilon = N.reverse.epsilon :=
    hTselected.1.trans (hepsilon.trans hNe.symm)
  have hselected : R.SameUpToReversal N' := by
    rcases hchoice with rfl | rfl
    · refine ⟨rfl, rfl, rfl, rfl, rfl, 1, Or.inl rfl, ?_⟩
      intro z _
      simp only [one_mul]
    · refine ⟨rfl, rfl, rfl, rfl, rfl, -1, Or.inr rfl, ?_⟩
      intro z _
      change N'.coordinate_map (z.1, -z.2) = N'.coordinate_map (z.1, -1 * z.2)
      simp
  have hquarter : R.region (epsilon⁻¹ / 2) epsilon⁻¹ ⊆ N.carrier ∧
      N.region (-epsilon⁻¹) (-epsilon⁻¹ / 2) ⊆ R.carrier := by
    constructor
    · have h := hTquarter.2
      change T.region (-N.epsilon⁻¹) (-N.epsilon⁻¹ / 2) ⊆ N.carrier at h
      rw [hTregion] at h
      simpa only [hNe, neg_div, neg_neg] using h
    · have h := hTquarter.1
      change N.reverse.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹ ⊆ T.carrier at h
      simpa only [EpsilonNeck.reverse_region, hNe, hTRu, neg_div] using h
  have hoverlap : R.carrier ∩ N.carrier ⊆
      R.region (-epsilon⁻¹ / 2) epsilon⁻¹ ∩
        N.region (-epsilon⁻¹) (epsilon⁻¹ / 2) := by
    intro x hx
    have h := hToverlap ⟨hx.2, hTRu.symm ▸ hx.1⟩
    constructor
    · have hh := h.2
      change x ∈ T.region (-N.epsilon⁻¹) (N.epsilon⁻¹ / 2) at hh
      rw [hTregion] at hh
      simpa only [hNe, neg_div, neg_neg] using hh
    · have hh := h.1
      change x ∈ N.reverse.region (-N.epsilon⁻¹ / 2) N.epsilon⁻¹ at hh
      simpa only [EpsilonNeck.reverse_region, hNe, neg_div, neg_neg] using hh
  have hinter : (R.carrier ∩ N.carrier).Nonempty := by
    obtain ⟨x, hxN, hxT⟩ := hTinter
    exact ⟨x, hTRu ▸ hxT, hxN⟩
  have hyT : T.center ∈ closure (N.reverse.region 0 N.reverse.epsilon⁻¹) := by
    rw [hTc]
    exact hyrev
  have hyTout : T.center ∉ N.reverse.carrier := by rw [hTc]; exact hyoutN
  have hclosedTpos := hclosedPositive N.reverse T
    (by change N.epsilon ≤ epsilonC; rw [hNe]; exact heC) hTe hyT hyTout
  have hclosedTneg := hclosedNegative N.reverse T
    (by change N.epsilon ≤ epsilonD; rw [hNe]; exact heD) hTe hNsep hyT hyTout
    hTquarter.2
  have hclosed : closure (R.region (epsilon⁻¹ / 2) epsilon⁻¹) ⊆ N.carrier ∧
      closure (N.region (-epsilon⁻¹) (-epsilon⁻¹ / 2)) ⊆ R.carrier := by
    constructor
    · change closure (T.region (-N.epsilon⁻¹) (-N.epsilon⁻¹ / 2)) ⊆ N.carrier
        at hclosedTneg
      rw [hTregion] at hclosedTneg
      simpa only [hNe, neg_div, neg_neg] using hclosedTneg
    · change closure (N.reverse.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹) ⊆ T.carrier
        at hclosedTpos
      simpa only [EpsilonNeck.reverse_region, hNe, hTRu, neg_div] using hclosedTpos
  have hinterNR : (N.carrier ∩ R.carrier).Nonempty := by
    obtain ⟨x, hxR, hxN⟩ := hinter
    exact ⟨x, hxN, hxR⟩
  have hratio := (hscale N R (by rw [hNe]; exact heS)
    (by rw [hRe]; exact heS) hinterNR).2
  have hratioReverse := (hscale R N (by rw [hRe]; exact heS)
    (by rw [hNe]; exact heS) hinter).2
  have hRupper : R.scale ≤ (1001 : ℝ) / 1000 * N.scale :=
    ((div_lt_iff₀ N.scale_pos).mp
      (show R.scale / N.scale < (1001 : ℝ) / 1000 by
        linarith [(abs_lt.mp hratio).2])).le
  have hNlower : (999 : ℝ) / 1000 * R.scale ≤ N.scale :=
    ((lt_div_iff₀ R.scale_pos).mp
      (show (999 : ℝ) / 1000 < N.scale / R.scale by
        linarith [(abs_lt.mp hratioReverse).1])).le
  have hNupper : N.scale ≤ (1001 : ℝ) / 1000 * R.scale :=
    ((div_lt_iff₀ R.scale_pos).mp
      (show N.scale / R.scale < (1001 : ℝ) / 1000 by
        linarith [(abs_lt.mp hratioReverse).2])).le
  have hRpositive : 0 < R.scale := R.scale_pos
  have hbalance :
      ENNReal.ofReal ((0.99 : ℝ) * R.scale * epsilon⁻¹) ≤ g.edist R.center N.center ∧
        g.edist R.center N.center ≤ ENNReal.ofReal ((1.01 : ℝ) * R.scale * epsilon⁻¹) := by
    rw [hcomm R.center N.center, hRc]
    have hc := N.edist_center_closure_bounds
      (closure_mono (fun _ hx => hx.1) hy) hyoutN
    rw [hNe] at hc
    constructor
    · apply (ENNReal.ofReal_le_ofReal ?_).trans hc.1
      change (0.99 : ℝ) * R.scale * L ≤ N.scale * Real.sqrt (1 - epsilon) * L
      calc
        _ ≤ ((999 / 1000) * R.scale) * (999 / 1000) * L := by
          nlinarith [mul_pos R.scale_pos hL]
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (mul_le_mul hNlower hsqrtLower (by norm_num) N.scale_pos.le) hL.le
    · apply hc.2.trans (ENNReal.ofReal_le_ofReal ?_)
      change N.scale * Real.sqrt (1 + epsilon) * (L + B) ≤ (1.01 : ℝ) * R.scale * L
      calc
        _ ≤ ((1001 / 1000) * R.scale) * (1001 / 1000) * (L + B) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul hNupper hsqrtUpper (Real.sqrt_nonneg _) (by positivity))
            (by positivity)
        _ ≤ ((1001 / 1000) * R.scale) * (1001 / 1000) * (L + L / 1000) :=
          mul_le_mul_of_nonneg_left (add_le_add le_rfl hBL) (by positivity)
        _ ≤ _ := by nlinarith [mul_pos R.scale_pos hL]
  obtain ⟨a0, b0, ha0, hb0, _, _, _, _, _, hcover⟩ :=
    N.exists_opposite_central_components hNsep
  obtain ⟨H, hH, hinside, hminus, hplus, _, hdist⟩ :=
    N.exists_saturatedAxialHeight hNsep a0 b0 ha0 hb0
  have hout {x : M} (hxK : x ∈ connectedComponent N.center) (hx : x ∉ N.carrier) :
      H x = -L ∨ H x = L := by
    rw [← hcover] at hxK
    rcases hxK with (hxA | hxS) | hxB
    · exact Or.inl (by simpa only [hNe] using hminus x ⟨hxA, hx⟩)
    · exact False.elim (hx (N.central_sphere_subset hxS))
    · exact Or.inr (by simpa only [hNe] using hplus x ⟨hxB, hx⟩)
  have hyK : N'.center ∈ connectedComponent N.center :=
    closure_minimal (fun _ hx => N.m25_carrier_subset_connectedComponent hx.1)
      isClosed_connectedComponent hy
  have hyH : H N'.center = -L := by
    have hnonpositive : N.region (-epsilon⁻¹) 0 ⊆ {x | H x ≤ 0} := by
      intro x hx
      change H x ≤ 0
      rw [hinside x hx.1]
      exact hx.2.2.le
    have hyneg : H N'.center ≤ 0 :=
      closure_minimal hnonpositive (isClosed_le hH continuous_const) hy
    rcases hout hyK hyoutN with h | h
    · exact h
    · linarith
  have hRcenter : H R.center = -L := by rw [hRc]; exact hyH
  have hRK : R.carrier ⊆ connectedComponent N.center := by
    intro x hx
    have hm := R.m25_carrier_subset_connectedComponent hx
    rw [hRc, ← connectedComponent_eq hyK] at hm
    exact hm
  have hupper {x : M} (hx : x ∈ R.carrier) :
      g.edist x R.center ≤
        ENNReal.ofReal ((1003003001 : ℝ) / 1000000000 * N.scale * L) := by
    have hc := (R.mem_central_sphere_iff R.center).mp R.center_on_central_sphere
    have hu := R.edist_le_axial_add hx hc.1
    rw [hc.2, zero_sub, abs_neg, hRe] at hu
    have hheight : |(R.coordinate_inverse x).2| ≤ L := by
      simpa only [hRe] using (abs_lt.mpr (R.coordinate_inverse_mem x hx).2).le
    apply hu.trans (ENNReal.ofReal_le_ofReal ?_)
    change R.scale * Real.sqrt (1 + epsilon) * (|(R.coordinate_inverse x).2| + B) ≤ _
    calc
      _ ≤ ((1001 / 1000) * N.scale) * (1001 / 1000) *
          (|(R.coordinate_inverse x).2| + B) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul hRupper hsqrtUpper (Real.sqrt_nonneg _) (by positivity))
          (by positivity)
      _ ≤ ((1001 / 1000) * N.scale) * (1001 / 1000) * (L + L / 1000) :=
        mul_le_mul_of_nonneg_left (add_le_add hheight hBL) (by positivity)
      _ = _ := by ring
  have hQheight {x : M} (hx : x ∈ R.region (-epsilon⁻¹) (-epsilon⁻¹ / 2)) :
      H x = -L := by
    have hxout : x ∉ N.carrier := by
      intro hxN
      have hh := (hoverlap ⟨hx.1, hxN⟩).1.2.1
      exact (not_lt_of_ge hh.le) hx.2.2
    rcases hout (hRK hx.1) hxout with h | h
    · exact h
    · have hd := hdist x R.center
      rw [h, hRcenter, hNe] at hd
      have hlow : ENNReal.ofReal ((1998 : ℝ) / 1000 * N.scale * L) ≤
          g.edist x R.center := by
        apply (ENNReal.ofReal_le_ofReal ?_).trans hd
        rw [show L - -L = 2 * L by ring, abs_of_pos (by positivity : 0 < 2 * L)]
        calc
          _ = N.scale * (999 / 1000) * (2 * L) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hsqrtLower N.scale_pos.le) (by positivity)
      have hstrict : ENNReal.ofReal ((1003003001 : ℝ) / 1000000000 * N.scale * L) <
          ENNReal.ofReal ((1998 : ℝ) / 1000 * N.scale * L) := by
        apply (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
        nlinarith [mul_pos N.scale_pos hL]
      exact False.elim ((not_le_of_gt hstrict) (hlow.trans (hupper hx.1)))
  have hOldHeight : ∀ x ∈ (⋃ i ∈ C.shape.active, (C.neck i).carrier), -L < H x := by
    have hNheight {x : M} (hx : x ∈ N.carrier) : -L < H x := by
      rw [hinside x hx]
      simpa only [hNe] using (N.coordinate_inverse_mem x hx).2.1
    by_cases hablt : a < b
    · have hJactive {j : ℤ} (hj : j ∈ Ioc a b) : j ∈ C.shape.active :=
        (hactive j).mpr ⟨hj.1.le, hj.2⟩
      have hcuts : ∀ j : ℤ, ∃ s : ℝ, j ∈ Ioc a b →
          s ∈ Ioo (-L) 0 ∧ Disjoint (C.neck j).carrier (N.region (-L) s) := by
        intro j
        by_cases hj : j ∈ Ioc a b
        · obtain ⟨s, hs, hd⟩ := C.later_disjoint_negative_end a ha j (hJactive hj) hj.1
          exact ⟨s, fun _ => ⟨hs, hd⟩⟩
        · exact ⟨0, fun hj' => False.elim (hj hj')⟩
      choose s hs using hcuts
      let J := Finset.Ioc a b
      have hbJ : b ∈ J := Finset.mem_Ioc.mpr ⟨hablt, le_rfl⟩
      let Q := J.image s
      have hQ : Q.Nonempty := ⟨s b, Finset.mem_image.mpr ⟨b, hbJ, rfl⟩⟩
      let m := Q.min' hQ
      have hm : m ∈ Ioo (-L) 0 := by
        obtain ⟨j, hj, hjm⟩ := Finset.mem_image.mp (Q.min'_mem hQ)
        dsimp only [m]
        rw [← hjm]
        exact (hs j (Finset.mem_Ioc.mp hj)).1
      have hmin {j : ℤ} (hj : j ∈ Ioc a b) : m ≤ s j :=
        Q.min'_le (s j) (Finset.mem_image.mpr ⟨j, Finset.mem_Ioc.mpr hj, rfl⟩)
      let t := (-L + m) / 2
      have htlo : -L < t := by dsimp only [t]; linarith [hm.1]
      have htm : t < m := by dsimp only [t]; linarith [hm.1]
      have htneg : t < 0 := htm.trans hm.2
      have ht : t ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
        rw [hNe]
        exact ⟨htlo, htneg.trans hL⟩
      let U := ⋃ j ∈ Ioc a b, (C.neck j).carrier
      have hU : IsConnected U := by
        apply IsConnected.biUnion_of_chain (t := Ioc a b)
          ⟨b, hablt, le_rfl⟩ ordConnected_Ioc
        · intro j _
          exact (C.neck j).isConnected_carrier
        · intro j hj hjnext
          have hj1 : j + 1 ∈ Ioc a b := by
            simpa only [Order.succ_eq_add_one] using hjnext
          simpa only [Order.succ_eq_add_one] using
            C.adjacent_overlap j (hJactive hj) (hJactive hj1)
      have havoid {x : M} (hx : x ∈ U) :
          x ∉ range (fun q : UnitTwoSphere => N.coordinate_map (q, t)) := by
        obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp hx
        rintro ⟨q, hq⟩
        have hxreg : x ∈ N.region (-L) (s j) := by
          rw [← hq]
          refine ⟨N.coordinate_map_mem ⟨mem_univ _, ht⟩, ?_⟩
          rw [N.coordinate_inverse_map (q, t) ht]
          exact ⟨htlo, htm.trans_le (hmin hj)⟩
        exact Set.disjoint_left.mp (hs j hj).2 hxj hxreg
      let q0 := (N.coordinate_inverse N.center).1
      let w := N.coordinate_map (q0, 3 * L / 4)
      have hthree : 3 * L / 4 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
        rw [hNe]
        change -L < 3 * L / 4 ∧ 3 * L / 4 < L
        constructor <;> linarith
      have hwN : w ∈ N.carrier := N.coordinate_map_mem ⟨mem_univ _, hthree⟩
      have hwheight : H w = 3 * L / 4 := by
        rw [hinside w hwN, N.coordinate_inverse_map (q0, 3 * L / 4) hthree]
      have ha1 : a + 1 ∈ Ioc a b := ⟨by omega, by omega⟩
      have hwU : w ∈ U := by
        apply mem_iUnion₂.mpr
        refine ⟨a + 1, ha1, (C.overlap_contains_quarters a ha (hJactive ha1)).1 ?_⟩
        refine ⟨hwN, ?_⟩
        rw [N.coordinate_inverse_map (q0, 3 * L / 4) hthree]
        change L / 2 < 3 * L / 4 ∧ 3 * L / 4 < L
        constructor <;> linarith
      have hUK : U ⊆ connectedComponent N.center := by
        have hwK := N.m25_carrier_subset_connectedComponent hwN
        have hsub := hU.subset_connectedComponent hwU
        rw [← connectedComponent_eq hwK] at hsub
        exact hsub
      have hnotlevel : ∀ x ∈ U, H x ≠ t := by
        intro x hx hxt
        by_cases hxN : x ∈ N.carrier
        · apply havoid hx
          refine ⟨(N.coordinate_inverse x).1, ?_⟩
          rw [hinside x hxN] at hxt
          rw [← hxt]
          exact N.coordinate_map_inverse hxN
        · rcases hout (hUK hx) hxN with h | h <;> linarith
      have hpositive : ∀ x ∈ U, t < H x := fun x hx =>
        hU.isPreconnected.lt_of_ne hH.continuousOn hnotlevel
          ⟨w, hwU, by rw [hwheight]; linarith⟩ hx
      intro x hx
      obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp hx
      by_cases hja : j = a
      · subst j
        exact hNheight hxj
      · obtain ⟨hjaLower, hjb⟩ := (hactive j).mp hj
        have hjU : j ∈ Ioc a b := ⟨by omega, hjb⟩
        exact htlo.trans (hpositive x (mem_iUnion₂.mpr ⟨j, hjU, hxj⟩))
    · intro x hx
      obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp hx
      obtain ⟨hjaLower, hjb⟩ := (hactive j).mp hj
      have hja : j = a := by omega
      subst j
      exact hNheight hxj
  have hexclusion {j : ℤ} (hj : j ∈ C.shape.active) :
      Disjoint (C.neck j).carrier (R.region (-epsilon⁻¹) (-epsilon⁻¹ / 2)) := by
    apply Set.disjoint_left.mpr
    intro x hxj hxR
    have hh := hOldHeight x (mem_iUnion₂.mpr ⟨j, hj, hxj⟩)
    rw [hQheight hxR] at hh
    exact (lt_irrefl _) hh
  have hcenters {j : ℤ} (hj : j ∈ C.shape.active) : (C.neck j).center ≠ R.center := by
    intro h
    apply hyout
    apply mem_iUnion₂.mpr
    refine ⟨j, hj, ?_⟩
    rw [← hRc, ← h]
    exact (C.neck j).central_sphere_subset (C.neck j).center_on_central_sphere
  let V := Function.update C.neck (a - 1) R
  have hVnew : V (a - 1) = R := Function.update_self _ _ _
  have hVold {i : ℤ} (hi : i ∈ C.shape.active) : V i = C.neck i := by
    have hile : a ≤ i := ((hactive i).mp hi).1
    have hine : i ≠ a - 1 := by omega
    exact Function.update_of_ne hine R C.neck
  have hold {i : ℤ} (hi : i ∈ Icc (a - 1) b) (hne : i ≠ a - 1) :
      i ∈ C.shape.active := by
    apply (hactive i).mpr
    rcases hi with ⟨hia, hib⟩
    exact ⟨by omega, hib⟩
  have holdPair {i : ℤ} (hi : i ∈ Icc (a - 1) b) (hi1 : i + 1 ∈ Icc (a - 1) b)
      (hne : i ≠ a - 1) : i ∈ C.shape.active ∧ i + 1 ∈ C.shape.active := by
    rcases hi with ⟨hia, hib⟩
    rcases hi1 with ⟨hi1a, hi1b⟩
    exact ⟨(hactive i).mpr ⟨by omega, hib⟩,
      (hactive (i + 1)).mpr ⟨by omega, hi1b⟩⟩
  have hnewNext : a - 1 + 1 = a := by omega
  let D : BalancedNeckChain g epsilon := {
    shape := .finite (a - 1) b
    neck := V
    source_necks := C.source_necks
    selected := by
      intro i hi
      change i ∈ Icc (a - 1) b at hi
      by_cases hin : i = a - 1
      · subst i
        exact ⟨N', hsource, hVnew ▸ hselected⟩
      · have hio := hold hi hin
        simpa only [hVold hio] using C.selected i hio
    active_nonempty := ⟨a, by omega, hab⟩
    epsilon_eq := by
      intro i hi
      change i ∈ Icc (a - 1) b at hi
      by_cases hin : i = a - 1
      · subst i
        rw [hVnew]
        exact hRe
      · rw [hVold (hold hi hin)]
        exact C.epsilon_eq i (hold hi hin)
    centers_distinct := by
      intro i hi j hj hij
      change i ∈ Icc (a - 1) b at hi
      change j ∈ Icc (a - 1) b at hj
      by_cases hin : i = a - 1
      · subst i
        have hjo := hold hj (Ne.symm hij)
        rw [hVnew, hVold hjo]
        exact (hcenters hjo).symm
      · have hio := hold hi hin
        by_cases hjn : j = a - 1
        · subst j
          rw [hVold hio, hVnew]
          exact hcenters hio
        · have hjo := hold hj hjn
          rw [hVold hio, hVold hjo]
          exact C.centers_distinct hio hjo hij
    adjacent_overlap := by
      intro i hi hi1
      change i ∈ Icc (a - 1) b at hi
      change i + 1 ∈ Icc (a - 1) b at hi1
      by_cases hin : i = a - 1
      · subst i
        rw [hnewNext, hVnew, hVold ha]
        exact hinter
      · obtain ⟨hio, hi1o⟩ := holdPair hi hi1 hin
        rw [hVold hio, hVold hi1o]
        exact C.adjacent_overlap i hio hi1o
    overlap_contains_quarters := by
      intro i hi hi1
      change i ∈ Icc (a - 1) b at hi
      change i + 1 ∈ Icc (a - 1) b at hi1
      by_cases hin : i = a - 1
      · subst i
        rw [hnewNext, hVnew, hVold ha]
        exact hquarter
      · obtain ⟨hio, hi1o⟩ := holdPair hi hi1 hin
        rw [hVold hio, hVold hi1o]
        exact C.overlap_contains_quarters i hio hi1o
    overlap_within_three_quarters := by
      intro i hi hi1
      change i ∈ Icc (a - 1) b at hi
      change i + 1 ∈ Icc (a - 1) b at hi1
      by_cases hin : i = a - 1
      · subst i
        rw [hnewNext, hVnew, hVold ha]
        exact hoverlap
      · obtain ⟨hio, hi1o⟩ := holdPair hi hi1 hin
        rw [hVold hio, hVold hi1o]
        exact C.overlap_within_three_quarters i hio hi1o
    later_disjoint_negative_end := by
      intro i hi j hj hij
      change i ∈ Icc (a - 1) b at hi
      change j ∈ Icc (a - 1) b at hj
      have hjo : j ∈ C.shape.active := by
        apply (hactive j).mpr
        rcases hi with ⟨hia, hib⟩
        rcases hj with ⟨hja, hjb⟩
        exact ⟨by omega, hjb⟩
      by_cases hin : i = a - 1
      · subst i
        refine ⟨-epsilon⁻¹ / 2, ⟨by change -L < -L / 2; linarith,
          by change -L / 2 < 0; linarith⟩, ?_⟩
        rw [hVold hjo, hVnew]
        exact hexclusion hjo
      · have hio := hold hi hin
        simpa only [hVold hio, hVold hjo] using
          C.later_disjoint_negative_end i hio j hjo hij
    balanced_center_distance := by
      intro i hi hi1
      change i ∈ Icc (a - 1) b at hi
      change i + 1 ∈ Icc (a - 1) b at hi1
      by_cases hin : i = a - 1
      · subst i
        rw [hnewNext, hVnew, hVold ha]
        exact hbalance
      · obtain ⟨hio, hi1o⟩ := holdPair hi hi1 hin
        rw [hVold hio, hVold hi1o]
        exact C.balanced_center_distance i hio hi1o }
  refine ⟨R, D, hchoice, hselected, rfl, rfl, rfl, ?_⟩
  intro i hi hi1
  change i ∈ Icc (a - 1) b at hi
  change i + 1 ∈ Icc (a - 1) b at hi1
  change closure ((V i).region (epsilon⁻¹ / 2) epsilon⁻¹) ⊆ (V (i + 1)).carrier ∧
    closure ((V (i + 1)).region (-epsilon⁻¹) (-epsilon⁻¹ / 2)) ⊆ (V i).carrier
  by_cases hin : i = a - 1
  · subst i
    rw [hnewNext, hVnew, hVold ha]
    exact hclosed
  · obtain ⟨hio, hi1o⟩ := holdPair hi hi1 hin
    rw [hVold hio, hVold hi1o]
    exact hquarters i hio hi1o

end PoincareConjecture.BalancedNeckChain
