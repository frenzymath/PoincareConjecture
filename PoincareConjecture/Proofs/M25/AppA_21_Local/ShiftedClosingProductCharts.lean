import PoincareConjecture.Proofs.M25.AppA_20_Fibration.CompactCutChart
import PoincareConjecture.Proofs.M25.Mathlib.NormalizedGraphStrip
import Mathlib.Data.Fin.VecNotation

set_option autoImplicit false
open Set
open scoped Manifold ContDiff Topology
universe u
namespace PoincareConjecture.BalancedNeckChain

theorem exists_shifted_closing_product_charts :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T3Space M] {g : RiemannianMetric 3 M} {epsilon : ℝ},
      ∀ (C : BalancedNeckChain g epsilon) {a b : ℤ},
      C.shape = ChainShape.finite a b → epsilon ≤ epsilon0 →
        let L := epsilon⁻¹
        let N := C.neck a
        let B := C.neck b
        let U : Set M := ⋃ i ∈ C.shape.active, (C.neck i).carrier
        ∀ (c : ℝ), c ∈ Set.Ioo (-L / 20) (3 * L / 20) →
        ∀ (Rh Q : EpsilonNeck g), Rh.epsilon = epsilon → Q.epsilon = epsilon →
          ∀ (f hN hR : UnitTwoSphere → ℝ),
            ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f →
            ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ hN →
            ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ hR →
            (∀ q, -(3 * L / 10) < f q ∧ f q < -(L / 5)) →
            (∀ q, -(9 * L / 10) < hN q ∧ hN q < -(4 * L / 5)) →
            (∀ q, -(L / 5) < hR q ∧ hR q < 19 * L / 20) →
            range (fun q : UnitTwoSphere => B.coordinate_map (q, 3 * L / 4)) =
              range (fun q : UnitTwoSphere => Rh.coordinate_map (q, f q)) →
            range (fun q : UnitTwoSphere => N.coordinate_map (q, hN q)) =
              range (fun q : UnitTwoSphere => Q.coordinate_map (q, c)) →
            range (fun q : UnitTwoSphere => Rh.coordinate_map (q, hR q)) =
              range (fun q : UnitTwoSphere => Q.coordinate_map (q, c - L / 4)) →
            let Sm : Set M := range (fun q => N.coordinate_map (q, hN q))
            let Sp : Set M := range (fun q : UnitTwoSphere =>
              B.coordinate_map (q, 3 * L / 4))
            let S2 : Set M := range (fun q : UnitTwoSphere => Q.coordinate_map (q, c - L / 4))
            let Gminus : Set M := N.coordinate_map ''
              {z : RoundCylinderSpace | -L < z.2 ∧ z.2 < hN z.1}
            let Pplus : Set M := connectedComponentIn (U \ Sp)
              (B.coordinate_map ((B.coordinate_inverse B.center).1, 7 * L / 8))
            let K : Set M := U \ (Gminus ∪ Pplus)
            ∃ eta : ℝ, 0 < eta ∧ eta < 1 / 8 ∧
              ∃ e : Fin 3 → OpenPartialHomeomorph RoundCylinderSpace M,
                (∀ i : Fin 3, (e i).source = univ ×ˢ Ioo (-eta) (1 + eta)) ∧
                (∀ i : Fin 3,
                  ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ (e i) (e i).source ∧
                  ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ (e i).symm (e i).target) ∧
                e 0 '' (univ ×ˢ Icc (0 : ℝ) 1) = K ∧
                e 1 '' (univ ×ˢ Icc (0 : ℝ) 1) = Rh.coordinate_map ''
                  {z : RoundCylinderSpace | f z.1 ≤ z.2 ∧ z.2 ≤ hR z.1} ∧
                e 2 '' (univ ×ˢ Icc (0 : ℝ) 1) =
                  Q.coordinate_map '' (univ ×ˢ Icc (c - L / 4) c) ∧
                range (fun q : UnitTwoSphere => e 0 (q, 0)) = Sm ∧
                range (fun q : UnitTwoSphere => e 1 (q, 0)) = Sp ∧
                range (fun q : UnitTwoSphere => e 2 (q, 0)) = S2 ∧
                (∀ i : Fin 3, range (fun q : UnitTwoSphere => e i (q, 1)) =
                  range (fun q : UnitTwoSphere => e (i + 1) (q, 0))) := by
  obtain ⟨epsilon0, h0, hcap, cut⟩ := exists_initial_aligned_compact_cut_chart.{u}
  refine ⟨epsilon0, h0, hcap, ?_⟩
  intro M _ _ _ _ _ _ g epsilon C a b hshape hepsilon
  classical
  let L : ℝ := epsilon⁻¹
  let N := C.neck a
  let B := C.neck b
  let U : Set M := ⋃ i ∈ C.shape.active, (C.neck i).carrier
  dsimp only
  intro c hc Rh Q heRh heQ f hN hR hf hhN hhR bf bN bR gSp gSm gS2
  let Sm : Set M := range (fun q => N.coordinate_map (q, hN q))
  let Sp : Set M := range (fun q : UnitTwoSphere => B.coordinate_map (q, 3 * L / 4))
  let S2 : Set M := range (fun q : UnitTwoSphere => Q.coordinate_map (q, c - L / 4))
  let Gminus : Set M := N.coordinate_map '' {z | -L < z.2 ∧ z.2 < hN z.1}
  let Pplus : Set M := connectedComponentIn (U \ Sp)
    (B.coordinate_map ((B.coordinate_inverse B.center).1, 7 * L / 8))
  let K : Set M := U \ (Gminus ∪ Pplus)
  have hactive (i : ℤ) : i ∈ C.shape.active ↔ i ∈ Icc a b := by rw [hshape]; rfl
  have hab : a ≤ b := by
    obtain ⟨i, hi⟩ := C.active_nonempty
    exact ((hactive i).mp hi).1.trans ((hactive i).mp hi).2
  have ha := (hactive a).mpr ⟨le_rfl, hab⟩
  have hb := (hactive b).mpr ⟨hab, le_rfl⟩
  have heN : N.epsilon = epsilon := C.epsilon_eq a ha
  have heB : B.epsilon = epsilon := C.epsilon_eq b hb
  have hL : 0 < L := inv_pos.mpr (heN ▸ N.epsilon_pos)
  obtain ⟨P, upper, beta, _, hbeta, hbounds, hPs, _, hPsm, hPism,
    hPlow, hPSp, _, hcut⟩ := cut C hshape hepsilon
  obtain ⟨_, _, _, _, hDsource, _, _, hKimage, _⟩ :=
    hcut hN hhN.continuous bN
  have hwidth0 (q : UnitTwoSphere) : hN q < beta q := by
    linarith [(bN q).2, (hbounds q).2.1]
  obtain ⟨delta0, hd0, hd0cap, chart0⟩ :=
    OpenPartialHomeomorph.exists_normalized_graph_strip_chart
      P.symm hN beta hhN hbeta hwidth0 hDsource hPism hPsm
  have hwidth1 (q : UnitTwoSphere) : f q < hR q := by
    linarith [(bf q).2, (bR q).1]
  have hstrip1 : {z : RoundCylinderSpace | f z.1 ≤ z.2 ∧ z.2 ≤ hR z.1} ⊆
      Rh.coordinatePartialHomeomorph.source := by
    intro z hz
    change z ∈ univ ×ˢ Ioo (-Rh.epsilon⁻¹) Rh.epsilon⁻¹
    rw [heRh]
    refine ⟨mem_univ _, ?_, ?_⟩
    · change -L < z.2
      linarith [(bf z.1).1, hz.1]
    · change z.2 < L
      linarith [(bR z.1).2, hz.2]
  obtain ⟨delta1, hd1, _, chart1⟩ :=
    OpenPartialHomeomorph.exists_normalized_graph_strip_chart
      Rh.coordinatePartialHomeomorph f hR hf hhR hwidth1 hstrip1
      Rh.coordinate_map_smooth Rh.coordinate_inverse_smooth
  have hstrip2 : {z : RoundCylinderSpace | c - L / 4 ≤ z.2 ∧ z.2 ≤ c} ⊆
      Q.coordinatePartialHomeomorph.source := by
    intro z hz
    change z ∈ univ ×ˢ Ioo (-Q.epsilon⁻¹) Q.epsilon⁻¹
    rw [heQ]
    refine ⟨mem_univ _, ?_, ?_⟩
    · change -L < z.2
      linarith [hc.1, hz.1, hL]
    · change z.2 < L
      linarith [hc.2, hz.2, hL]
  obtain ⟨delta2, hd2, _, chart2⟩ :=
    OpenPartialHomeomorph.exists_normalized_graph_strip_chart
      Q.coordinatePartialHomeomorph (fun _ => c - L / 4) (fun _ => c)
      contMDiff_const contMDiff_const (fun _ => by linarith) hstrip2
      Q.coordinate_map_smooth Q.coordinate_inverse_smooth
  let eta : ℝ := min delta0 (min delta1 delta2)
  have heta : 0 < eta := lt_min hd0 (lt_min hd1 hd2)
  have heta0 : eta ≤ delta0 := min_le_left _ _
  have heta1 : eta ≤ delta1 := (min_le_right _ _).trans (min_le_left _ _)
  have heta2 : eta ≤ delta2 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨c0, hs0, hc0, hci0, _, him0, hlo0, hhi0⟩ := chart0 eta heta heta0
  obtain ⟨c1, hs1, hc1, hci1, _, him1, hlo1, hhi1⟩ := chart1 eta heta heta1
  obtain ⟨c2, hs2, hc2, hci2, _, him2, hlo2, hhi2⟩ := chart2 eta heta heta2
  have himage0 : c0 '' (univ ×ˢ Icc (0 : ℝ) 1) = K := him0.trans hKimage
  have himage2 : c2 '' (univ ×ˢ Icc (0 : ℝ) 1) =
      Q.coordinate_map '' (univ ×ˢ Icc (c - L / 4) c) := by
    rw [him2]
    congr 1
    ext z
    simp
  have hNdomain (q : UnitTwoSphere) : (q, hN q) ∈ N.cylinderDomain := by
    change (q, hN q) ∈ univ ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹
    rw [heN]
    refine ⟨mem_univ _, ?_, ?_⟩
    · change -L < hN q
      linarith [(bN q).1]
    · change hN q < L
      linarith [(bN q).2]
  have hlower0 : range (fun q : UnitTwoSphere => c0 (q, 0)) = Sm := by
    rw [hlo0]
    congr 1
    funext q
    exact (hPlow (q, hN q) (hNdomain q) (by
      change hN q ≤ -(3 * L / 4)
      linarith [(bN q).2])).2
  have hSpSource : Sp ⊆ P.source := by
    rintro x ⟨q, rfl⟩
    rw [hPs]
    apply mem_iUnion₂.mpr
    refine ⟨b, hb, B.coordinate_map_mem ?_⟩
    change (q, 3 * L / 4) ∈ univ ×ˢ Ioo (-B.epsilon⁻¹) B.epsilon⁻¹
    rw [heB]
    exact ⟨mem_univ _, by change -L < 3 * L / 4; linarith,
      by change 3 * L / 4 < L; linarith⟩
  have hupper0 : range (fun q : UnitTwoSphere => c0 (q, 1)) = Sp := by
    rw [hhi0]
    apply Subset.antisymm
    · rintro x ⟨q, rfl⟩
      have hq : (q, beta q) ∈ P '' Sp := hPSp.symm ▸ mem_range_self q
      obtain ⟨y, hy, heq⟩ := hq
      change P.symm (q, beta q) ∈ Sp
      rw [← heq, P.left_inv (hSpSource hy)]
      exact hy
    · intro x hx
      have hq : P x ∈ range (fun q : UnitTwoSphere => (q, beta q)) :=
        hPSp ▸ mem_image_of_mem P hx
      obtain ⟨q, hq⟩ := hq
      refine ⟨q, ?_⟩
      change P.symm (q, beta q) = x
      change (q, beta q) = P x at hq
      rw [hq, P.left_inv (hSpSource hx)]
  have hlower1 : range (fun q : UnitTwoSphere => c1 (q, 0)) = Sp := hlo1.trans gSp.symm
  have hupper1 : range (fun q : UnitTwoSphere => c1 (q, 1)) = S2 := hhi1.trans gS2
  have hlower2 : range (fun q : UnitTwoSphere => c2 (q, 0)) = S2 := hlo2
  have hupper2 : range (fun q : UnitTwoSphere => c2 (q, 1)) = Sm := hhi2.trans gSm.symm
  let e : Fin 3 → OpenPartialHomeomorph RoundCylinderSpace M := ![c0, c1, c2]
  refine ⟨eta, heta, heta0.trans_lt hd0cap, e, ?_, ?_,
    himage0, him1, himage2, hlower0, hlower1, hlower2, ?_⟩
  · intro i
    fin_cases i
    · exact hs0
    · exact hs1
    · exact hs2
  · intro i
    fin_cases i
    · exact ⟨hc0, hci0⟩
    · exact ⟨hc1, hci1⟩
    · exact ⟨hc2, hci2⟩
  · intro i
    fin_cases i
    · exact hupper0.trans hlower1.symm
    · exact hupper1.trans hlower2.symm
    · exact hupper2.trans hlower0.symm

end PoincareConjecture.BalancedNeckChain
