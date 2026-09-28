import PoincareConjecture.Proofs.M25.AppA_1_Necks.SaturatedHeight
import PoincareConjecture.Proofs.M25.AppA_1_Necks.OverlapSlab
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.Finset.Max
import Mathlib.Topology.Connected.Basic












set_option autoImplicit false

open Set
open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareConjecture.BalancedNeckChain




theorem exists_positive_frontier_negative_quarter_exclusion :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T3Space M] {g : RiemannianMetric 3 M} {epsilon : ℝ},
      ∀ (C : BalancedNeckChain g epsilon) {a b : ℤ},
      C.shape = ChainShape.finite a b →
      epsilon ≤ epsilon0 →
      (∀ i ∈ C.shape.active, (C.neck i).IsSeparating) →
      ∀ (N' : EpsilonNeck g),
      N'.epsilon = epsilon →
      N'.center ∈ closure ((C.neck b).region 0 epsilon⁻¹) →
      N'.center ∉ (⋃ i ∈ C.shape.active, (C.neck i).carrier) →
      ∀ i ∈ C.shape.active,
        Disjoint N'.carrier
          ((C.neck i).region (-epsilon⁻¹) (-epsilon⁻¹ / 2)) := by
  classical
  obtain ⟨epsilonS, hS, hScap, hscale⟩ :=
    EpsilonNeck.exists_intersecting_scale_control.{u} (α := 1 / 100) (by norm_num)
  let B := Real.sqrt 2 * (Real.pi + 1)
  have hB : 0 < B := by dsimp only [B]; positivity
  have hden : 0 < 1000 * (B + 1) := by positivity
  refine ⟨min epsilonS (1 / (1000 * (B + 1))),
    lt_min hS (div_pos zero_lt_one hden), (min_le_left _ _).trans hScap, ?_⟩
  intro M _ _ _ _ _ _ g epsilon C a b hshape he hsep N' hepsilon hy hyout
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
  have hactive (j : ℤ) : j ∈ C.shape.active ↔ j ∈ Icc a b := by
    rw [hshape]
    rfl
  obtain ⟨j0, hj0⟩ := C.active_nonempty
  have hab : a ≤ b := ((hactive j0).mp hj0).1.trans ((hactive j0).mp hj0).2
  have hepos : 0 < epsilon := by
    rw [← C.epsilon_eq j0 hj0]
    exact (C.neck j0).epsilon_pos
  let L := epsilon⁻¹
  have hL : 0 < L := inv_pos.mpr hepos
  have heS : epsilon ≤ epsilonS := he.trans (min_le_left _ _)
  have hcap : epsilon ≤ 1 / 200 := heS.trans hScap
  have hsmall : epsilon ≤ 1 / (1000 * (B + 1)) := he.trans (min_le_right _ _)
  have hBL : B ≤ L / 1000 := by
    have h := (le_div_iff₀ hden).mp hsmall
    have hBe : B * epsilon ≤ 1 / 1000 := by nlinarith
    calc
      B ≤ (1 / 1000) / epsilon := (le_div_iff₀ hepos).mpr hBe
      _ = L / 1000 := by dsimp only [L]; ring
  have hbeta : (99 : ℝ) / 100 ≤ Real.sqrt (1 - epsilon) :=
    Real.le_sqrt_of_sq_le (by nlinarith)
  have hp : Real.sqrt (1 + epsilon) ≤ (101 : ℝ) / 100 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by nlinarith⟩
  have hc' := (N'.mem_central_sphere_iff N'.center).mp N'.center_on_central_sphere
  intro i hi
  let N := C.neck i
  have hiI := (hactive i).mp hi
  have hiLe : i ≤ b := hiI.2
  have hNe : N.epsilon = epsilon := C.epsilon_eq i hi
  have hr : 0 < N.scale := N.scale_pos
  have hyoutN : N'.center ∉ N.carrier := by
    intro hx
    exact hyout (mem_iUnion₂.mpr ⟨i, hi, hx⟩)
  obtain ⟨a0, b0, ha0, hb0, _, _, _, _, _, hcover⟩ :=
    N.exists_opposite_central_components (hsep i hi)
  obtain ⟨H, hH, hinside, hminus, hplus, _, hdist⟩ :=
    N.exists_saturatedAxialHeight (hsep i hi) a0 b0 ha0 hb0
  have hout {x : M} (hxK : x ∈ connectedComponent N.center) (hx : x ∉ N.carrier) :
      H x = -L ∨ H x = L := by
    rw [← hcover] at hxK
    rcases hxK with (hxA | hxS) | hxB
    · exact Or.inl (by simpa only [hNe] using hminus x ⟨hxA, hx⟩)
    · exact False.elim (hx (N.central_sphere_subset hxS))
    · exact Or.inr (by simpa only [hNe] using hplus x ⟨hxB, hx⟩)
  have hyH : H N'.center = L := by
    by_cases hib : i < b
    · have hJactive {j : ℤ} (hj : j ∈ Ioc i b) : j ∈ C.shape.active :=
        (hactive j).mpr ⟨hiI.1.trans hj.1.le, hj.2⟩
      have hcuts : ∀ j : ℤ, ∃ s : ℝ, j ∈ Ioc i b →
          s ∈ Ioo (-L) 0 ∧ Disjoint (C.neck j).carrier (N.region (-L) s) := by
        intro j
        by_cases hj : j ∈ Ioc i b
        · obtain ⟨s, hs, hd⟩ := C.later_disjoint_negative_end i hi j (hJactive hj) hj.1
          exact ⟨s, fun _ => ⟨hs, hd⟩⟩
        · exact ⟨0, fun hj' => False.elim (hj hj')⟩
      choose s hs using hcuts
      let J := Finset.Ioc i b
      have hbJ : b ∈ J := Finset.mem_Ioc.mpr ⟨hib, le_rfl⟩
      let Q := J.image s
      have hQ : Q.Nonempty := ⟨s b, Finset.mem_image.mpr ⟨b, hbJ, rfl⟩⟩
      let m := Q.min' hQ
      have hm : m ∈ Ioo (-L) 0 := by
        obtain ⟨j, hj, hjm⟩ := Finset.mem_image.mp (Q.min'_mem hQ)
        dsimp only [m]
        rw [← hjm]
        exact (hs j (Finset.mem_Ioc.mp hj)).1
      have hmin {j : ℤ} (hj : j ∈ Ioc i b) : m ≤ s j :=
        Q.min'_le (s j) (Finset.mem_image.mpr ⟨j, Finset.mem_Ioc.mpr hj, rfl⟩)
      let t := (-L + m) / 2
      have htlo : -L < t := by dsimp only [t]; linarith [hm.1]
      have htm : t < m := by dsimp only [t]; linarith [hm.1]
      have htneg : t < 0 := htm.trans hm.2
      have ht : t ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
        rw [hNe]
        exact ⟨htlo, htneg.trans hL⟩
      let T := ⋃ j ∈ Ioc i b, (C.neck j).carrier
      have hT : IsConnected T := by
        apply IsConnected.biUnion_of_chain (t := Ioc i b)
          ⟨b, hib, le_rfl⟩ ordConnected_Ioc
        · intro j _
          exact (C.neck j).isConnected_carrier
        · intro j hj hjnext
          have hj1 : j + 1 ∈ Ioc i b := by
            simpa only [Order.succ_eq_add_one] using hjnext
          simpa only [Order.succ_eq_add_one] using
            C.adjacent_overlap j (hJactive hj) (hJactive hj1)
      have havoid {x : M} (hx : x ∈ T) :
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
      have hi1 : i + 1 ∈ Ioc i b := ⟨by omega, by omega⟩
      have hwT : w ∈ T := by
        apply mem_iUnion₂.mpr
        refine ⟨i + 1, hi1, (C.overlap_contains_quarters i hi (hJactive hi1)).1 ?_⟩
        refine ⟨hwN, ?_⟩
        rw [N.coordinate_inverse_map (q0, 3 * L / 4) hthree]
        change L / 2 < 3 * L / 4 ∧ 3 * L / 4 < L
        constructor <;> linarith
      have hTK : T ⊆ connectedComponent N.center := by
        have hwK := N.m25_carrier_subset_connectedComponent hwN
        have hsub := hT.subset_connectedComponent hwT
        rw [← connectedComponent_eq hwK] at hsub
        exact hsub
      have hnotlevel : ∀ x ∈ T, H x ≠ t := by
        intro x hx hxt
        by_cases hxN : x ∈ N.carrier
        · apply havoid hx
          refine ⟨(N.coordinate_inverse x).1, ?_⟩
          rw [hinside x hxN] at hxt
          rw [← hxt]
          exact N.coordinate_map_inverse hxN
        · rcases hout (hTK hx) hxN with h | h <;> linarith
      have hpositive : ∀ x ∈ T, t < H x := fun x hx =>
        hT.isPreconnected.lt_of_ne hH.continuousOn hnotlevel
          ⟨w, hwT, by rw [hwheight]; linarith⟩ hx
      have hlast : (C.neck b).region 0 epsilon⁻¹ ⊆ T := by
        intro x hx
        exact mem_iUnion₂.mpr ⟨b, ⟨hib, le_rfl⟩, hx.1⟩
      have hyT : N'.center ∈ closure T := closure_mono hlast hy
      have hyK := closure_minimal hTK isClosed_connectedComponent hyT
      have hyge : t ≤ H N'.center := closure_minimal
        (fun x hx => (hpositive x hx).le) (isClosed_le continuous_const hH) hyT
      rcases hout hyK hyoutN with h | h
      · linarith
      · exact h
    · have hibEq : i = b := by omega
      have hyN : N'.center ∈ closure (N.region 0 epsilon⁻¹) := by
        simpa only [N, hibEq] using hy
      have hyK : N'.center ∈ connectedComponent N.center :=
        closure_minimal (fun _ hx => N.m25_carrier_subset_connectedComponent hx.1)
          isClosed_connectedComponent hyN
      have hyge : 0 ≤ H N'.center := by
        apply closure_minimal (t := {x | 0 ≤ H x}) ?_
          (isClosed_le continuous_const hH) hyN
        intro x hx
        change 0 ≤ H x
        rw [hinside x hx.1]
        exact hx.2.1.le
      rcases hout hyK hyoutN with h | h
      · linarith
      · exact h
  refine Set.disjoint_left.mpr ?_
  intro z hz' hzN
  have hratio := (hscale N N' (by rw [hNe]; exact heS)
    (by rw [hepsilon]; exact heS) ⟨z, hzN.1, hz'⟩).2
  have hscaleUpper : N'.scale ≤ (101 : ℝ) / 100 * N.scale :=
    ((div_lt_iff₀ N.scale_pos).mp
      (show N'.scale / N.scale < (101 : ℝ) / 100 by
        linarith [(abs_lt.mp hratio).2])).le
  have hprodUpper : N'.scale * Real.sqrt (1 + epsilon) ≤
      (10201 : ℝ) / 10000 * N.scale := by
    calc
      _ ≤ ((101 / 100) * N.scale) * (101 / 100) :=
        mul_le_mul hscaleUpper hp (Real.sqrt_nonneg _) (by positivity)
      _ = _ := by ring
  have hu : g.edist z N'.center ≤
      ENNReal.ofReal ((10211201 : ℝ) / 10000000 * N.scale * L) := by
    have h := N'.edist_le_axial_add hz' hc'.1
    rw [hc'.2, zero_sub, abs_neg, hepsilon] at h
    have hheight : |(N'.coordinate_inverse z).2| ≤ L := by
      simpa only [hepsilon] using (abs_lt.mpr (N'.coordinate_inverse_mem z hz').2).le
    apply h.trans (ENNReal.ofReal_le_ofReal ?_)
    change N'.scale * Real.sqrt (1 + epsilon) * (|(N'.coordinate_inverse z).2| + B) ≤ _
    calc
      _ ≤ ((10201 : ℝ) / 10000 * N.scale) * (|(N'.coordinate_inverse z).2| + B) :=
        mul_le_mul_of_nonneg_right hprodUpper (add_nonneg (abs_nonneg _) hB.le)
      _ ≤ ((10201 : ℝ) / 10000 * N.scale) * (L + L / 1000) :=
        mul_le_mul_of_nonneg_left (add_le_add hheight hBL) (by positivity)
      _ = _ := by ring
  have hheight : H z < -L / 2 := by rw [hinside z hzN.1]; exact hzN.2.2
  have hgap : 3 * L / 2 ≤ |H z - L| := by
    rw [abs_of_neg (by linarith : H z - L < 0)]
    linarith
  have hd : ENNReal.ofReal ((1485 : ℝ) / 1000 * N.scale * L) ≤
      g.edist z N'.center := by
    have h := hdist z N'.center
    rw [hyH, hNe] at h
    apply (ENNReal.ofReal_le_ofReal ?_).trans h
    calc
      _ = N.scale * (99 / 100) * (3 * L / 2) := by ring
      _ ≤ N.scale * Real.sqrt (1 - epsilon) * (3 * L / 2) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbeta hr.le) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left hgap
        (mul_nonneg hr.le (Real.sqrt_nonneg _))
  have hstrict : ENNReal.ofReal ((10211201 : ℝ) / 10000000 * N.scale * L) <
      ENNReal.ofReal ((1485 : ℝ) / 1000 * N.scale * L) := by
    apply (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
    nlinarith [mul_pos hr hL]
  exact (not_le_of_gt hstrict) (hd.trans hu)

end PoincareConjecture.BalancedNeckChain
