import PoincareConjecture.Proofs.M25.AppA_20_Fibration.FiniteExtensionReturn
import PoincareConjecture.Proofs.M25.AppA_20_Fibration.FiniteBackwardExtensionReturn
import PoincareConjecture.Proofs.M25.AppA_20_Fibration.ForwardInfiniteEndSeparation
import PoincareConjecture.Proofs.M25.AppA_20_Fibration.BackwardInfiniteEndSeparation
import PoincareConjecture.Proofs.M25.AppA_1_Necks.FiniteChainFrontier
import PoincareConjecture.Proofs.M25.AppA_1_Necks.CoherentChainLimit
import Mathlib.Logic.Function.Iterate










set_option autoImplicit false
open Set Topology
open scoped Manifold ContDiff
universe u
namespace PoincareConjecture




theorem NeckOnlyCover.exists_two_ended_finite_chain_or_deep_return :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T3Space M] {g : RiemannianMetric 3 M},
      ∀ (H : NeckOnlyCover g), H.epsilon ≤ epsilon0 →
      (∀ N ∈ H.necks, N.IsNonseparating) →
      ∀ (N : EpsilonNeck g), N ∈ H.necks → N.center ∈ H.X →
      ∃ (C : BalancedNeckChain g H.epsilon) (a b : ℤ),
        C.shape = ChainShape.finite a b ∧ C.source_necks = H.necks ∧
        a ≤ 0 ∧ 0 ≤ b ∧ C.neck 0 = N ∧
        (∀ i ∈ C.shape.active, (C.neck i).center ∈ H.X) ∧
        (∀ i ∈ C.shape.active, i + 1 ∈ C.shape.active →
          closure ((C.neck i).region (H.epsilon⁻¹ / 2) H.epsilon⁻¹) ⊆
              (C.neck (i + 1)).carrier ∧
            closure ((C.neck (i + 1)).region
                (-H.epsilon⁻¹) (-H.epsilon⁻¹ / 2)) ⊆ (C.neck i).carrier) ∧
        (∀ i ∈ C.shape.active, i + 1 ∈ C.shape.active →
          ((C.neck (i + 1)).center ∈
                closure ((C.neck i).region 0 H.epsilon⁻¹) ∧
              (C.neck (i + 1)).center ∉ (C.neck i).carrier) ∨
            ((C.neck i).center ∈
                closure ((C.neck (i + 1)).region (-H.epsilon⁻¹) 0) ∧
              (C.neck i).center ∉ (C.neck (i + 1)).carrier)) ∧
        ((H.X ⊆ ⋃ i ∈ C.shape.active, (C.neck i).carrier) ∨
          ∃ R ∈ H.necks, R.epsilon = H.epsilon ∧ R.center ∈ H.X ∧
            R.center ∉ (⋃ i ∈ C.shape.active, (C.neck i).carrier) ∧
            ((R.center ∈ closure ((C.neck b).region 0 H.epsilon⁻¹) ∧
                ∀ c ∈ Ioo (-H.epsilon⁻¹) 0,
                  ¬ Disjoint R.carrier ((C.neck a).region (-H.epsilon⁻¹) c)) ∨
              (R.center ∈ closure ((C.neck a).region (-H.epsilon⁻¹) 0) ∧
                ∀ c ∈ Ioo (0 : ℝ) H.epsilon⁻¹,
                  ¬ Disjoint R.carrier ((C.neck b).region c H.epsilon⁻¹)))) := by
  obtain ⟨ef, hfp, hfcap, forwardStep⟩ :=
    BalancedNeckChain.exists_finite_forward_extension_or_deep_return.{u}
  obtain ⟨eb, hbp, _, backwardStep⟩ :=
    BalancedNeckChain.exists_finite_backward_extension_or_deep_return.{u}
  obtain ⟨ei, hip, _, forwardEnd⟩ :=
    BalancedNeckChain.N1b_initial_isSeparating_of_forward_chain.{u}
  obtain ⟨ej, hjp, _, backwardEnd⟩ :=
    BalancedNeckChain.exists_terminal_isSeparating_of_backward_chain.{u}
  refine ⟨min ef (min eb (min ei ej)), by positivity,
    (min_le_left _ _).trans hfcap, ?_⟩
  intro M _ _ _ _ _ _ g H he hnon N hN hNX
  classical
  rcases le_min_iff.mp he with ⟨hef, he⟩
  rcases le_min_iff.mp he with ⟨heb, he⟩
  rcases le_min_iff.mp he with ⟨hei, hej⟩
  let L := H.epsilon⁻¹
  let U (C : BalancedNeckChain g H.epsilon) : Set M :=
    ⋃ i ∈ C.shape.active, (C.neck i).carrier
  let Quarters (C : BalancedNeckChain g H.epsilon) : Prop :=
    ∀ i ∈ C.shape.active, i + 1 ∈ C.shape.active →
      closure ((C.neck i).region (L / 2) L) ⊆ (C.neck (i + 1)).carrier ∧
        closure ((C.neck (i + 1)).region (-L) (-L / 2)) ⊆ (C.neck i).carrier
  let Incidence (C : BalancedNeckChain g H.epsilon) : Prop :=
    ∀ i ∈ C.shape.active, i + 1 ∈ C.shape.active →
      ((C.neck (i + 1)).center ∈ closure ((C.neck i).region 0 L) ∧
          (C.neck (i + 1)).center ∉ (C.neck i).carrier) ∨
        ((C.neck i).center ∈ closure ((C.neck (i + 1)).region (-L) 0) ∧
          (C.neck i).center ∉ (C.neck (i + 1)).carrier)
  let Good (a b : ℤ) (C : BalancedNeckChain g H.epsilon) : Prop :=
    C.shape = ChainShape.finite a b ∧ C.source_necks = H.necks ∧
      a ≤ 0 ∧ 0 ≤ b ∧ C.neck 0 = N ∧
      (∀ i ∈ C.shape.active, (C.neck i).center ∈ H.X) ∧
      Quarters C ∧ Incidence C
  let Stop (a b : ℤ) (C : BalancedNeckChain g H.epsilon) : Prop :=
    (H.X ⊆ U C) ∨
      ∃ R ∈ H.necks, R.epsilon = H.epsilon ∧ R.center ∈ H.X ∧ R.center ∉ U C ∧
        ((R.center ∈ closure ((C.neck b).region 0 L) ∧
            ∀ c ∈ Ioo (-L) 0, ¬ Disjoint R.carrier ((C.neck a).region (-L) c)) ∨
          (R.center ∈ closure ((C.neck a).region (-L) 0) ∧
            ∀ c ∈ Ioo (0 : ℝ) L, ¬ Disjoint R.carrier ((C.neck b).region c L)))
  by_contra hno
  have hnostop (a b : ℤ) (C : BalancedNeckChain g H.epsilon)
      (hg : Good a b C) : ¬ Stop a b C := by
    intro hs
    rcases hg with ⟨hshape, hsource, ha, hb, hstart, hcenters, hquarters, hinc⟩
    exact hno ⟨C, a, b, hshape, hsource, ha, hb, hstart, hcenters, hquarters, hinc, hs⟩
  have hnext (a b : ℤ) (C : BalancedNeckChain g H.epsilon) (hg : Good a b C) :
      ∃ (a' b' : ℤ) (D : BalancedNeckChain g H.epsilon),
        Good a' b' D ∧ C.shape.active ⊆ D.shape.active ∧
          (∀ i ∈ C.shape.active, D.neck i = C.neck i) ∧ b' - a' = b - a + 1 := by
    have hstop := hnostop a b C hg
    rcases hg with ⟨hshape, hsource, ha0, hb0, hstart, hcenters, hquarters, hinc⟩
    have active (i : ℤ) : i ∈ C.shape.active ↔ a ≤ i ∧ i ≤ b := by
      rw [hshape]
      rfl
    have ha := (active a).mpr ⟨le_rfl, ha0.trans hb0⟩
    have hb := (active b).mpr ⟨ha0.trans hb0, le_rfl⟩
    have hzero := (active 0).mpr ⟨ha0, hb0⟩
    have hmeet : (H.X ∩ U C).Nonempty := by
      refine ⟨N.center, hNX, mem_iUnion₂.mpr ⟨0, hzero, ?_⟩⟩
      rw [hstart]
      exact N.central_sphere_subset N.center_on_central_sphere
    have hnot : ¬ H.X ⊆ U C := fun h => hstop (Or.inl h)
    obtain ⟨R, hRC, heR, hRX, hRout, hfront⟩ :=
      BalancedNeckChain.exists_exterior_end_center_of_not_subset
        H C hshape hquarters hsource hmeet hnot
    have hRH : R ∈ H.necks := hsource ▸ hRC
    rcases hfront with hneg | hpos
    · rcases backwardStep C hshape heb R hRC heR hneg hRout with hext | hret
      · obtain ⟨Q, D, _hchoice, hsel, hshapeD, hsourceD, hneckD, hq1, hq2⟩ := hext
        have hQc : Q.center = R.center := hsel.2.2.1
        have hnew : D.neck (a - 1) = Q := by rw [hneckD, Function.update_self]
        have hold (i : ℤ) (hi : i ∈ C.shape.active) : D.neck i = C.neck i := by
          have hlo := ((active i).mp hi).1
          rw [hneckD, Function.update_of_ne (show i ≠ a - 1 by omega)]
        have hactiveD (i : ℤ) : i ∈ D.shape.active ↔ a - 1 ≤ i ∧ i ≤ b := by
          rw [hshapeD]
          rfl
        have hcentersD : ∀ i ∈ D.shape.active, (D.neck i).center ∈ H.X := by
          intro i hi
          have hbounds := (hactiveD i).mp hi
          by_cases hinew : i = a - 1
          · rw [hinew, hnew, hQc]
            exact hRX
          · have hio : i ∈ C.shape.active := (active i).mpr ⟨by omega, hbounds.2⟩
            rw [hold i hio]
            exact hcenters i hio
        have hquartersD : Quarters D := by
          intro i hi hi1
          have hbdi := (hactiveD i).mp hi
          have hbdi1 := (hactiveD (i + 1)).mp hi1
          by_cases hia : i = a - 1
          · have hs : a - 1 + 1 = a := by omega
            rw [hia, hs, hnew, hold a ha]
            exact ⟨hq1, hq2⟩
          · have hio : i ∈ C.shape.active := (active i).mpr ⟨by omega, hbdi.2⟩
            have hi1o : i + 1 ∈ C.shape.active :=
              (active (i + 1)).mpr ⟨by omega, hbdi1.2⟩
            rw [hold i hio, hold (i + 1) hi1o]
            exact hquarters i hio hi1o
        have hincD : Incidence D := by
          intro i hi hi1
          have hbdi := (hactiveD i).mp hi
          have hbdi1 := (hactiveD (i + 1)).mp hi1
          by_cases hia : i = a - 1
          · have hs : a - 1 + 1 = a := by omega
            rw [hia, hs, hnew, hold a ha, hQc]
            exact Or.inr ⟨hneg, fun hx => hRout (mem_iUnion₂.mpr ⟨a, ha, hx⟩)⟩
          · have hio : i ∈ C.shape.active := (active i).mpr ⟨by omega, hbdi.2⟩
            have hi1o : i + 1 ∈ C.shape.active :=
              (active (i + 1)).mpr ⟨by omega, hbdi1.2⟩
            rw [hold i hio, hold (i + 1) hi1o]
            exact hinc i hio hi1o
        refine ⟨a - 1, b, D,
          ⟨hshapeD, hsourceD.trans hsource, by omega, hb0,
            (hold 0 hzero).trans hstart, hcentersD, hquartersD, hincD⟩, ?_, hold, by omega⟩
        intro i hi
        have hbounds := (active i).mp hi
        exact (hactiveD i).mpr ⟨by omega, hbounds.2⟩
      · exact (hstop (Or.inr ⟨R, hRH, heR, hRX, hRout, Or.inr ⟨hneg, hret⟩⟩)).elim
    · rcases forwardStep C hshape hef R hRC heR hpos hRout with hext | hret
      · obtain ⟨Q, D, _hchoice, hsel, hshapeD, hsourceD, hneckD, hq1, hq2⟩ := hext
        have hQc : Q.center = R.center := hsel.2.2.1
        have hnew : D.neck (b + 1) = Q := by rw [hneckD, Function.update_self]
        have hold (i : ℤ) (hi : i ∈ C.shape.active) : D.neck i = C.neck i := by
          have hhi := ((active i).mp hi).2
          rw [hneckD, Function.update_of_ne (show i ≠ b + 1 by omega)]
        have hactiveD (i : ℤ) : i ∈ D.shape.active ↔ a ≤ i ∧ i ≤ b + 1 := by
          rw [hshapeD]
          rfl
        have hcentersD : ∀ i ∈ D.shape.active, (D.neck i).center ∈ H.X := by
          intro i hi
          have hbounds := (hactiveD i).mp hi
          by_cases hinew : i = b + 1
          · rw [hinew, hnew, hQc]
            exact hRX
          · have hio : i ∈ C.shape.active := (active i).mpr ⟨hbounds.1, by omega⟩
            rw [hold i hio]
            exact hcenters i hio
        have hquartersD : Quarters D := by
          intro i hi hi1
          have hbdi := (hactiveD i).mp hi
          have hbdi1 := (hactiveD (i + 1)).mp hi1
          by_cases hib : i = b
          · rw [hib, hnew, hold b hb]
            exact ⟨hq1, hq2⟩
          · have hio : i ∈ C.shape.active := (active i).mpr ⟨hbdi.1, by omega⟩
            have hi1o : i + 1 ∈ C.shape.active :=
              (active (i + 1)).mpr ⟨hbdi1.1, by omega⟩
            rw [hold i hio, hold (i + 1) hi1o]
            exact hquarters i hio hi1o
        have hincD : Incidence D := by
          intro i hi hi1
          have hbdi := (hactiveD i).mp hi
          have hbdi1 := (hactiveD (i + 1)).mp hi1
          by_cases hib : i = b
          · rw [hib, hnew, hold b hb, hQc]
            exact Or.inl ⟨hpos, fun hx => hRout (mem_iUnion₂.mpr ⟨b, hb, hx⟩)⟩
          · have hio : i ∈ C.shape.active := (active i).mpr ⟨hbdi.1, by omega⟩
            have hi1o : i + 1 ∈ C.shape.active :=
              (active (i + 1)).mpr ⟨hbdi1.1, by omega⟩
            rw [hold i hio, hold (i + 1) hi1o]
            exact hinc i hio hi1o
        refine ⟨a, b + 1, D,
          ⟨hshapeD, hsourceD.trans hsource, ha0, by omega,
            (hold 0 hzero).trans hstart, hcentersD, hquartersD, hincD⟩, ?_, hold, by omega⟩
        intro i hi
        have hbounds := (active i).mp hi
        exact (hactiveD i).mpr ⟨hbounds.1, by omega⟩
      · exact (hstop (Or.inr ⟨R, hRH, heR, hRX, hRout, Or.inl ⟨hpos, hret⟩⟩)).elim
  have hsingle {i : ℤ} (hi : i ∈ (ChainShape.finite 0 0).active)
      (hi1 : i + 1 ∈ (ChainShape.finite 0 0).active) : False := by
    change 0 ≤ i ∧ i ≤ 0 at hi
    change 0 ≤ i + 1 ∧ i + 1 ≤ 0 at hi1
    omega
  let C0 : BalancedNeckChain g H.epsilon := {
    shape := .finite 0 0
    neck := fun _ => N
    source_necks := H.necks
    selected := by
      intro _ _
      refine ⟨N, hN, rfl, rfl, rfl, rfl, rfl, 1, Or.inl rfl, ?_⟩
      intro z _
      simp only [one_mul]
    active_nonempty := ⟨0, le_rfl, le_rfl⟩
    epsilon_eq := fun _ _ => H.neck_epsilon N hN
    centers_distinct := by
      intro i hi j hj hij
      change 0 ≤ i ∧ i ≤ 0 at hi
      change 0 ≤ j ∧ j ≤ 0 at hj
      omega
    adjacent_overlap := fun _ hi hi1 => (hsingle hi hi1).elim
    overlap_contains_quarters := fun _ hi hi1 => (hsingle hi hi1).elim
    overlap_within_three_quarters := fun _ hi hi1 => (hsingle hi hi1).elim
    later_disjoint_negative_end := by
      intro i hi j hj hij
      change 0 ≤ i ∧ i ≤ 0 at hi
      change 0 ≤ j ∧ j ≤ 0 at hj
      omega
    balanced_center_distance := fun _ hi hi1 => (hsingle hi hi1).elim }
  have hC0 : Good 0 0 C0 :=
    ⟨rfl, rfl, le_rfl, le_rfl, rfl, fun _ _ => hNX,
      fun _ hi hi1 => (hsingle hi hi1).elim,
      fun _ hi hi1 => (hsingle hi hi1).elim⟩
  let State := {s : ℤ × ℤ × BalancedNeckChain g H.epsilon // Good s.1 s.2.1 s.2.2}
  let Step (s t : State) : Prop :=
    s.1.2.2.shape.active ⊆ t.1.2.2.shape.active ∧
      (∀ i ∈ s.1.2.2.shape.active, t.1.2.2.neck i = s.1.2.2.neck i) ∧
      t.1.2.1 - t.1.1 = s.1.2.1 - s.1.1 + 1
  have hround (s : State) : ∃ t : State, Step s t := by
    obtain ⟨a, b, D, hg, hsub, hretain, hwidth⟩ := hnext s.1.1 s.1.2.1 s.1.2.2 s.2
    exact ⟨⟨(a, b, D), hg⟩, hsub, hretain, hwidth⟩
  let seed : State := ⟨(0, 0, C0), hC0⟩
  choose step hstep using hround
  let seq : ℕ → State := fun n => step^[n] seed
  have hsucc (n : ℕ) : seq (n + 1) = step (seq n) :=
    Function.iterate_succ_apply' step n seed
  have hseq (n : ℕ) : Step (seq n) (seq (n + 1)) := by
    rw [hsucc]
    exact hstep (seq n)
  let a : ℕ → ℤ := fun n => (seq n).1.1
  let b : ℕ → ℤ := fun n => (seq n).1.2.1
  let C : ℕ → BalancedNeckChain g H.epsilon := fun n => (seq n).1.2.2
  have good (n : ℕ) : Good (a n) (b n) (C n) := (seq n).2
  have shape (n : ℕ) : (C n).shape = ChainShape.finite (a n) (b n) := (good n).1
  have source (n : ℕ) : (C n).source_necks = H.necks := (good n).2.1
  have zero (n : ℕ) : (0 : ℤ) ∈ (C n).shape.active := by
    rw [shape n]
    exact ⟨(good n).2.2.1, (good n).2.2.2.1⟩
  have width (n : ℕ) : b n - a n = (n : ℤ) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      have hs : b (n + 1) - a (n + 1) = b n - a n + 1 := (hseq n).2.2
      simpa only [Int.natCast_succ, ih] using hs
  have mono : Monotone (fun n => (C n).shape.active) :=
    monotone_nat_of_le_succ (fun n => (hseq n).1)
  obtain ⟨D, hactive, _hsource, hneck⟩ :=
    BalancedNeckChain.exists_coherent_finite_limit C a b shape
      (fun n => (hseq n).1) (fun n => (hseq n).2.1)
      (fun n => (source n).trans (source 0).symm)
  have stage (n : ℕ) : (C n).shape.active ⊆ D.shape.active := by
    rw [hactive]
    exact subset_iUnion (fun k => (C k).shape.active) n
  have hzero : (0 : ℤ) ∈ D.shape.active := stage 0 (zero 0)
  have hstart : D.neck 0 = N := (hneck 0 0 (zero 0)).trans (good 0).2.2.2.2.1
  have common {i j : ℤ} (hi : i ∈ D.shape.active) (hj : j ∈ D.shape.active) :
      ∃ n, i ∈ (C n).shape.active ∧ j ∈ (C n).shape.active := by
    rw [hactive] at hi hj
    obtain ⟨n, hn⟩ := mem_iUnion.mp hi
    obtain ⟨m, hm⟩ := mem_iUnion.mp hj
    exact ⟨max n m, mono (Nat.le_max_left _ _) hn, mono (Nat.le_max_right _ _) hm⟩
  have hquartersD : Quarters D := by
    intro i hi hi1
    obtain ⟨n, hn, hn1⟩ := common hi hi1
    rw [hneck n i hn, hneck n (i + 1) hn1]
    exact (good n).2.2.2.2.2.2.1 i hn hn1
  have hincD : Incidence D := by
    intro i hi hi1
    obtain ⟨n, hn, hn1⟩ := common hi hi1
    rw [hneck n i hn, hneck n (i + 1) hn1]
    exact (good n).2.2.2.2.2.2.2 i hn hn1
  let restrict (s : ChainShape) (hs : s.active ⊆ D.shape.active)
      (hz : (0 : ℤ) ∈ s.active) : BalancedNeckChain g H.epsilon := {
    shape := s
    neck := D.neck
    source_necks := D.source_necks
    selected := fun i hi => D.selected i (hs hi)
    active_nonempty := ⟨0, hz⟩
    epsilon_eq := fun i hi => D.epsilon_eq i (hs hi)
    centers_distinct := fun i hi j hj hij => D.centers_distinct (hs hi) (hs hj) hij
    adjacent_overlap := fun i hi hi1 => D.adjacent_overlap i (hs hi) (hs hi1)
    overlap_contains_quarters := fun i hi hi1 =>
      D.overlap_contains_quarters i (hs hi) (hs hi1)
    overlap_within_three_quarters := fun i hi hi1 =>
      D.overlap_within_three_quarters i (hs hi) (hs hi1)
    later_disjoint_negative_end := fun i hi j hj hij =>
      D.later_disjoint_negative_end i (hs hi) j (hs hj) hij
    balanced_center_distance := fun i hi hi1 =>
      D.balanced_center_distance i (hs hi) (hs hi1) }
  have separatedForward (hs : Ici (0 : ℤ) ⊆ D.shape.active) : N.IsSeparating := by
    let E := restrict (ChainShape.forward 0) hs (show (0 : ℤ) ≤ 0 from le_rfl)
    have quarters := hquartersD 0 (hs (show (0 : ℤ) ≤ 0 from le_rfl))
      (hs (by norm_num : (1 : ℤ) ∈ Ici 0))
    have incidence : Incidence E := fun i hi hi1 => hincD i (hs hi) (hs hi1)
    have hsep := forwardEnd E 0 rfl hei quarters incidence
    change (D.neck 0).IsSeparating at hsep
    rwa [hstart] at hsep
  have separatedBackward (hs : Iic (0 : ℤ) ⊆ D.shape.active) : N.IsSeparating := by
    let E := restrict (ChainShape.backward 0) hs (show (0 : ℤ) ≤ 0 from le_rfl)
    have hm : (-1 : ℤ) ∈ D.shape.active := hs (by norm_num)
    have hp : (-1 : ℤ) + 1 ∈ D.shape.active := by
      simpa using hs (show (0 : ℤ) ≤ 0 from le_rfl)
    have quarters := hquartersD (-1) hm hp
    have incidence : Incidence E := fun i hi hi1 => hincD i (hs hi) (hs hi1)
    have hsep := backwardEnd E 0 rfl hej
      (by simpa only [E, restrict, L, zero_sub, neg_add_cancel] using quarters) incidence
    change (D.neck 0).IsSeparating at hsep
    rwa [hstart] at hsep
  cases hd : D.shape with
  | finite p q =>
    have bound (n : ℕ) : (n : ℤ) ≤ q - p := by
      have hgood := good n
      have han : a n ∈ (C n).shape.active := by
        rw [shape n]
        exact ⟨le_rfl, hgood.2.2.1.trans hgood.2.2.2.1⟩
      have hbn : b n ∈ (C n).shape.active := by
        rw [shape n]
        exact ⟨hgood.2.2.1.trans hgood.2.2.2.1, le_rfl⟩
      have haD : p ≤ a n ∧ a n ≤ q := by
        simpa only [hd, ChainShape.active, mem_Icc] using stage n han
      have hbD : p ≤ b n ∧ b n ≤ q := by
        simpa only [hd, ChainShape.active, mem_Icc] using stage n hbn
      rw [← width n]
      omega
    have hnonneg : 0 ≤ q - p := by simpa using bound 0
    have hbad := bound ((q - p).toNat + 1)
    rw [Int.natCast_add, Int.natCast_one, Int.toNat_of_nonneg hnonneg] at hbad
    omega
  | forward p =>
    have hp : p ≤ 0 := by simpa only [hd, ChainShape.active, mem_Ici] using hzero
    have hs : Ici (0 : ℤ) ⊆ D.shape.active := by
      intro i hi
      rw [hd]
      exact hp.trans hi
    exact (separatedForward hs).2 (hnon N hN)
  | backward q =>
    have hq : 0 ≤ q := by simpa only [hd, ChainShape.active, mem_Iic] using hzero
    have hs : Iic (0 : ℤ) ⊆ D.shape.active := by
      intro i hi
      rw [hd]
      exact hi.trans hq
    exact (separatedBackward hs).2 (hnon N hN)
  | biInfinite =>
    have hs : Ici (0 : ℤ) ⊆ D.shape.active := by
      rw [hd]
      exact subset_univ _
    exact (separatedForward hs).2 (hnon N hN)

end PoincareConjecture
