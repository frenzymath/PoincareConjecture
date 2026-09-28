import PoincareConjecture.Proofs.M25.AppA_20_Fibration.FiniteExtensionReturn
import PoincareConjecture.Proofs.M25.AppA_1_Necks.FiniteChainFrontier
import PoincareConjecture.Proofs.M25.AppA_1_Necks.CoherentChainLimit
import PoincareConjecture.Proofs.M25.AppA_20_Fibration.ForwardInfiniteEndSeparation
import Mathlib.Logic.Function.Iterate

set_option autoImplicit false
open Set Topology
open scoped Manifold ContDiff
universe u
namespace PoincareConjecture

theorem NeckOnlyCover.exists_finite_forward_chain_or_protected_deep_return :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T3Space M] {g : RiemannianMetric 3 M},
      ∀ (H : NeckOnlyCover g), H.epsilon ≤ epsilon0 →
      ∀ (N : EpsilonNeck g),
      (∃ P ∈ H.necks, N.SameUpToReversal P) →
      N.epsilon = H.epsilon → N.center ∈ H.X → N.IsNonseparating →
      Disjoint H.X
        (closure (N.region (-H.epsilon⁻¹) (-(99 * H.epsilon⁻¹ / 100)))) →
      ∃ (b : ℤ) (D : BalancedNeckChain g H.epsilon),
        0 ≤ b ∧ D.shape = ChainShape.finite 0 b ∧
        D.source_necks = H.necks ∧ D.neck 0 = N ∧
        (∀ i ∈ D.shape.active, (D.neck i).center ∈ H.X) ∧
        (∀ i ∈ D.shape.active, i + 1 ∈ D.shape.active →
          closure ((D.neck i).region (H.epsilon⁻¹ / 2) H.epsilon⁻¹) ⊆
              (D.neck (i + 1)).carrier ∧
            closure ((D.neck (i + 1)).region
                (-H.epsilon⁻¹) (-H.epsilon⁻¹ / 2)) ⊆ (D.neck i).carrier) ∧
        (∀ i ∈ D.shape.active, i + 1 ∈ D.shape.active →
          (D.neck (i + 1)).center ∈
              closure ((D.neck i).region 0 H.epsilon⁻¹) ∧
            (D.neck (i + 1)).center ∉
              (⋃ j ∈ Icc (0 : ℤ) i, (D.neck j).carrier)) ∧
        ((H.X ⊆ ⋃ i ∈ D.shape.active, (D.neck i).carrier) ∨
          ∃ R ∈ H.necks,
            R.epsilon = H.epsilon ∧ R.center ∈ H.X ∧
            R.center ∈ closure ((D.neck b).region 0 H.epsilon⁻¹) ∧
            R.center ∉ (⋃ i ∈ D.shape.active, (D.neck i).carrier) ∧
            ∀ c ∈ Ioo (-H.epsilon⁻¹) 0,
              ¬ Disjoint R.carrier (N.region (-H.epsilon⁻¹) c)) := by
  obtain ⟨ef, hfp, hfcap, forwardStep⟩ :=
    BalancedNeckChain.exists_finite_forward_extension_or_deep_return.{u}
  obtain ⟨ei, hip, _, forwardEnd⟩ :=
    BalancedNeckChain.N1b_initial_isSeparating_of_forward_chain.{u}
  refine ⟨min ef ei, lt_min hfp hip, (min_le_left _ _).trans hfcap, ?_⟩
  intro M _ _ _ _ _ _ g H he N hNS heN hNX hnon hprotected
  classical
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
  rcases le_min_iff.mp he with ⟨hef, hei⟩
  let L : ℝ := H.epsilon⁻¹
  have hL : 0 < L := inv_pos.mpr H.epsilon_pos
  let cut : ℝ := -(99 * L / 100)
  let K : Set M := N.coordinate_map '' (univ ×ˢ Icc cut (0 : ℝ))
  have hcut : -L < cut ∧ cut < 0 := by
    dsimp only [cut]
    constructor <;> linarith
  have hK : IsCompact K := by
    apply N.isCompact_coordinate_slab
    · simpa only [heN] using hcut.1
    · simpa only [heN] using hL
  have hKN : K ⊆ N.carrier := by
    rintro x ⟨z, hz, rfl⟩
    apply N.coordinate_map_mem
    refine ⟨mem_univ _, ?_, ?_⟩
    · simpa only [heN] using hcut.1.trans_le hz.2.1
    · simpa only [heN] using hz.2.2.trans_lt hL
  have hsplit : N.region (-L) 0 ⊆ N.region (-L) cut ∪ K := by
    intro x hx
    by_cases hs : (N.coordinate_inverse x).2 < cut
    · exact Or.inl ⟨hx.1, hx.2.1, hs⟩
    · refine Or.inr ⟨N.coordinate_inverse x, ⟨mem_univ _, not_lt.mp hs, hx.2.2.le⟩, ?_⟩
      exact N.coordinate_map_inverse hx.1
  have hclosure : closure (N.region (-L) 0) ⊆ closure (N.region (-L) cut) ∪ K := by
    simpa only [closure_union, hK.isClosed.closure_eq] using closure_mono hsplit
  have noNegative {x : M} (hx : x ∈ H.X) (hout : x ∉ N.carrier) :
      x ∉ closure (N.region (-L) 0) := by
    intro hc
    rcases hclosure hc with ht | hk
    · exact Set.disjoint_left.mp hprotected hx ht
    · exact hout (hKN hk)
  let U (C : BalancedNeckChain g H.epsilon) : Set M :=
    ⋃ i ∈ C.shape.active, (C.neck i).carrier
  let Quarters (C : BalancedNeckChain g H.epsilon) : Prop :=
    ∀ i ∈ C.shape.active, i + 1 ∈ C.shape.active →
      closure ((C.neck i).region (L / 2) L) ⊆ (C.neck (i + 1)).carrier ∧
        closure ((C.neck (i + 1)).region (-L) (-L / 2)) ⊆ (C.neck i).carrier
  let History (C : BalancedNeckChain g H.epsilon) : Prop :=
    ∀ i ∈ C.shape.active, i + 1 ∈ C.shape.active →
      (C.neck (i + 1)).center ∈ closure ((C.neck i).region 0 L) ∧
        (C.neck (i + 1)).center ∉ (⋃ j ∈ Icc (0 : ℤ) i, (C.neck j).carrier)
  let Good (b : ℤ) (C : BalancedNeckChain g H.epsilon) : Prop :=
    0 ≤ b ∧ C.shape = ChainShape.finite 0 b ∧ C.source_necks = H.necks ∧
      C.neck 0 = N ∧ (∀ i ∈ C.shape.active, (C.neck i).center ∈ H.X) ∧
      Quarters C ∧ History C
  let Stop (b : ℤ) (C : BalancedNeckChain g H.epsilon) : Prop :=
    (H.X ⊆ U C) ∨
      ∃ R ∈ H.necks, R.epsilon = H.epsilon ∧ R.center ∈ H.X ∧
        R.center ∈ closure ((C.neck b).region 0 L) ∧ R.center ∉ U C ∧
        ∀ c ∈ Ioo (-L) 0, ¬ Disjoint R.carrier (N.region (-L) c)
  by_contra hno
  have hnostop (b : ℤ) (C : BalancedNeckChain g H.epsilon)
      (hg : Good b C) : ¬ Stop b C := by
    intro hs
    rcases hg with ⟨hb, hshape, hsource, hstart, hcenters, hquarters, hhistory⟩
    exact hno ⟨b, C, hb, hshape, hsource, hstart, hcenters, hquarters, hhistory, hs⟩
  have hnext (b : ℤ) (C : BalancedNeckChain g H.epsilon) (hg : Good b C) :
      ∃ D : BalancedNeckChain g H.epsilon,
        Good (b + 1) D ∧ C.shape.active ⊆ D.shape.active ∧
          ∀ i ∈ C.shape.active, D.neck i = C.neck i := by
    have hstop := hnostop b C hg
    rcases hg with ⟨hb0, hshape, hsource, hstart, hcenters, hquarters, hhistory⟩
    have active (i : ℤ) : i ∈ C.shape.active ↔ 0 ≤ i ∧ i ≤ b := by
      rw [hshape]
      rfl
    have hb := (active b).mpr ⟨hb0, le_rfl⟩
    have hzero := (active 0).mpr ⟨le_rfl, hb0⟩
    have hmeet : (H.X ∩ U C).Nonempty := by
      refine ⟨N.center, hNX, mem_iUnion₂.mpr ⟨0, hzero, ?_⟩⟩
      rw [hstart]
      exact N.central_sphere_subset N.center_on_central_sphere
    obtain ⟨R, hRC, heR, hRX, hRout, hfront⟩ :=
      BalancedNeckChain.exists_exterior_end_center_of_not_subset
        H C hshape hquarters hsource hmeet (fun h => hstop (Or.inl h))
    have hRH : R ∈ H.necks := hsource ▸ hRC
    have hRpos : R.center ∈ closure ((C.neck b).region 0 L) := by
      rcases hfront with hneg | hpos
      · rw [hstart] at hneg
        apply False.elim
        apply noNegative hRX _ hneg
        intro hx
        exact hRout (mem_iUnion₂.mpr ⟨0, hzero, hstart.symm ▸ hx⟩)
      · exact hpos
    rcases forwardStep C hshape hef R hRC heR hRpos hRout with hext | hret
    · obtain ⟨Q, D, _hchoice, hsel, hshapeD, hsourceD, hneckD, hq1, hq2⟩ := hext
      have hQc : Q.center = R.center := hsel.2.2.1
      have hnew : D.neck (b + 1) = Q := by rw [hneckD, Function.update_self]
      have hold (i : ℤ) (hi : i ∈ C.shape.active) : D.neck i = C.neck i := by
        have hhi := ((active i).mp hi).2
        rw [hneckD, Function.update_of_ne (show i ≠ b + 1 by omega)]
      have activeD (i : ℤ) : i ∈ D.shape.active ↔ 0 ≤ i ∧ i ≤ b + 1 := by
        rw [hshapeD]
        rfl
      have hcentersD : ∀ i ∈ D.shape.active, (D.neck i).center ∈ H.X := by
        intro i hi
        have hbounds := (activeD i).mp hi
        by_cases hinew : i = b + 1
        · rw [hinew, hnew, hQc]
          exact hRX
        · have hio := (active i).mpr ⟨hbounds.1, by omega⟩
          rw [hold i hio]
          exact hcenters i hio
      have hquartersD : Quarters D := by
        intro i hi hi1
        have hbi := (activeD i).mp hi
        have hbi1 := (activeD (i + 1)).mp hi1
        by_cases hib : i = b
        · rw [hib, hnew, hold b hb]
          exact ⟨hq1, hq2⟩
        · have hio := (active i).mpr ⟨hbi.1, by omega⟩
          have hi1o := (active (i + 1)).mpr ⟨hbi1.1, by omega⟩
          rw [hold i hio, hold (i + 1) hi1o]
          exact hquarters i hio hi1o
      have hhistoryD : History D := by
        intro i hi hi1
        have hbi := (activeD i).mp hi
        have hbi1 := (activeD (i + 1)).mp hi1
        by_cases hib : i = b
        · subst i
          rw [hnew, hold b hb, hQc]
          refine ⟨hRpos, ?_⟩
          intro hx
          obtain ⟨j, hj, hjx⟩ := mem_iUnion₂.mp hx
          have hjo := (active j).mpr hj
          rw [hold j hjo] at hjx
          exact hRout (mem_iUnion₂.mpr ⟨j, hjo, hjx⟩)
        · have hio := (active i).mpr ⟨hbi.1, by omega⟩
          have hi1o := (active (i + 1)).mpr ⟨hbi1.1, by omega⟩
          rw [hold i hio, hold (i + 1) hi1o]
          refine ⟨(hhistory i hio hi1o).1, ?_⟩
          intro hx
          apply (hhistory i hio hi1o).2
          obtain ⟨j, hj, hjx⟩ := mem_iUnion₂.mp hx
          have hjo := (active j).mpr ⟨hj.1, hj.2.trans ((active i).mp hio).2⟩
          exact mem_iUnion₂.mpr ⟨j, hj, (hold j hjo) ▸ hjx⟩
      refine ⟨D, ⟨by omega, hshapeD, hsourceD.trans hsource,
        (hold 0 hzero).trans hstart, hcentersD, hquartersD, hhistoryD⟩, ?_, hold⟩
      intro i hi
      have hbi := (active i).mp hi
      exact (activeD i).mpr ⟨hbi.1, by omega⟩
    · apply False.elim
      apply hstop
      refine Or.inr ⟨R, hRH, heR, hRX, hRpos, hRout, ?_⟩
      simpa only [hstart] using hret
  have hsingle {i : ℤ} (hi : i ∈ (ChainShape.finite 0 0).active)
      (hi1 : i + 1 ∈ (ChainShape.finite 0 0).active) : False := by
    change 0 ≤ i ∧ i ≤ 0 at hi
    change 0 ≤ i + 1 ∧ i + 1 ≤ 0 at hi1
    omega
  let C0 : BalancedNeckChain g H.epsilon := {
    shape := .finite 0 0
    neck := fun _ => N
    source_necks := H.necks
    selected := fun _ _ => hNS
    active_nonempty := ⟨0, le_rfl, le_rfl⟩
    epsilon_eq := fun _ _ => heN
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
  have hC0 : Good 0 C0 :=
    ⟨le_rfl, rfl, rfl, rfl, fun _ _ => hNX,
      fun _ hi hi1 => (hsingle hi hi1).elim,
      fun _ hi hi1 => (hsingle hi hi1).elim⟩
  let State := {s : ℤ × BalancedNeckChain g H.epsilon // Good s.1 s.2}
  let Step (s t : State) : Prop :=
    t.1.1 = s.1.1 + 1 ∧ s.1.2.shape.active ⊆ t.1.2.shape.active ∧
      ∀ i ∈ s.1.2.shape.active, t.1.2.neck i = s.1.2.neck i
  have hround (s : State) : ∃ t : State, Step s t := by
    obtain ⟨D, hg, hsub, hretain⟩ := hnext s.1.1 s.1.2 s.2
    exact ⟨⟨(s.1.1 + 1, D), hg⟩, rfl, hsub, hretain⟩
  choose step hstep using hround
  let seed : State := ⟨(0, C0), hC0⟩
  let seq : ℕ → State := fun n => step^[n] seed
  have hsucc (n : ℕ) : seq (n + 1) = step (seq n) :=
    Function.iterate_succ_apply' step n seed
  have hseq (n : ℕ) : Step (seq n) (seq (n + 1)) := by
    rw [hsucc]
    exact hstep (seq n)
  let b : ℕ → ℤ := fun n => (seq n).1.1
  let C : ℕ → BalancedNeckChain g H.epsilon := fun n => (seq n).1.2
  have good (n : ℕ) : Good (b n) (C n) := (seq n).2
  have shape (n : ℕ) : (C n).shape = ChainShape.finite 0 (b n) := (good n).2.1
  have source (n : ℕ) : (C n).source_necks = H.necks := (good n).2.2.1
  have zero (n : ℕ) : (0 : ℤ) ∈ (C n).shape.active := by
    rw [shape n]
    exact ⟨le_rfl, (good n).1⟩
  have endpoint (n : ℕ) : b n = (n : ℤ) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      have hs : b (n + 1) = b n + 1 := (hseq n).1
      simpa only [Int.natCast_succ, ih] using hs
  have mono : Monotone (fun n => (C n).shape.active) :=
    monotone_nat_of_le_succ (fun n => (hseq n).2.1)
  obtain ⟨D, hactive, _hsource, hneck⟩ :=
    BalancedNeckChain.exists_coherent_finite_limit C (fun _ => 0) b shape
      (fun n => (hseq n).2.1) (fun n => (hseq n).2.2)
      (fun n => (source n).trans (source 0).symm)
  have hforward : D.shape.active = Ici (0 : ℤ) := by
    rw [hactive]
    ext i
    constructor
    · intro hi
      obtain ⟨n, hn⟩ := mem_iUnion.mp hi
      change 0 ≤ i
      exact
        (show 0 ≤ i ∧ i ≤ b n by
          simpa only [shape n, ChainShape.active, mem_Icc] using hn).1
    · intro hi
      refine mem_iUnion.mpr ⟨i.toNat, ?_⟩
      rw [shape, endpoint]
      exact ⟨hi, (Int.toNat_of_nonneg hi).ge⟩
  have hzero : (0 : ℤ) ∈ D.shape.active := by
    rw [hforward]
    exact (show (0 : ℤ) ≤ 0 from le_rfl)
  have hstart : D.neck 0 = N := (hneck 0 0 (zero 0)).trans (good 0).2.2.2.1
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
    exact (good n).2.2.2.2.2.1 i hn hn1
  have hincidence (i : ℤ) (hi : i ∈ D.shape.active)
      (hi1 : i + 1 ∈ D.shape.active) :
      (D.neck (i + 1)).center ∈ closure ((D.neck i).region 0 L) ∧
        (D.neck (i + 1)).center ∉ (D.neck i).carrier := by
    obtain ⟨n, hn, hn1⟩ := common hi hi1
    rw [hneck n i hn, hneck n (i + 1) hn1]
    have hist := (good n).2.2.2.2.2.2 i hn hn1
    refine ⟨hist.1, ?_⟩
    intro hx
    apply hist.2
    have hi0 : 0 ≤ i := by
      have hiI : 0 ≤ i ∧ i ≤ b n := by
        simpa only [shape n, ChainShape.active, mem_Icc] using hn
      exact hiI.1
    exact mem_iUnion₂.mpr ⟨i, ⟨hi0, le_rfl⟩, hx⟩
  have hsub : (ChainShape.forward 0).active ⊆ D.shape.active := by
    rw [hforward]
    exact subset_rfl
  let E : BalancedNeckChain g H.epsilon := {
    shape := .forward 0
    neck := D.neck
    source_necks := D.source_necks
    selected := fun i hi => D.selected i (hsub hi)
    active_nonempty := ⟨0, show (0 : ℤ) ≤ 0 from le_rfl⟩
    epsilon_eq := fun i hi => D.epsilon_eq i (hsub hi)
    centers_distinct := fun i hi j hj hij => D.centers_distinct (hsub hi) (hsub hj) hij
    adjacent_overlap := fun i hi hi1 => D.adjacent_overlap i (hsub hi) (hsub hi1)
    overlap_contains_quarters := fun i hi hi1 =>
      D.overlap_contains_quarters i (hsub hi) (hsub hi1)
    overlap_within_three_quarters := fun i hi hi1 =>
      D.overlap_within_three_quarters i (hsub hi) (hsub hi1)
    later_disjoint_negative_end := fun i hi j hj hij =>
      D.later_disjoint_negative_end i (hsub hi) j (hsub hj) hij
    balanced_center_distance := fun i hi hi1 =>
      D.balanced_center_distance i (hsub hi) (hsub hi1) }
  have hone : (1 : ℤ) ∈ D.shape.active := hforward.symm ▸ (by norm_num : (1 : ℤ) ∈ Ici 0)
  have sep := forwardEnd E 0 rfl hei (hquartersD 0 hzero hone)
    (fun i hi hi1 => Or.inl (hincidence i (hsub hi) (hsub hi1)))
  change (D.neck 0).IsSeparating at sep
  rw [hstart] at sep
  exact sep.2 hnon

end PoincareConjecture
