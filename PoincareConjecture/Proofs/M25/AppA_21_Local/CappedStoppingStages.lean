import PoincareConjecture.Proofs.M25.AppA_21_Local.CappedChainExtension
import PoincareConjecture.Proofs.M25.AppA_21_Local.CappedChainFrontier
import PoincareConjecture.Proofs.M25.AppA_21_Local.CapEndSeparation
import PoincareConjecture.Definitions.Ch09.NeckCapTopology
import Mathlib.Logic.Function.Iterate
import Mathlib.Order.Monotone.Basic

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

theorem ConnectedNeckCapCover.exists_finite_capped_stopping_stages :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T3Space M] {g : RiemannianMetric 3 M},
      ∀ (H : ConnectedNeckCapCover g), H.epsilon ≤ epsilon0 →
      ∀ (C : CapCertificate g), C ∈ H.caps →
      (H.X ∩ C.carrier).Nonempty →
      let U (D : BalancedNeckChain g C.epsilon) : Set M :=
        ⋃ i ∈ D.shape.active, (D.neck i).carrier
      let Stop (b : ℤ) (D : BalancedNeckChain g C.epsilon) : Prop :=
        H.X ⊆ C.carrier ∪ U D ∨
          ∃ C1 ∈ H.caps, ∃ y ∈ H.X,
            y ∈ C1.core ∧ y ∉ C.carrier ∪ U D ∧
              y ∈ closure ((D.neck b).region 0 C.epsilon⁻¹)
      ∃ (b : ℕ → ℤ) (D : ℕ → BalancedNeckChain g C.epsilon),
        b 0 = 0 ∧ (D 0).neck = (fun _ : ℤ => C.end_neck) ∧
        (∀ n, (D n).shape = ChainShape.finite 0 (b n)) ∧
        (∀ n, (D n).source_necks = insert C.end_neck H.necks) ∧
        Monotone b ∧
        (∀ n, ∀ i ∈ (D n).shape.active,
          (D (n + 1)).neck i = (D n).neck i) ∧
        (∀ n, (D n).neck 0 = C.end_neck) ∧
        (∀ n, ∀ i ∈ (D n).shape.active, ((D n).neck i).IsSeparating) ∧
        (∀ n, ∀ i ∈ (D n).shape.active, 0 < i →
          ((D n).neck i).center ∈ H.X \ C.carrier) ∧
        (∀ n, ∀ i ∈ (D n).shape.active, i + 1 ∈ (D n).shape.active →
          closure (((D n).neck i).region (C.epsilon⁻¹ / 2) C.epsilon⁻¹) ⊆
              ((D n).neck (i + 1)).carrier ∧
            closure (((D n).neck (i + 1)).region
                (-C.epsilon⁻¹) (-C.epsilon⁻¹ / 2)) ⊆ ((D n).neck i).carrier) ∧
        (∀ n, ∀ i ∈ (D n).shape.active, i + 1 ∈ (D n).shape.active →
          ((D n).neck (i + 1)).center ∈
              closure (((D n).neck i).region 0 C.epsilon⁻¹) ∧
            ((D n).neck (i + 1)).center ∉ ((D n).neck i).carrier) ∧
        (∀ n, Stop (b n) (D n) → b (n + 1) = b n ∧ D (n + 1) = D n) ∧
        (∀ n, ¬ Stop (b n) (D n) → b (n + 1) = b n + 1) := by
  classical
  obtain ⟨epsilon0, hpos, hcap, hextend⟩ :=
    CapCertificate.exists_finite_outward_extension.{u}
  refine ⟨epsilon0, hpos, hcap, ?_⟩
  intro M _ _ _ _ _ _ g H he C hC hmeet
  dsimp only
  have heC : C.epsilon ≤ epsilon0 := by
    rw [H.cap_epsilon C hC]
    exact he
  let S : Set (EpsilonNeck g) := insert C.end_neck H.necks
  have hinitial : C.end_neck ∈ S := mem_insert _ _
  have hepsilon : ∀ N ∈ S, N.epsilon = C.epsilon := by
    intro N hN
    rcases mem_insert_iff.mp hN with rfl | hN
    · exact C.end_neck_epsilon
    · exact (H.neck_epsilon N hN).trans (H.cap_epsilon C hC).symm
  let U (D : BalancedNeckChain g C.epsilon) : Set M :=
    ⋃ i ∈ D.shape.active, (D.neck i).carrier
  let Stop (b : ℤ) (D : BalancedNeckChain g C.epsilon) : Prop :=
    H.X ⊆ C.carrier ∪ U D ∨
      ∃ C1 ∈ H.caps, ∃ y ∈ H.X,
        y ∈ C1.core ∧ y ∉ C.carrier ∪ U D ∧
          y ∈ closure ((D.neck b).region 0 C.epsilon⁻¹)
  let Good (b : ℤ) (D : BalancedNeckChain g C.epsilon) : Prop :=
    0 ≤ b ∧ D.shape = ChainShape.finite 0 b ∧ D.source_necks = S ∧
      D.neck 0 = C.end_neck ∧
      (∀ i ∈ D.shape.active, (D.neck i).IsSeparating) ∧
      (∀ i ∈ D.shape.active, 0 < i → (D.neck i).center ∈ H.X \ C.carrier) ∧
      (∀ i ∈ D.shape.active, i + 1 ∈ D.shape.active →
        closure ((D.neck i).region (C.epsilon⁻¹ / 2) C.epsilon⁻¹) ⊆
            (D.neck (i + 1)).carrier ∧
          closure ((D.neck (i + 1)).region
              (-C.epsilon⁻¹) (-C.epsilon⁻¹ / 2)) ⊆ (D.neck i).carrier) ∧
      (∀ i ∈ D.shape.active, i + 1 ∈ D.shape.active →
        (D.neck (i + 1)).center ∈ closure ((D.neck i).region 0 C.epsilon⁻¹) ∧
          (D.neck (i + 1)).center ∉ (D.neck i).carrier)
  have hnext (b : ℤ) (D : BalancedNeckChain g C.epsilon) (hgood : Good b D) :
      ∃ (b' : ℤ) (E : BalancedNeckChain g C.epsilon),
        Good b' E ∧ b ≤ b' ∧
          (∀ i ∈ D.shape.active, E.neck i = D.neck i) ∧
          (Stop b D → b' = b ∧ E = D) ∧
          (¬ Stop b D → b' = b + 1) := by
    by_cases hstop : Stop b D
    · refine ⟨b, D, hgood, le_rfl, fun _ _ => rfl, fun _ => ⟨rfl, rfl⟩, ?_⟩
      intro hnot
      exact False.elim (hnot hstop)
    · rcases hgood with ⟨hb, hshape, hsource, hstart, hsep, hcenters,
        hquarters, hincidence⟩
      have hcovered : ¬ H.X ⊆ C.carrier ∪ U D := fun h => hstop (Or.inl h)
      have hmeetStage : (H.X ∩ (C.carrier ∪ U D)).Nonempty := by
        obtain ⟨x, hxX, hxC⟩ := hmeet
        exact ⟨x, hxX, Or.inl hxC⟩
      obtain ⟨y, hyX, hyout, hyfront⟩ :=
        C.exists_positive_chain_frontier D hshape hstart hquarters
          H.connected_X.isPreconnected hmeetStage hcovered
      have hneck : ∃ N ∈ H.necks, N.center = y := by
        rcases H.pointwise_cover y hyX with hneck | ⟨C1, hC1, hycore⟩
        · exact hneck
        · exact False.elim (hstop (Or.inr ⟨C1, hC1, y, hyX, hycore, hyout, hyfront⟩))
      obtain ⟨N, hN, hNc⟩ := hneck
      have hNS : N ∈ S := mem_insert_of_mem _ hN
      obtain ⟨R, E, _, hselected, hEshape, hEsource, hEneck, hEstart,
        hEsep, _, hEquarters⟩ :=
        hextend C D hshape heC hstart hsep
          (fun i hi hi0 => (hcenters i hi hi0).2) hquarters N
          (by rw [hsource]; exact hNS) (hepsilon N hNS)
          (by simpa only [hNc] using hyfront)
          (by simpa only [hNc] using hyout)
      have hactive (i : ℤ) : i ∈ D.shape.active ↔ 0 ≤ i ∧ i ≤ b := by
        rw [hshape]
        rfl
      have hbActive : b ∈ D.shape.active := (hactive b).mpr ⟨hb, le_rfl⟩
      have hRc : R.center = y := hselected.2.2.1.trans hNc
      have hEnew : E.neck (b + 1) = R := by rw [hEneck, Function.update_self]
      have hEold (i : ℤ) (hi : i ∈ D.shape.active) : E.neck i = D.neck i := by
        have hib : i ≤ b := ((hactive i).mp hi).2
        have hine : i ≠ b + 1 := by omega
        rw [hEneck, Function.update_of_ne hine]
      have hEcenters : ∀ i ∈ E.shape.active, 0 < i →
          (E.neck i).center ∈ H.X \ C.carrier := by
        intro i hi hi0
        rw [hEshape] at hi
        change 0 ≤ i ∧ i ≤ b + 1 at hi
        rcases hi with ⟨hilo, hihi⟩
        by_cases hinew : i = b + 1
        · rw [hinew, hEnew, hRc]
          exact ⟨hyX, fun hx => hyout (Or.inl hx)⟩
        · have hio : i ∈ D.shape.active := (hactive i).mpr ⟨hilo, by omega⟩
          rw [hEold i hio]
          exact hcenters i hio hi0
      have hEincidence : ∀ i ∈ E.shape.active, i + 1 ∈ E.shape.active →
          (E.neck (i + 1)).center ∈ closure ((E.neck i).region 0 C.epsilon⁻¹) ∧
            (E.neck (i + 1)).center ∉ (E.neck i).carrier := by
        intro i hi hi1
        rw [hEshape] at hi hi1
        change 0 ≤ i ∧ i ≤ b + 1 at hi
        change 0 ≤ i + 1 ∧ i + 1 ≤ b + 1 at hi1
        rcases hi with ⟨hilo, hihi⟩
        rcases hi1 with ⟨hi1lo, hi1hi⟩
        by_cases hib : i = b
        · rw [hib, hEnew, hEold b hbActive, hRc]
          exact ⟨hyfront,
            fun hx => hyout (Or.inr (mem_iUnion₂.mpr ⟨b, hbActive, hx⟩))⟩
        · have hio : i ∈ D.shape.active := (hactive i).mpr ⟨hilo, by omega⟩
          have hi1o : i + 1 ∈ D.shape.active :=
            (hactive (i + 1)).mpr ⟨hi1lo, by omega⟩
          rw [hEold i hio, hEold (i + 1) hi1o]
          exact hincidence i hio hi1o
      have hEgood : Good (b + 1) E :=
        ⟨by omega, hEshape, hEsource.trans hsource, hEstart, hEsep,
          hEcenters, hEquarters, hEincidence⟩
      refine ⟨b + 1, E, hEgood, by omega, hEold, ?_, fun _ => rfl⟩
      intro hyes
      exact False.elim (hstop hyes)
  let State := {s : ℤ × BalancedNeckChain g C.epsilon // Good s.1 s.2}
  let Step (s t : State) : Prop :=
    s.1.1 ≤ t.1.1 ∧
      (∀ i ∈ s.1.2.shape.active, t.1.2.neck i = s.1.2.neck i) ∧
      (Stop s.1.1 s.1.2 → t.1.1 = s.1.1 ∧ t.1.2 = s.1.2) ∧
      (¬ Stop s.1.1 s.1.2 → t.1.1 = s.1.1 + 1)
  have hround (s : State) : ∃ t : State, Step s t := by
    obtain ⟨b', E, hgood, hle, hretain, hfixed, hgrow⟩ :=
      hnext s.1.1 s.1.2 s.2
    exact ⟨⟨(b', E), hgood⟩, hle, hretain, hfixed, hgrow⟩
  have hsingle {i : ℤ} (hi : i ∈ (ChainShape.finite 0 0).active)
      (hi1 : i + 1 ∈ (ChainShape.finite 0 0).active) : False := by
    change 0 ≤ i ∧ i ≤ 0 at hi
    change 0 ≤ i + 1 ∧ i + 1 ≤ 0 at hi1
    omega
  let D0 : BalancedNeckChain g C.epsilon := {
    shape := .finite 0 0
    neck := fun _ => C.end_neck
    source_necks := S
    selected := by
      intro _ _
      refine ⟨C.end_neck, hinitial, rfl, rfl, rfl, rfl, rfl, 1, Or.inl rfl, ?_⟩
      intro z _
      simp only [one_mul]
    active_nonempty := ⟨0, le_rfl, le_rfl⟩
    epsilon_eq := fun _ _ => C.end_neck_epsilon
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
  have hD0 : Good 0 D0 := by
    refine ⟨le_rfl, rfl, rfl, rfl, fun _ _ => C.end_neck_isSeparating, ?_, ?_, ?_⟩
    · intro i hi hi0
      change 0 ≤ i ∧ i ≤ 0 at hi
      omega
    · intro _ hi hi1
      exact (hsingle hi hi1).elim
    · intro _ hi hi1
      exact (hsingle hi hi1).elim
  let seed : State := ⟨(0, D0), hD0⟩
  choose step hstep using hround
  let seq : ℕ → State := fun n => step^[n] seed
  have hsucc (n : ℕ) : seq (n + 1) = step (seq n) :=
    Function.iterate_succ_apply' step n seed
  have hseq (n : ℕ) : Step (seq n) (seq (n + 1)) := by
    rw [hsucc]
    exact hstep (seq n)
  exact ⟨fun n => (seq n).1.1, fun n => (seq n).1.2, rfl, rfl,
    fun n => (seq n).2.2.1, fun n => (seq n).2.2.2.1,
    monotone_nat_of_le_succ (fun n => (hseq n).1),
    fun n => (hseq n).2.1, fun n => (seq n).2.2.2.2.1,
    fun n => (seq n).2.2.2.2.2.1, fun n => (seq n).2.2.2.2.2.2.1,
    fun n => (seq n).2.2.2.2.2.2.2.1, fun n => (seq n).2.2.2.2.2.2.2.2,
    fun n => (hseq n).2.2.1, fun n => (hseq n).2.2.2⟩

end PoincareConjecture
