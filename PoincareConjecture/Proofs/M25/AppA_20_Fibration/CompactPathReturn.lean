import PoincareConjecture.Proofs.M25.AppA_20_Fibration.FiniteExtensionReturn
import PoincareConjecture.Proofs.M25.AppA_20_Fibration.ExteriorCenterCount










set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture



theorem NeckOnlyCover.exists_finite_deep_return_on_complementary_path :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T3Space M] {g : RiemannianMetric 3 M},
      ∀ (H : NeckOnlyCover g), H.epsilon ≤ epsilon0 →
      H.X = Set.univ →
      ∀ (N : EpsilonNeck g), N ∈ H.necks →
        let L := H.epsilon⁻¹
        ∀ (q : UnitTwoSphere)
          (γ : Path (N.coordinate_map (q, -L / 2))
            (N.coordinate_map (q, L / 2))),
          (∀ t, γ t ∉ N.central_sphere) →
          let K : Set M := Set.range γ ∪ {N.center}
          ∃ (b : ℕ) (C : BalancedNeckChain g H.epsilon)
            (R : EpsilonNeck g),
            let U : Set M := ⋃ i ∈ C.shape.active, (C.neck i).carrier
            C.shape = ChainShape.finite 0 (b : ℤ) ∧
            C.source_necks = H.necks ∧ C.neck 0 = N ∧
            (∀ i ∈ C.shape.active, i + 1 ∈ C.shape.active →
              closure ((C.neck i).region (L / 2) L) ⊆
                  (C.neck (i + 1)).carrier ∧
                closure ((C.neck (i + 1)).region (-L) (-L / 2)) ⊆
                  (C.neck i).carrier) ∧
            (∀ i ∈ C.shape.active, (C.neck i).center ∈ K) ∧
            (∀ i ∈ C.shape.active, ∀ j ∈ C.shape.active,
              i < j → (C.neck j).center ∉ (C.neck i).carrier) ∧
            (∀ i ∈ C.shape.active, i + 1 ∈ C.shape.active →
              (C.neck (i + 1)).center ∈
                closure ((C.neck i).region 0 L)) ∧
            R ∈ H.necks ∧ R.epsilon = H.epsilon ∧
            R.center ∈ Set.range γ ∧ R.center ∈ frontier U ∧
            R.center ∉ U ∧
            R.center ∈ closure ((C.neck (b : ℤ)).region 0 L) ∧
            (∀ c ∈ Set.Ioo (-L) 0,
              ¬ Disjoint R.carrier (N.region (-L) c)) := by
  obtain ⟨ec, hcpos, hccap, hcount⟩ :=
    NeckOnlyCover.exists_exterior_center_count_bound.{u}
  obtain ⟨ee, hepos, _, hextend⟩ :=
    BalancedNeckChain.exists_finite_forward_extension_or_deep_return.{u}
  refine ⟨min ec ee, lt_min hcpos hepos, (min_le_left _ _).trans hccap, ?_⟩
  intro M _ _ _ _ _ _ g H hsmall hwhole N hN
  dsimp only
  intro q γ hγ
  classical
  let L : ℝ := H.epsilon⁻¹
  let K : Set M := Set.range γ ∪ {N.center}
  let U (C : BalancedNeckChain g H.epsilon) : Set M :=
    ⋃ i ∈ C.shape.active, (C.neck i).carrier
  let Good (n : ℕ) (C : BalancedNeckChain g H.epsilon) : Prop :=
    C.shape = ChainShape.finite 0 (n : ℤ) ∧
      C.source_necks = H.necks ∧ C.neck 0 = N ∧
      (∀ i ∈ C.shape.active, i + 1 ∈ C.shape.active →
        closure ((C.neck i).region (L / 2) L) ⊆
            (C.neck (i + 1)).carrier ∧
          closure ((C.neck (i + 1)).region (-L) (-L / 2)) ⊆
            (C.neck i).carrier) ∧
      (∀ i ∈ C.shape.active, (C.neck i).center ∈ K) ∧
      (∀ i ∈ C.shape.active, ∀ j ∈ C.shape.active,
        i < j → (C.neck j).center ∉ (C.neck i).carrier) ∧
      (∀ i ∈ C.shape.active, i + 1 ∈ C.shape.active →
        (C.neck (i + 1)).center ∈ closure ((C.neck i).region 0 L))
  have hK : IsCompact K :=
    (isCompact_range γ.continuous).union isCompact_singleton
  have hKX : K ⊆ H.X := by
    intro x _
    rw [hwhole]
    exact mem_univ x
  obtain ⟨B, hB⟩ := hcount H (hsmall.trans (min_le_left _ _)) K hK hKX
  by_contra hnot
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
  have hseed : ∃ C, Good 0 C := by
    refine ⟨C0, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
    · intro _ hi hi1
      exact (hsingle hi hi1).elim
    · intro _ _
      exact Or.inr rfl
    · intro i hi j hj hij
      change 0 ≤ i ∧ i ≤ 0 at hi
      change 0 ≤ j ∧ j ≤ 0 at hj
      omega
    · intro _ hi hi1
      exact (hsingle hi hi1).elim
  have hnext (n : ℕ) (C : BalancedNeckChain g H.epsilon) (hgood : Good n C) :
      ∃ D, Good (n + 1) D := by
    rcases hgood with ⟨hshape, hsource, hstart, hquarters, hcenters,
      hhistory, hincidence⟩
    have hactive (i : ℤ) : i ∈ C.shape.active ↔ 0 ≤ i ∧ i ≤ (n : ℤ) := by
      rw [hshape]
      rfl
    have hnActive : (n : ℤ) ∈ C.shape.active :=
      (hactive _).mpr ⟨by omega, le_rfl⟩
    have hzeroActive : (0 : ℤ) ∈ C.shape.active :=
      (hactive _).mpr ⟨le_rfl, by omega⟩
    let γC : Path ((C.neck 0).coordinate_map (q, -L / 2))
        ((C.neck 0).coordinate_map (q, L / 2)) :=
      γ.cast (by rw [hstart]) (by rw [hstart])
    have hγC : ∀ t, γC t ∉ (C.neck 0).central_sphere := by
      intro t
      change γ t ∉ (C.neck 0).central_sphere
      rw [hstart]
      exact hγ t
    obtain ⟨N', hN'source, hN'epsilon, hpath, hfrontier, hout, hpositive⟩ :=
      H.exists_positive_frontier_center_on_complementary_path hwhole C hshape
        hsource hquarters q γC hγC
    change N'.center ∈ Set.range γ at hpath
    change N'.center ∈ frontier (U C) at hfrontier
    change N'.center ∉ U C at hout
    change N'.center ∈ closure ((C.neck (n : ℤ)).region 0 L) at hpositive
    rcases hextend C hshape (hsmall.trans (min_le_right _ _)) N' hN'source
        hN'epsilon hpositive hout with hextension | hreturn
    · obtain ⟨S, D, _, hsame, hDshape, hDsource, hDneck, hquarterPos,
        hquarterNeg⟩ := hextension
      have hSc : S.center = N'.center := hsame.2.2.1
      have hDactive (i : ℤ) :
          i ∈ D.shape.active ↔ 0 ≤ i ∧ i ≤ (n : ℤ) + 1 := by
        rw [hDshape]
        rfl
      have hDnew : D.neck ((n : ℤ) + 1) = S := by
        rw [hDneck, Function.update_self]
      have hDold (i : ℤ) (hi : i ∈ C.shape.active) : D.neck i = C.neck i := by
        have hile : i ≤ (n : ℤ) := ((hactive i).mp hi).2
        have hine : i ≠ (n : ℤ) + 1 := by omega
        rw [hDneck, Function.update_of_ne hine]
      have hDcenters : ∀ i ∈ D.shape.active, (D.neck i).center ∈ K := by
        intro i hi
        obtain ⟨hilo, hihi⟩ := (hDactive i).mp hi
        by_cases hinew : i = (n : ℤ) + 1
        · rw [hinew, hDnew, hSc]
          exact Or.inl hpath
        · have hiold : i ∈ C.shape.active := (hactive i).mpr ⟨hilo, by omega⟩
          rw [hDold i hiold]
          exact hcenters i hiold
      have hDhistory : ∀ i ∈ D.shape.active, ∀ j ∈ D.shape.active,
          i < j → (D.neck j).center ∉ (D.neck i).carrier := by
        intro i hi j hj hij
        obtain ⟨hilo, hihi⟩ := (hDactive i).mp hi
        obtain ⟨hjlo, hjhi⟩ := (hDactive j).mp hj
        by_cases hjnew : j = (n : ℤ) + 1
        · have hiold : i ∈ C.shape.active := (hactive i).mpr ⟨hilo, by omega⟩
          rw [hjnew, hDnew, hSc, hDold i hiold]
          intro hx
          exact hout (mem_iUnion₂.mpr ⟨i, hiold, hx⟩)
        · have hiold : i ∈ C.shape.active := (hactive i).mpr ⟨hilo, by omega⟩
          have hjold : j ∈ C.shape.active := (hactive j).mpr ⟨hjlo, by omega⟩
          rw [hDold i hiold, hDold j hjold]
          exact hhistory i hiold j hjold hij
      have hDquarters : ∀ i ∈ D.shape.active, i + 1 ∈ D.shape.active →
          closure ((D.neck i).region (L / 2) L) ⊆
              (D.neck (i + 1)).carrier ∧
            closure ((D.neck (i + 1)).region (-L) (-L / 2)) ⊆
              (D.neck i).carrier := by
        intro i hi hi1
        have hilo := ((hDactive i).mp hi).1
        have hi1hi := ((hDactive (i + 1)).mp hi1).2
        by_cases hin : i = (n : ℤ)
        · rw [hin, hDold (n : ℤ) hnActive, hDnew]
          exact ⟨hquarterPos, hquarterNeg⟩
        · have hiold : i ∈ C.shape.active := (hactive i).mpr ⟨hilo, by omega⟩
          have hi1old : i + 1 ∈ C.shape.active :=
            (hactive (i + 1)).mpr ⟨by omega, by omega⟩
          rw [hDold i hiold, hDold (i + 1) hi1old]
          exact hquarters i hiold hi1old
      have hDincidence : ∀ i ∈ D.shape.active, i + 1 ∈ D.shape.active →
          (D.neck (i + 1)).center ∈ closure ((D.neck i).region 0 L) := by
        intro i hi hi1
        have hilo := ((hDactive i).mp hi).1
        have hi1hi := ((hDactive (i + 1)).mp hi1).2
        by_cases hin : i = (n : ℤ)
        · rw [hin, hDold (n : ℤ) hnActive, hDnew, hSc]
          exact hpositive
        · have hiold : i ∈ C.shape.active := (hactive i).mpr ⟨hilo, by omega⟩
          have hi1old : i + 1 ∈ C.shape.active :=
            (hactive (i + 1)).mpr ⟨by omega, by omega⟩
          rw [hDold i hiold, hDold (i + 1) hi1old]
          exact hincidence i hiold hi1old
      refine ⟨D, ?_, hDsource.trans hsource, (hDold 0 hzeroActive).trans hstart,
        hDquarters, hDcenters, hDhistory, hDincidence⟩
      simpa only [Int.natCast_add_one] using hDshape
    · exfalso
      apply hnot
      refine ⟨n, C, N', hshape, hsource, hstart, hquarters, hcenters,
        hhistory, hincidence, ?_, hN'epsilon, hpath, hfrontier, hout, hpositive, ?_⟩
      · simpa only [hsource] using hN'source
      · simpa only [hstart] using hreturn
  have hstages : ∀ n : ℕ, ∃ C, Good n C := by
    intro n
    induction n with
    | zero => exact hseed
    | succ n ih =>
      obtain ⟨C, hC⟩ := ih
      exact hnext n C hC
  obtain ⟨C, hC⟩ := hstages B
  rcases hC with ⟨hshape, _hsource, _hstart, _hquarters, hcenters,
    hhistory, _hincidence⟩
  let F : Fin (B + 1) → EpsilonNeck g := fun i => C.neck (i.val : ℤ)
  have hactive (i : Fin (B + 1)) : (i.val : ℤ) ∈ C.shape.active := by
    rw [hshape]
    change 0 ≤ (i.val : ℤ) ∧ (i.val : ℤ) ≤ (B : ℤ)
    have hi := i.isLt
    constructor <;> omega
  have hFepsilon (i : Fin (B + 1)) : (F i).epsilon = H.epsilon :=
    C.epsilon_eq (i.val : ℤ) (hactive i)
  have hFcenters (i : Fin (B + 1)) : (F i).center ∈ K :=
    hcenters (i.val : ℤ) (hactive i)
  have hFhistory (i j : Fin (B + 1)) (hij : i < j) :
      (F j).center ∉ (F i).carrier := by
    exact hhistory (i.val : ℤ) (hactive i) (j.val : ℤ) (hactive j)
      (Int.ofNat_lt.mpr (show i.val < j.val from hij))
  have hbound : B + 1 ≤ B := hB (B + 1) F hFepsilon hFcenters hFhistory
  omega

end PoincareConjecture
