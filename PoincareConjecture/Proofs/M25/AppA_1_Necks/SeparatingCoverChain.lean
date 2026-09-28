import PoincareConjecture.Proofs.M25.AppA_1_Necks.FairFiniteExhaustion
import PoincareConjecture.Proofs.M25.AppA_1_Necks.CoherentChainLimit
import PoincareConjecture.Proofs.M25.AppA_1_Necks.MiddleFrontier











set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.NeckOnlyCover




theorem exists_covering_balanced_chain_of_separating :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T3Space M] {g : RiemannianMetric 3 M},
      ∀ (H : NeckOnlyCover g), H.epsilon ≤ epsilon0 →
      (∀ N ∈ H.necks, N.IsSeparating) →
      ∃ C : BalancedNeckChain g H.epsilon,
        C.source_necks = H.necks ∧
        H.X ⊆ (⋃ i ∈ C.shape.active, (C.neck i).carrier) ∧
        (∀ i ∈ C.shape.active, (C.neck i).center ∈ H.X) ∧
        (∀ i ∈ C.shape.active, i + 1 ∈ C.shape.active →
          closure ((C.neck i).region (H.epsilon⁻¹ / 2) H.epsilon⁻¹) ⊆
              (C.neck (i + 1)).carrier ∧
            closure ((C.neck (i + 1)).region
                (-H.epsilon⁻¹) (-H.epsilon⁻¹ / 2)) ⊆
              (C.neck i).carrier) ∧
        (∀ i ∈ C.shape.active, i + 1 ∈ C.shape.active →
          ((C.neck (i + 1)).center ∈
                closure ((C.neck i).region 0 H.epsilon⁻¹) ∧
              (C.neck (i + 1)).center ∉ (C.neck i).carrier) ∨
            ((C.neck i).center ∈
                closure ((C.neck (i + 1)).region (-H.epsilon⁻¹) 0) ∧
              (C.neck i).center ∉ (C.neck (i + 1)).carrier)) := by
  classical
  obtain ⟨epsilonE, hE, hEcap, hexhaustion⟩ := exists_fair_finite_exhaustion.{u}
  obtain ⟨epsilonF, hF, _, hfrontier⟩ :=
    BalancedNeckChain.exists_frontier_subset_exposed_end_closures.{u}
  refine ⟨min epsilonE epsilonF, lt_min hE hF, (min_le_left _ _).trans hEcap, ?_⟩
  intro M _ _ _ _ _ _ g H he hsep
  obtain ⟨a, b, C, _, _, hshape, hsource, ha, hb, hretain, hcenters,
    hquarters, hincidence, hnegative, hpositive⟩ :=
    hexhaustion H (he.trans (min_le_left _ _)) hsep
  have hactive (n : ℕ) (i : ℤ) : i ∈ (C n).shape.active ↔ a n ≤ i ∧ i ≤ b n := by
    rw [hshape n]
    rfl
  have hab (n : ℕ) : a n ≤ b n := by
    obtain ⟨i, hi⟩ := (C n).active_nonempty
    exact ((hactive n i).mp hi).1.trans ((hactive n i).mp hi).2
  have hmono : Monotone (fun n => (C n).shape.active) := by
    intro n m hnm i hi
    have hii := (hactive n i).mp hi
    exact (hactive m i).mpr ⟨(ha hnm).trans hii.1, hii.2.trans (hb hnm)⟩
  obtain ⟨D, hDactive, hDsource, hDneck⟩ :=
    BalancedNeckChain.exists_coherent_finite_limit C a b hshape
      (fun n => hmono (Nat.le_succ n)) hretain
      (fun n => (hsource n).trans (hsource 0).symm)
  have hsubactive (n : ℕ) : (C n).shape.active ⊆ D.shape.active := by
    intro i hi
    rw [hDactive]
    exact mem_iUnion.mpr ⟨n, hi⟩
  have hstage {i : ℤ} (hi : i ∈ D.shape.active) : ∃ n, i ∈ (C n).shape.active := by
    rw [hDactive] at hi
    exact mem_iUnion.mp hi
  have hcommon {i j : ℤ} (hi : i ∈ D.shape.active) (hj : j ∈ D.shape.active) :
      ∃ n, i ∈ (C n).shape.active ∧ j ∈ (C n).shape.active := by
    obtain ⟨n, hn⟩ := hstage hi
    obtain ⟨m, hm⟩ := hstage hj
    exact ⟨max n m, hmono (Nat.le_max_left _ _) hn, hmono (Nat.le_max_right _ _) hm⟩
  have hDcenters : ∀ i ∈ D.shape.active, (D.neck i).center ∈ H.X := by
    intro i hi
    obtain ⟨n, hn⟩ := hstage hi
    rw [hDneck n i hn]
    exact hcenters n i hn
  have hDquarters : ∀ i ∈ D.shape.active, i + 1 ∈ D.shape.active →
      closure ((D.neck i).region (H.epsilon⁻¹ / 2) H.epsilon⁻¹) ⊆
          (D.neck (i + 1)).carrier ∧
        closure ((D.neck (i + 1)).region (-H.epsilon⁻¹) (-H.epsilon⁻¹ / 2)) ⊆
          (D.neck i).carrier := by
    intro i hi hi1
    obtain ⟨n, hni, hni1⟩ := hcommon hi hi1
    rw [hDneck n i hni, hDneck n (i + 1) hni1]
    exact hquarters n i hni hni1
  have hDincidence : ∀ i ∈ D.shape.active, i + 1 ∈ D.shape.active →
      ((D.neck (i + 1)).center ∈ closure ((D.neck i).region 0 H.epsilon⁻¹) ∧
          (D.neck (i + 1)).center ∉ (D.neck i).carrier) ∨
        ((D.neck i).center ∈ closure ((D.neck (i + 1)).region (-H.epsilon⁻¹) 0) ∧
          (D.neck i).center ∉ (D.neck (i + 1)).carrier) := by
    intro i hi hi1
    obtain ⟨n, hni, hni1⟩ := hcommon hi hi1
    rw [hDneck n i hni, hDneck n (i + 1) hni1]
    exact hincidence n i hni hni1
  let U := ⋃ i ∈ D.shape.active, (D.neck i).carrier
  have hsubunion (n : ℕ) : (⋃ i ∈ (C n).shape.active, ((C n).neck i).carrier) ⊆ U := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
    exact mem_iUnion₂.mpr ⟨i, hsubactive n hi, by simpa only [hDneck n i hi] using hxi⟩
  have hleft (p : ℤ) (hp : p ∈ D.shape.active)
      (hbound : ∀ i ∈ D.shape.active, p ≤ i) :
      H.X ∩ closure ((D.neck p).region (-H.epsilon⁻¹) 0) ⊆ U := by
    obtain ⟨n, hn⟩ := hstage hp
    have haactive (k : ℕ) : a k ∈ (C k).shape.active :=
      (hactive k _).mpr ⟨le_rfl, hab k⟩
    have hane : a n = p := le_antisymm ((hactive n p).mp hn).1
      (hbound _ (hsubactive n (haactive n)))
    have hnext : a (n + 1) = a n := by
      apply le_antisymm (ha (Nat.le_succ n))
      rw [hane]
      exact hbound _ (hsubactive (n + 1) (haactive (n + 1)))
    have hneck : D.neck p = (C n).neck (a n) := by
      rw [hane]
      exact hDneck n p hn
    intro x hx
    exact hsubunion (n + 1) (hnegative n hnext (by simpa only [← hneck] using hx))
  have hright (p : ℤ) (hp : p ∈ D.shape.active)
      (hbound : ∀ i ∈ D.shape.active, i ≤ p) :
      H.X ∩ closure ((D.neck p).region 0 H.epsilon⁻¹) ⊆ U := by
    obtain ⟨n, hn⟩ := hstage hp
    have hbactive (k : ℕ) : b k ∈ (C k).shape.active :=
      (hactive k _).mpr ⟨hab k, le_rfl⟩
    have hbne : b n = p := le_antisymm (hbound _ (hsubactive n (hbactive n)))
      ((hactive n p).mp hn).2
    have hnext : b (n + 1) = b n := by
      apply le_antisymm ?_ (hb (Nat.le_succ n))
      rw [hbne]
      exact hbound _ (hsubactive (n + 1) (hbactive (n + 1)))
    have hneck : D.neck p = (C n).neck (b n) := by
      rw [hbne]
      exact hDneck n p hn
    intro x hx
    exact hsubunion (n + 1) (hpositive n hnext (by simpa only [← hneck] using hx))
  have hcover : H.X ⊆ U := by
    by_contra hnot
    have hopen : IsOpen U := isOpen_iUnion fun i => isOpen_iUnion fun _ => (D.neck i).carrier_open
    have hmeet : (H.X ∩ U).Nonempty := by
      obtain ⟨i, hi⟩ := D.active_nonempty
      exact ⟨(D.neck i).center, hDcenters i hi,
        mem_iUnion₂.mpr ⟨i, hi, (D.neck i).central_sphere_subset
          (D.neck i).center_on_central_sphere⟩⟩
    have hescape : ¬ closure U ∩ H.X ⊆ U := by
      intro hsub
      exact hnot (H.connected_X.2.subset_of_closure_inter_subset hopen hmeet hsub)
    obtain ⟨y, hy, hyout⟩ := Set.not_subset.mp hescape
    have hyfront : y ∈ frontier U := by
      rw [hopen.frontier_eq]
      exact ⟨hy.1, hyout⟩
    have hyend := hfrontier D (he.trans (min_le_right _ _)) hDincidence hyfront
    cases hs : D.shape with
    | finite p q =>
        have hpq : p ≤ q := by
          obtain ⟨i, hi⟩ := D.active_nonempty
          simp only [hs, ChainShape.active, mem_Icc] at hi
          exact hi.1.trans hi.2
        have hp : p ∈ D.shape.active := by
          simpa only [hs, ChainShape.active, mem_Icc] using And.intro le_rfl hpq
        have hq : q ∈ D.shape.active := by
          simpa only [hs, ChainShape.active, mem_Icc] using And.intro hpq le_rfl
        simp only [hs] at hyend
        rcases hyend with hyneg | hypos
        · exact hyout (hleft p hp (by
            intro i hi
            exact (show i ∈ Icc p q by simpa only [hs, ChainShape.active] using hi).1)
              ⟨hy.2, hyneg⟩)
        · exact hyout (hright q hq (by
            intro i hi
            exact (show i ∈ Icc p q by simpa only [hs, ChainShape.active] using hi).2)
              ⟨hy.2, hypos⟩)
    | forward p =>
        have hp : p ∈ D.shape.active := by
          simpa only [hs, ChainShape.active, mem_Ici] using (le_refl p)
        exact hyout (hleft p hp (by
          intro i hi
          simpa only [hs, ChainShape.active, mem_Ici] using hi)
            ⟨hy.2, by simpa only [hs] using hyend⟩)
    | backward q =>
        have hq : q ∈ D.shape.active := by
          simpa only [hs, ChainShape.active, mem_Iic] using (le_refl q)
        exact hyout (hright q hq (by
          intro i hi
          simpa only [hs, ChainShape.active, mem_Iic] using hi)
            ⟨hy.2, by simpa only [hs] using hyend⟩)
    | biInfinite => simp only [hs, mem_empty_iff_false] at hyend
  exact ⟨D, hDsource.trans (hsource 0), hcover, hDcenters, hDquarters, hDincidence⟩

end PoincareConjecture.NeckOnlyCover
