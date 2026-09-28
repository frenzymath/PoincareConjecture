import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.ConstantSpeedInitialApproximation
import PoincareConjecture.Proofs.M63.Mathlib.PeriodicSmoothApproximation
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.ContinuousMap.Compact

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u v w

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {ι : Type v} [Fintype ι] {Z : Type w} [TopologicalSpace Z]
  [CompactSpace Z] [Nonempty Z] {a b L0 : ℝ} [Fact (0 < L0)]

local notation "W" => EuclideanSpace ℝ ι
local notation "X" => C(AddCircle L0, W)
local notation "J" => ((X × X) × X) × ℝ

theorem exists_compact_smooth_initial_pool
    (F : RicciFlow n M (Icc a b)) {tau : ℝ} (htau : tau ∈ Icc a b)
    {e : M → W} (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e)
    {U : Set W} (hU : IsOpen U) (heU : range e ⊆ U) {ρ : W → M}
    (hρ : ContMDiffOn 𝓘(ℝ, W) (𝓡 n) ∞ ρ U) (hρe : ∀ p, ρ (e p) = p)
    (gamma : Z → ℝ → M)
    (hperiod : ∀ z, Function.Periodic (gamma z) L0)
    (hC2 : ∀ z, ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 2 (gamma z))
    (himm : ∀ z x, curveVelocity (n := n) (gamma z) x ≠ 0)
    (Q : Z → J) (hQ : Continuous Q)
    (hjets : ∀ z (x : ℝ),
      (Q z).1.1.1 (x : AddCircle L0) = e (gamma z x) ∧
      (Q z).1.1.2 (x : AddCircle L0) = deriv (fun y => e (gamma z y)) x ∧
      (Q z).1.2 (x : AddCircle L0) = deriv (deriv (fun y => e (gamma z y))) x)
    (hspeed : ∀ z x, curveSpeed F (fun y _ => gamma z y) tau x = (Q z).2)
    {O : Set J} (hO : IsOpen O) (hQO : range Q ⊆ O)
    (eps : ℕ → ℝ) (heps : ∀ j, 0 < eps j)
    (heps0 : Tendsto eps atTop (𝓝 0)) :
    ∃ P : ℕ → Finset J,
      (∀ j, (P j).Nonempty) ∧
      (∀ j p, p ∈ P j →
        let r : ℝ → W := fun x => p.1.1.1 (x : AddCircle L0)
        0 < p.2 ∧ ContDiff ℝ ∞ r ∧ Function.Periodic r L0 ∧
          (∀ x, r x ∈ U ∧ e (ρ (r x)) = r x) ∧
          (∀ x, mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (r x) (deriv r x) ≠ 0) ∧
          (∀ x : ℝ, HasDerivAt r (p.1.1.2 (x : AddCircle L0)) x ∧
            HasDerivAt (fun y : ℝ => p.1.1.2 (y : AddCircle L0))
              (p.1.2 (x : AddCircle L0)) x) ∧
          (∀ x, curveSpeed F (fun y _ => ρ (r y)) tau x = p.2)) ∧
      (∀ j p, p ∈ P j → ∃ z, dist p (Q z) < eps j) ∧
      (∀ j z, ∃ p, p ∈ P j ∧ dist p (Q z) < eps j) ∧
      IsCompact (range Q ∪ ⋃ j, (P j : Set J)) ∧
      (range Q ∪ ⋃ j, (P j : Set J)) ⊆ O := by
  classical
  let Good : J → Prop := fun p =>
    let r : ℝ → W := fun x => p.1.1.1 (x : AddCircle L0)
    0 < p.2 ∧ ContDiff ℝ ∞ r ∧ Function.Periodic r L0 ∧
      (∀ x, r x ∈ U ∧ e (ρ (r x)) = r x) ∧
      (∀ x, mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (r x) (deriv r x) ≠ 0) ∧
      (∀ x : ℝ, HasDerivAt r (p.1.1.2 (x : AddCircle L0)) x ∧
        HasDerivAt (fun y : ℝ => p.1.1.2 (y : AddCircle L0))
          (p.1.2 (x : AddCircle L0)) x) ∧
      (∀ x, curveSpeed F (fun y _ => ρ (r y)) tau x = p.2)
  have descend (f : ℝ → W) (hf : Continuous f) (hp : Function.Periodic f L0) :
      ∃ q : X, ∀ x : ℝ, q (x : AddCircle L0) = f x := by
    refine ⟨⟨hp.lift,
      (QuotientAddGroup.isQuotientMap_mk (AddSubgroup.zmultiples L0)).continuous_iff.mpr hf⟩,
      fun x => Function.Periodic.lift_coe hp x⟩
  have approximate (z : Z) (δ : ℝ) (hδ : 0 < δ) :
      ∃ p : J, Good p ∧ dist p (Q z) ≤ δ := by
    have hv : 0 < (Q z).2 := by
      rw [← hspeed z 0]
      exact Real.sqrt_pos.mpr ((F.metric tau).pos _ _ (himm z 0))
    obtain ⟨r, m, hm, hmdist, hr, hrp, hfix, hrimm, hrspeed, hnear⟩ :=
      exists_smooth_positive_constantSpeed_C2_approximation F he hU heU hρ hρe htau
        (Fact.out : 0 < L0) (hperiod z) (hC2 z) (himm z) hv (hspeed z) hδ
    have hr1 : ContDiff ℝ ∞ (deriv r) := (contDiff_infty_iff_deriv.mp hr).2
    have hr1p := hrp.deriv_of_differentiable (hr.differentiable (by simp))
    have hr2p := hr1p.deriv_of_differentiable (hr1.differentiable (by simp))
    obtain ⟨r0, h0⟩ := descend r hr.continuous hrp
    obtain ⟨r1, h1⟩ := descend (deriv r) hr1.continuous hr1p
    obtain ⟨r2, h2⟩ := descend (deriv (deriv r)) (hr1.continuous_deriv (by simp)) hr2p
    have hgood : Good (((r0, r1), r2), m) := by
      have hfixed0 := hfix
      have himm0 := hrimm
      have hspeed0 := hrspeed
      rw [← funext h0] at hfixed0 himm0 hspeed0
      dsimp only [Good]
      refine ⟨hm, ?_, ?_, hfixed0, himm0, ?_, hspeed0⟩
      · rw [funext h0]
        exact hr
      · rw [funext h0]
        exact hrp
      · intro x
        constructor
        · rw [funext h0, h1]
          exact ((hr.differentiable (by simp)) x).hasDerivAt
        · rw [funext h1, h2]
          exact ((hr1.differentiable (by simp)) x).hasDerivAt
    have hd0 : dist r0 (Q z).1.1.1 ≤ δ := by
      apply (ContinuousMap.dist_le hδ.le).mpr
      intro q
      obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
      rw [h0, (hjets z x).1, dist_eq_norm]
      exact (hnear x).1.le
    have hd1 : dist r1 (Q z).1.1.2 ≤ δ := by
      apply (ContinuousMap.dist_le hδ.le).mpr
      intro q
      obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
      rw [h1, (hjets z x).2.1, dist_eq_norm]
      exact (hnear x).2.1.le
    have hd2 : dist r2 (Q z).1.2 ≤ δ := by
      apply (ContinuousMap.dist_le hδ.le).mpr
      intro q
      obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
      rw [h2, (hjets z x).2.2, dist_eq_norm]
      exact (hnear x).2.2.le
    refine ⟨(((r0, r1), r2), m), hgood, ?_⟩
    simp only [Prod.dist_eq]
    exact max_le (max_le (max_le hd0 hd1) hd2)
      (by simpa only [Real.dist_eq] using hmdist.le)
  let K : Set J := range Q
  have hK : IsCompact K := isCompact_range hQ
  have hKne : K.Nonempty := range_nonempty Q
  obtain ⟨eta, heta, hetaO⟩ := hK.exists_thickening_subset_open hO hQO
  let delta : ℕ → ℝ := fun j => min (eps j / 4) (eta / 4)
  have hdpos (j : ℕ) : 0 < delta j :=
    lt_min (div_pos (heps j) (by norm_num)) (div_pos heta (by norm_num))
  have hdeps (j : ℕ) : 2 * delta j < eps j := by
    have h := min_le_left (eps j / 4) (eta / 4)
    dsimp only [delta]
    linarith [heps j]
  have hdeta (j : ℕ) : delta j < eta := by
    have h := min_le_right (eps j / 4) (eta / 4)
    dsimp only [delta]
    linarith
  have level (j : ℕ) : ∃ P : Finset J,
      P.Nonempty ∧ (∀ p ∈ P, Good p) ∧
      (∀ p ∈ P, ∃ z, dist p (Q z) ≤ delta j) ∧
      ∀ z, ∃ p ∈ P, dist p (Q z) < 2 * delta j := by
    obtain ⟨T, hTK, hTfin, hcover⟩ :=
      Metric.finite_approx_of_totallyBounded hK.totallyBounded (delta j) (hdpos j)
    let : Fintype T := hTfin.fintype
    have centers (q : T) : ∃ z, Q z = (q : J) := hTK q.property
    choose z hz using centers
    have samples (q : T) : ∃ p : J, Good p ∧ dist p (q : J) ≤ delta j := by
      obtain ⟨p, hp, hd⟩ := approximate (z q) (delta j) (hdpos j)
      exact ⟨p, hp, by simpa only [hz q] using hd⟩
    choose sample hsample hsampleDist using samples
    let P : Finset J := Finset.univ.image sample
    have hmem (q : T) : sample q ∈ P := Finset.mem_image.mpr ⟨q, Finset.mem_univ _, rfl⟩
    obtain ⟨q, hq, _hqnear⟩ := mem_iUnion₂.mp (hcover hKne.choose_spec)
    refine ⟨P, ⟨sample ⟨q, hq⟩, hmem _⟩, ?_, ?_, ?_⟩
    · intro p hp
      obtain ⟨q, _hq, rfl⟩ := Finset.mem_image.mp hp
      exact hsample q
    · intro p hp
      obtain ⟨q, _hq, rfl⟩ := Finset.mem_image.mp hp
      exact ⟨z q, by simpa only [hz q] using hsampleDist q⟩
    · intro w
      obtain ⟨q, hq, hnear⟩ := mem_iUnion₂.mp (hcover (mem_range_self w))
      refine ⟨sample ⟨q, hq⟩, hmem _, ?_⟩
      have hnear' : dist q (Q w) < delta j := (dist_comm _ _).trans_lt hnear
      calc
        dist (sample ⟨q, hq⟩) (Q w) ≤
            dist (sample ⟨q, hq⟩) q + dist q (Q w) := dist_triangle _ _ _
        _ < delta j + delta j := add_lt_add_of_le_of_lt (hsampleDist _) hnear'
        _ = 2 * delta j := by ring
  choose P hPne hPgood hPcenter hPcover using level
  have hnear (j : ℕ) (p : J) (hp : p ∈ P j) : ∃ z, dist p (Q z) < eps j := by
    obtain ⟨z, hz⟩ := hPcenter j p hp
    exact ⟨z, hz.trans_lt (by linarith [hdeps j, hdpos j])⟩
  have hcover (j : ℕ) (z : Z) : ∃ p, p ∈ P j ∧ dist p (Q z) < eps j := by
    obtain ⟨p, hp, hd⟩ := hPcover j z
    exact ⟨p, hp, hd.trans (hdeps j)⟩
  let Kplus : Set J := K ∪ ⋃ j, (P j : Set J)
  have hguard : Kplus ⊆ O := by
    intro p hp
    rcases hp with hp | hp
    · exact hQO hp
    · obtain ⟨j, hj⟩ := mem_iUnion.mp hp
      obtain ⟨z, hz⟩ := hPcenter j p hj
      exact hetaO (Metric.mem_thickening_iff.mpr
        ⟨Q z, mem_range_self _, hz.trans_lt (hdeta j)⟩)
  let finitePrefix : ℕ → Set J := fun N => ⋃ j ∈ (Finset.range N : Set ℕ), (P j : Set J)
  have hprefixFinite (N : ℕ) : (finitePrefix N).Finite :=
    (Finset.finite_toSet _).biUnion (fun j _ => (P j).finite_toSet)
  have hprefixMem (N j : ℕ) (hj : j < N) {p : J} (hp : p ∈ P j) : p ∈ finitePrefix N :=
    mem_iUnion₂.mpr ⟨j, Finset.mem_range.mpr hj, hp⟩
  have hprefixSub (N : ℕ) : finitePrefix N ⊆ Kplus := by
    intro p hp
    obtain ⟨j, _hj, hp⟩ := mem_iUnion₂.mp hp
    exact Or.inr (mem_iUnion.mpr ⟨j, hp⟩)
  have hsmall (ε : ℝ) (hε : 0 < ε) : ∃ N, ∀ j ≥ N, eps j < ε :=
    eventually_atTop.mp (heps0.eventually (gt_mem_nhds hε))
  have htotal : TotallyBounded Kplus := by
    apply Metric.totallyBounded_iff.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := hsmall (ε / 3) (by positivity)
    obtain ⟨T, _hTK, hTfin, hTcover⟩ :=
      Metric.finite_approx_of_totallyBounded hK.totallyBounded (ε / 3) (by positivity)
    refine ⟨T ∪ finitePrefix N, hTfin.union (hprefixFinite N), ?_⟩
    intro p hp
    rcases hp with hp | hp
    · obtain ⟨q, hq, hqdist⟩ := mem_iUnion₂.mp (hTcover hp)
      refine mem_iUnion₂.mpr ⟨q, Or.inl hq, ?_⟩
      exact (Metric.mem_ball.mp hqdist).trans (by linarith)
    · obtain ⟨j, hj⟩ := mem_iUnion.mp hp
      by_cases hjN : j < N
      · exact mem_iUnion₂.mpr
          ⟨p, Or.inr (hprefixMem N j hjN hj), Metric.mem_ball_self hε⟩
      · obtain ⟨z, hz⟩ := hnear j p hj
        obtain ⟨q, hq, hqdist⟩ := mem_iUnion₂.mp (hTcover (mem_range_self z))
        refine mem_iUnion₂.mpr ⟨q, Or.inl hq, ?_⟩
        have hsum := (dist_triangle p (Q z) q).trans_lt (add_lt_add hz hqdist)
        exact hsum.trans (by linarith [hN j (Nat.le_of_not_gt hjN)])
  have hclosed : IsClosed Kplus := by
    apply isOpen_compl_iff.mp
    apply Metric.isOpen_iff.mpr
    intro y hy
    have hyK : y ∈ Kᶜ := fun h => hy (Or.inl h)
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hK.isClosed.isOpen_compl y hyK
    obtain ⟨N, hN⟩ := hsmall (ε / 3) (by positivity)
    have hyPrefix : y ∈ (finitePrefix N)ᶜ := fun h => hy (hprefixSub N h)
    obtain ⟨η, hη, hballPrefix⟩ :=
      Metric.isOpen_iff.mp (hprefixFinite N).isClosed.isOpen_compl y hyPrefix
    refine ⟨min (ε / 3) η, lt_min (by positivity) hη, ?_⟩
    intro p hp hpk
    have hpε : dist p y < ε / 3 := hp.trans_le (min_le_left _ _)
    have hpη : dist p y < η := hp.trans_le (min_le_right _ _)
    rcases hpk with hpk | hpk
    · exact hball (hpε.trans (by linarith)) hpk
    · obtain ⟨j, hj⟩ := mem_iUnion.mp hpk
      by_cases hjN : j < N
      · exact hballPrefix hpη (hprefixMem N j hjN hj)
      · obtain ⟨z, hz⟩ := hnear j p hj
        have hz' : dist (Q z) p < ε / 3 := by
          rw [dist_comm]
          exact hz.trans (hN j (Nat.le_of_not_gt hjN))
        have hd : dist (Q z) y < ε :=
          ((dist_triangle _ p _).trans_lt (add_lt_add hz' hpε)).trans (by linarith)
        exact hball hd (mem_range_self z)
  exact ⟨P, hPne, hPgood, hnear, hcover, htotal.isCompact_of_isClosed hclosed, hguard⟩

end PoincareConjecture.M63
