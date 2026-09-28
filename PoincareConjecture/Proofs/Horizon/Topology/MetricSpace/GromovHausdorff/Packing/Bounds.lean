import PoincareConjecture.Proofs.Horizon.Topology.MetricSpace.GromovHausdorff.Basic

open Set Filter Topology

namespace Poincare.GromovHausdorff

structure PackingWitness {X : Type*} [MetricSpace X]
    (x : X) (δ R : ℝ) (n : ℕ) where
  center : Fin n → X
  center_mem : ∀ i, center i ∈ Metric.ball x R
  ball_subset : ∀ i, Metric.ball (center i) δ ⊆ Metric.ball x R
  pairwise_disjoint :
    Pairwise (fun i j => Disjoint (Metric.ball (center i) δ)
      (Metric.ball (center j) δ))

theorem PackingWitness.center_separated {X : Type*} [MetricSpace X]
    {x : X} {δ R : ℝ} {n : ℕ} (w : PackingWitness x δ R n)
    (hδ : 0 < δ) :
    ∀ ⦃i j : Fin n⦄, i ≠ j → δ ≤ dist (w.center i) (w.center j) := by
  intro i j hij
  by_contra hnot
  have hlt : dist (w.center i) (w.center j) < δ := lt_of_not_ge hnot
  have hi : w.center j ∈ Metric.ball (w.center i) δ := by
    rw [Metric.mem_ball]
    simpa [dist_comm] using hlt
  have hj : w.center j ∈ Metric.ball (w.center j) δ :=
    Metric.mem_ball_self hδ
  exact (Set.disjoint_left.mp (w.pairwise_disjoint hij)) hi hj

theorem PackingWitness.center_injective {X : Type*} [MetricSpace X]
    {x : X} {δ R : ℝ} {n : ℕ} (w : PackingWitness x δ R n)
    (hδ : 0 < δ) : Function.Injective w.center := by
  intro i j hij
  by_contra hne
  have hsep := w.center_separated hδ hne
  exact (not_le_of_gt hδ) (by simpa [hij] using hsep)

def packingWitness_of_separated_centers {X : Type*} [MetricSpace X]
    (x : X) {δ R : ℝ} (hδ : 0 < δ) {n : ℕ} (c : Fin n → X)
    (hc : ∀ i, dist (c i) x + δ ≤ R)
    (hsep : ∀ ⦃i j : Fin n⦄, i ≠ j → 2 * δ ≤ dist (c i) (c j)) :
    PackingWitness x δ R n := by
  refine ⟨c, ?_, ?_, ?_⟩
  · intro i
    rw [Metric.mem_ball]
    exact lt_of_lt_of_le (lt_add_of_pos_right _ hδ) (hc i)
  · intro i z hz
    rw [Metric.mem_ball] at hz ⊢
    calc
      dist z x ≤ dist z (c i) + dist (c i) x := dist_triangle _ _ _
      _ < δ + dist (c i) x := add_lt_add_left hz _
      _ = dist (c i) x + δ := by ring
      _ ≤ R := hc i
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro z hzi hzj
    have hi : dist (c i) z < δ := by
      simpa [dist_comm] using Metric.mem_ball.mp hzi
    have hj : dist z (c j) < δ := Metric.mem_ball.mp hzj
    have hlt : dist (c i) (c j) < 2 * δ := by
      calc
        dist (c i) (c j) ≤ dist (c i) z + dist z (c j) := dist_triangle _ _ _
        _ < δ + δ := add_lt_add hi hj
        _ = 2 * δ := by ring
    exact (not_lt_of_ge (hsep hij)) hlt

def packingAdmissible {X : Type*} [MetricSpace X]
    (x : X) (δ R : ℝ) : Set ℕ :=
  {n | Nonempty (PackingWitness x δ R n)}

theorem exists_packing_bound_of_totallyBounded_closedBall
    {X : Type*} [MetricSpace X] (x : X) {δ R : ℝ} (hδ : 0 < δ)
    (hball : TotallyBounded (Metric.closedBall x R)) :
    ∃ N : ℕ, ∀ n, n ∈ packingAdmissible x δ R → n ≤ N := by
  obtain ⟨t, htfin, hcover⟩ :=
    (Metric.totallyBounded_iff.mp hball) (δ / 2) (by linarith)
  letI : Fintype t := htfin.fintype
  refine ⟨Fintype.card t, ?_⟩
  intro n hn
  rcases hn with ⟨w⟩
  have hcenter_closed : ∀ i, w.center i ∈ Metric.closedBall x R := by
    intro i
    exact Metric.mem_closedBall.mpr
      (le_of_lt (Metric.mem_ball.mp (w.center_mem i)))
  have hcover_i : ∀ i : Fin n, ∃ y : t,
      w.center i ∈ Metric.ball (y : X) (δ / 2) := by
    intro i
    rcases Set.mem_iUnion₂.mp (hcover (hcenter_closed i)) with ⟨y, hy, hiy⟩
    exact ⟨⟨y, hy⟩, hiy⟩
  let choose : Fin n → t := fun i => (hcover_i i).choose
  have choose_spec (i : Fin n) :
      w.center i ∈ Metric.ball (choose i : X) (δ / 2) :=
    (hcover_i i).choose_spec
  have hchoose_inj : Function.Injective choose := by
    intro i j hij
    by_contra hne
    have hsep := w.center_separated hδ hne
    have hi : dist (w.center i) (choose i : X) < δ / 2 :=
      Metric.mem_ball.mp (choose_spec i)
    have hj : dist (choose i : X) (w.center j) < δ / 2 := by
      rw [hij]
      simpa [dist_comm] using Metric.mem_ball.mp (choose_spec j)
    have hlt : dist (w.center i) (w.center j) < δ := by
      calc
        dist (w.center i) (w.center j) ≤
            dist (w.center i) (choose i : X) + dist (choose i : X) (w.center j) :=
          dist_triangle _ _ _
        _ < δ / 2 + δ / 2 := add_lt_add hi hj
        _ = δ := by ring
    exact (not_lt_of_ge hsep) hlt
  simpa using Fintype.card_le_of_injective choose hchoose_inj

noncomputable def packingNumber {X : Type*} [MetricSpace X]
    (x : X) (δ R : ℝ) : WithTop ℕ :=
  sSup ((fun n : ℕ => (n : WithTop ℕ)) '' packingAdmissible x δ R)

theorem PackingWitness.card_le_packingNumber {X : Type*} [MetricSpace X]
    {x : X} {δ R : ℝ} {n : ℕ} (w : PackingWitness x δ R n) :
    (n : WithTop ℕ) ≤ packingNumber x δ R := by
  unfold packingNumber
  exact le_sSup ⟨n, ⟨w⟩, rfl⟩

theorem packingNumber_le_of_bound {X : Type*} [MetricSpace X]
    (x : X) (δ R : ℝ) {N : ℕ}
    (hN : ∀ n, n ∈ packingAdmissible x δ R → n ≤ N) :
    packingNumber x δ R ≤ (N : WithTop ℕ) := by
  unfold packingNumber
  refine sSup_le ?_
  rintro z ⟨n, hn, rfl⟩
  exact WithTop.coe_le_coe.mpr (hN n hn)

theorem finite_of_subset_ball_packing_bound {X : Type*} [MetricSpace X]
    (x : X) {δ R : ℝ} {N : ℕ} (hδ : 0 < δ)
    (hN : ∀ n, n ∈ packingAdmissible x δ R → n ≤ N)
    {S : Set X} (hS : S ⊆ Metric.ball x (R - δ))
    (hsep : ∀ ⦃u v : X⦄, u ∈ S → v ∈ S → u ≠ v →
      2 * δ ≤ dist u v) :
    S.Finite := by
  by_contra hfin
  have hSinf : S.Infinite := hfin
  obtain ⟨C, hCS, hCfin, hCcard⟩ := hSinf.exists_subset_ncard_eq (N + 1)
  have hCpack : C.ncard ∈ packingAdmissible x δ R := by
    let T : Finset X := hCfin.toFinset
    have hTcoe : (↑T : Set X) = C := hCfin.coe_toFinset
    have hrad : ∀ u : X, u ∈ (↑T : Set X) →
        dist u x + δ ≤ R := by
      intro u hu
      have huC : u ∈ C := hTcoe ▸ hu
      have huS : u ∈ S := hCS huC
      have hub := hS huS
      rw [Metric.mem_ball] at hub
      linarith
    let c : Fin T.card → X := fun i => ((Finset.equivFin T).symm i : X)
    have hc : ∀ i, dist (c i) x + δ ≤ R := by
      intro i
      apply hrad (c i)
      exact ((Finset.equivFin T).symm i).property
    have hsep' : ∀ ⦃i j : Fin T.card⦄, i ≠ j →
        2 * δ ≤ dist (c i) (c j) := by
      intro i j hij
      have hne : c i ≠ c j := by
        intro heq
        apply hij
        apply (Finset.equivFin T).symm.injective
        apply Subtype.ext
        exact heq
      apply hsep
      · exact hCS (hTcoe ▸ ((Finset.equivFin T).symm i).property)
      · exact hCS (hTcoe ▸ ((Finset.equivFin T).symm j).property)
      · exact hne
    have hw : T.card ∈ packingAdmissible x δ R := by
      exact ⟨packingWitness_of_separated_centers x hδ c hc hsep'⟩
    simpa [T, Set.ncard_eq_toFinset_card C hCfin] using hw
  have hle : C.ncard ≤ N := hN _ hCpack
  rw [hCcard] at hle
  exact (Nat.not_succ_le_self N) hle

theorem ncard_le_of_finite_subset_ball_packing_bound
    {X : Type*} [MetricSpace X]
    (x : X) {δ R : ℝ} {N : ℕ} (hδ : 0 < δ)
    (hN : ∀ n, n ∈ packingAdmissible x δ R → n ≤ N)
    {S : Set X} (hS : S ⊆ Metric.ball x (R - δ))
    (hsep : ∀ ⦃u v : X⦄, u ∈ S → v ∈ S → u ≠ v →
      2 * δ ≤ dist u v)
    (hSfin : S.Finite) :
    S.ncard ≤ N := by
  let T : Finset X := hSfin.toFinset
  have hTcoe : (↑T : Set X) = S := hSfin.coe_toFinset
  let c : Fin T.card → X := fun i => ((Finset.equivFin T).symm i : X)
  have hc : ∀ i, dist (c i) x + δ ≤ R := by
    intro i
    have hi : c i ∈ S := by
      rw [← hTcoe]
      exact ((Finset.equivFin T).symm i).property
    have hi' := hS hi
    rw [Metric.mem_ball] at hi'
    exact le_of_lt (by linarith)
  have hsep' : ∀ ⦃i j : Fin T.card⦄, i ≠ j →
      2 * δ ≤ dist (c i) (c j) := by
    intro i j hij
    have hi : c i ∈ S := by
      rw [← hTcoe]
      exact ((Finset.equivFin T).symm i).property
    have hj : c j ∈ S := by
      rw [← hTcoe]
      exact ((Finset.equivFin T).symm j).property
    have hne : c i ≠ c j := by
      intro heq
      apply hij
      apply (Finset.equivFin T).symm.injective
      apply Subtype.ext
      exact heq
    exact hsep hi hj hne
  have hw : T.card ∈ packingAdmissible x δ R := by
    exact ⟨packingWitness_of_separated_centers x hδ c hc hsep'⟩
  have hle := hN T.card hw
  simpa [T, Set.ncard_eq_toFinset_card S hSfin] using hle

theorem exists_finite_ball_cover_of_uniform_packing_bound_with_card
    {X : Type*} [MetricSpace X] (x : X) {R η : ℝ} {N : ℕ}
    (hR : 0 < R) (hη : 0 < η)
    (hN : ∀ n, n ∈ packingAdmissible x (η / 2) (R + 1 + η / 2) →
      n ≤ N) :
    ∃ L : Set X, L.Finite ∧ L.ncard ≤ N ∧ ∀ y ∈ Metric.ball x R,
      ∃ z ∈ L, dist y z < η := by
  let B : Set X := Metric.ball x (R + 1)
  let xb : B := ⟨x, Metric.mem_ball_self (by linarith)⟩
  obtain ⟨L₀, hx₀, hcover₀, hsep₀⟩ :=
    exists_isDeltaNet_separated η hη xb
  let S : Set X := (fun z : B => (z : X)) '' L₀
  have hS : S ⊆ Metric.ball x ((R + 1 + η / 2) - η / 2) := by
    intro y hy
    rcases hy with ⟨z, hz, rfl⟩
    have hzB : (z : X) ∈ Metric.ball x (R + 1) := z.property
    rw [Metric.mem_ball] at hzB ⊢
    linarith
  have hsep : ∀ ⦃u v : X⦄, u ∈ S → v ∈ S → u ≠ v →
      2 * (η / 2) ≤ dist u v := by
    intro u v hu hv huv
    rcases hu with ⟨a, ha, rfl⟩
    rcases hv with ⟨b, hb, rfl⟩
    have hab : a ≠ b := by
      intro hab
      apply huv
      exact congrArg (fun z : B => (z : X)) hab
    have h := hsep₀ ha hb hab
    rw [Subtype.dist_eq] at h
    simpa [two_mul] using h
  have hSfin : S.Finite :=
    finite_of_subset_ball_packing_bound x (δ := η / 2)
      (R := R + 1 + η / 2) (by linarith) hN hS hsep
  have hSncard := ncard_le_of_finite_subset_ball_packing_bound x
    (δ := η / 2) (R := R + 1 + η / 2) (by linarith) hN hS hsep hSfin
  refine ⟨S, hSfin, hSncard, ?_⟩
  intro y hy
  have hyB : y ∈ Metric.ball x (R + 1) := by
    rw [Metric.mem_ball] at hy ⊢
    linarith
  obtain ⟨z, hz, hdist⟩ := hcover₀ ⟨y, hyB⟩
  refine ⟨(z : X), ⟨z, hz, rfl⟩, ?_⟩
  rw [Subtype.dist_eq] at hdist
  exact hdist

theorem exists_finite_ball_cover_of_uniform_packing_bound
    {X : Type*} [MetricSpace X] (x : X) {R η : ℝ} (hR : 0 < R) (hη : 0 < η)
    (hpack : ∀ (δ R : ℝ), 0 < δ → ∃ N : ℕ,
      ∀ n, n ∈ packingAdmissible x δ R → n ≤ N) :
    ∃ L : Set X, L.Finite ∧ ∀ y ∈ Metric.ball x R,
      ∃ z ∈ L, dist y z < η := by
  obtain ⟨N, hN⟩ := hpack (η / 2) (R + 1 + η / 2) (by linarith)
  obtain ⟨L, hLfin, _, hLcover⟩ :=
    exists_finite_ball_cover_of_uniform_packing_bound_with_card
      x hR hη hN
  exact ⟨L, hLfin, hLcover⟩

theorem exists_finite_closedBall_cover_of_uniform_packing_bound_with_card
    {X : Type*} [MetricSpace X] (x : X) {R η : ℝ} {N : ℕ}
    (hR : 0 ≤ R) (hη : 0 < η)
    (hN : ∀ n, n ∈ packingAdmissible x (η / 2) (R + 1 + η / 2) →
      n ≤ N) :
    ∃ L : Set (Metric.closedBall x R), L.Finite ∧ L.ncard ≤ N ∧
      (Set.univ : Set (Metric.closedBall x R)) ⊆
        ⋃ y ∈ L, Metric.ball y η := by
  let B : Set X := Metric.closedBall x R
  let xb : B := ⟨x, Metric.mem_closedBall_self hR⟩
  obtain ⟨L₀, hx₀, hcover₀, hsep₀⟩ :=
    exists_isDeltaNet_separated η hη xb
  let S : Set X := (fun z : B ↦ (z : X)) '' L₀
  have hS : S ⊆ Metric.ball x ((R + 1 + η / 2) - η / 2) := by
    intro y hy
    rcases hy with ⟨z, hz, rfl⟩
    rw [Metric.mem_ball]
    have hzmem : (z : X) ∈ Metric.closedBall x R := by
      simpa only [B] using z.property
    have hzB : dist (z : X) x ≤ R := Metric.mem_closedBall.mp hzmem
    linarith
  have hsep : ∀ (a b : X), a ∈ S → b ∈ S → a ≠ b →
      2 * (η / 2) ≤ dist a b := by
    intro a b ha hb hab
    rcases ha with ⟨a, ha, rfl⟩
    rcases hb with ⟨b, hb, rfl⟩
    have hab' : a ≠ b := by
      intro h
      apply hab
      exact congrArg (fun z : B ↦ (z : X)) h
    have h := hsep₀ ha hb hab'
    rw [Subtype.dist_eq] at h
    simpa [two_mul] using h
  have hSfin : S.Finite :=
    finite_of_subset_ball_packing_bound x (δ := η / 2)
      (R := R + 1 + η / 2) (by linarith) hN hS hsep
  have hSncard := ncard_le_of_finite_subset_ball_packing_bound x
    (δ := η / 2) (R := R + 1 + η / 2) (by linarith) hN hS hsep hSfin
  have hLfin : L₀.Finite := by
    apply Set.Finite.of_finite_image (f := fun z : B ↦ (z : X))
    · exact hSfin
    · exact Set.injOn_of_injective Subtype.val_injective
  have hLncard : L₀.ncard ≤ N := by
    rw [← Set.ncard_image_of_injective L₀ Subtype.val_injective]
    exact hSncard
  refine ⟨L₀, hLfin, hLncard, ?_⟩
  intro y hy
  obtain ⟨z, hz, hyz⟩ := hcover₀ y
  exact Set.mem_iUnion₂.mpr ⟨z, hz, hyz⟩

theorem totallyBounded_closedBall_of_uniform_packing_bound
    {X : Type*} [MetricSpace X] (x : X) {R : ℝ} (hR : 0 ≤ R)
    (hpack : ∀ (δ R : ℝ), 0 < δ → ∃ N : ℕ,
      ∀ n, n ∈ packingAdmissible x δ R → n ≤ N) :
    TotallyBounded (Metric.closedBall x R) := by
  rw [Metric.totallyBounded_iff]
  intro η hη
  obtain ⟨L, hLfin, hcover⟩ :=
    exists_finite_ball_cover_of_uniform_packing_bound x
      (R := R + 1) (η := η) (by linarith) hη hpack
  refine ⟨L, hLfin, ?_⟩
  intro y hy
  have hyopen : y ∈ Metric.ball x (R + 1) := by
    rw [Metric.mem_ball]
    exact lt_of_le_of_lt (Metric.mem_closedBall.mp hy) (by linarith)
  obtain ⟨z, hz, hdist⟩ := hcover y hyopen
  exact Set.mem_iUnion₂.mpr ⟨z, hz, hdist⟩

theorem packingNumber_lt_top_of_bound {X : Type*} [MetricSpace X]
    (x : X) (δ R : ℝ) {N : ℕ}
    (hN : ∀ n, n ∈ packingAdmissible x δ R → n ≤ N) :
    packingNumber x δ R < ⊤ := by
  unfold packingNumber
  apply lt_of_le_of_lt ?_ (WithTop.coe_lt_top N)
  refine sSup_le ?_
  rintro z ⟨n, hn, rfl⟩
  exact WithTop.coe_le_coe.mpr (hN n hn)

theorem zero_mem_packingAdmissible {X : Type*} [MetricSpace X]
    (x : X) (δ R : ℝ) : 0 ∈ packingAdmissible x δ R := by
  exact ⟨⟨(fun i => Fin.elim0 i), (fun i => Fin.elim0 i),
    (fun i z hz => Fin.elim0 i), (fun i => Fin.elim0 i)⟩⟩

theorem exists_packingWitness_of_packingNumber_lt_top
    {X : Type*} [MetricSpace X] (x : X) (δ R : ℝ)
    (hN : packingNumber x δ R < ⊤) :
    ∃ n, n ∈ packingAdmissible x δ R ∧
      packingNumber x δ R = (n : WithTop ℕ) := by
  let S : Set (WithTop ℕ) :=
    (fun n : ℕ => (n : WithTop ℕ)) '' packingAdmissible x δ R
  have hS : S.Nonempty := by
    refine ⟨(0 : WithTop ℕ), ?_⟩
    exact ⟨0, zero_mem_packingAdmissible x δ R, rfl⟩
  obtain ⟨N, hN_eq⟩ := WithTop.ne_top_iff_exists.mp hN.ne
  have hfinite_admissible : (packingAdmissible x δ R).Finite := by
    apply (Set.finite_le_nat N).subset
    intro n hn
    have hn' : (n : WithTop ℕ) ≤ packingNumber x δ R :=
      le_sSup ⟨n, hn, rfl⟩
    rw [← hN_eq] at hn'
    exact WithTop.coe_le_coe.mp hn'
  have hfiniteS : S.Finite := hfinite_admissible.image _
  have hmem : sSup S ∈ S := hS.csSup_mem hfiniteS
  rcases hmem with ⟨n, hn, hEq⟩
  refine ⟨n, hn, ?_⟩
  simpa [S, packingNumber] using hEq.symm

theorem exists_packingWitness_attaining_of_totallyBounded_closedBall
    {X : Type*} [MetricSpace X] (x : X) {δ R : ℝ} (hδ : 0 < δ)
    (hball : TotallyBounded (Metric.closedBall x R)) :
    ∃ n, n ∈ packingAdmissible x δ R ∧
      packingNumber x δ R = (n : WithTop ℕ) := by
  obtain ⟨N, hN⟩ := exists_packing_bound_of_totallyBounded_closedBall x hδ hball
  exact exists_packingWitness_of_packingNumber_lt_top x δ R
    (packingNumber_lt_top_of_bound x δ R hN)

theorem packingAdmissible_mono_radius {X : Type*} [MetricSpace X]
    (x : X) {δ R₁ R₂ : ℝ} (hR : R₁ ≤ R₂) :
    packingAdmissible x δ R₁ ⊆ packingAdmissible x δ R₂ := by
  intro n hn
  rcases hn with ⟨w⟩
  exact ⟨⟨w.center, fun i => Metric.mem_ball.mpr
    (lt_of_lt_of_le (Metric.mem_ball.mp (w.center_mem i)) hR),
    fun i z hz => Metric.mem_ball.mpr
      (lt_of_lt_of_le (Metric.mem_ball.mp (w.ball_subset i hz)) hR),
    w.pairwise_disjoint⟩⟩

theorem packingAdmissible_mono_scale {X : Type*} [MetricSpace X]
    (x : X) {δ₁ δ₂ R : ℝ} (hδ : δ₂ ≤ δ₁) :
    packingAdmissible x δ₁ R ⊆ packingAdmissible x δ₂ R := by
  intro n hn
  rcases hn with ⟨w⟩
  refine ⟨⟨w.center, w.center_mem, ?_, ?_⟩⟩
  · intro i z hz
    exact w.ball_subset i (by
      rw [Metric.mem_ball] at hz ⊢
      exact lt_of_lt_of_le hz hδ)
  · intro i j hij
    apply (w.pairwise_disjoint hij).mono
    · intro z hz
      rw [Metric.mem_ball] at hz ⊢
      exact lt_of_lt_of_le hz hδ
    · intro z hz
      rw [Metric.mem_ball] at hz ⊢
      exact lt_of_lt_of_le hz hδ

theorem packingNumber_mono_radius {X : Type*} [MetricSpace X]
    (x : X) {δ R₁ R₂ : ℝ} (hR : R₁ ≤ R₂) :
    packingNumber x δ R₁ ≤ packingNumber x δ R₂ := by
  unfold packingNumber
  exact sSup_le_sSup (Set.image_mono (packingAdmissible_mono_radius x hR))

theorem packingNumber_mono_scale {X : Type*} [MetricSpace X]
    (x : X) {δ₁ δ₂ R : ℝ} (hδ : δ₂ ≤ δ₁) :
    packingNumber x δ₁ R ≤ packingNumber x δ₂ R := by
  unfold packingNumber
  exact sSup_le_sSup (Set.image_mono (packingAdmissible_mono_scale x hδ))

theorem exists_common_subseq_tendsto_fin
    {X : Type*} [MetricSpace X] {K : Set X} (hK : IsCompact K)
    {m : ℕ} (f : ℕ → Fin m → X)
    (hf : ∀ n i, f n i ∈ K) :
    ∃ a : Fin m → X, ∃ φ : ℕ → ℕ,
      StrictMono φ ∧
      (∀ i, Tendsto (fun n => f (φ n) i) atTop (𝓝 (a i))) := by
  let S : Set (Fin m → X) := Set.univ.pi (fun _ => K)
  have hS : IsCompact S := isCompact_univ_pi (fun _ => hK)
  let g : ℕ → (Fin m → X) := fun n i => f n i
  have hg : ∀ n, g n ∈ S := by
    intro n i hi
    exact hf n i
  obtain ⟨a, ha, φ, hφ, hconv⟩ := hS.tendsto_subseq hg
  refine ⟨a, φ, hφ, ?_⟩
  intro i
  have happly : Tendsto (fun q : Fin m → X => q i) (𝓝 a) (𝓝 (a i)) :=
    (continuous_apply i).tendsto a
  have hcoord := happly.comp hconv
  simpa [g, Function.comp_def] using hcoord

theorem PackingWitness.exists_common_subseq_tendsto_centers
    {X : Type*} [MetricSpace X] {x : X} {δ R : ℝ} {m : ℕ}
    (hball : IsCompact (Metric.closedBall x R))
    (w : ℕ → PackingWitness x δ R m) :
    ∃ a : Fin m → X, ∃ φ : ℕ → ℕ,
      StrictMono φ ∧
      (∀ i, Tendsto (fun n => (w (φ n)).center i) atTop (𝓝 (a i))) := by
  apply exists_common_subseq_tendsto_fin (m := m) hball
    (fun n i => (w n).center i)
  intro n i
  exact Metric.mem_closedBall.mpr
    (le_of_lt (Metric.mem_ball.mp ((w n).center_mem i)))

theorem exists_subseq_tendsto_countable_family
    {X : Type*} [MetricSpace X] {K : Set X} (hK : IsCompact K)
    (f : ℕ → ℕ → X) (hf : ∀ n i, f n i ∈ K) :
    ∃ a : ℕ → X, ∃ φ : ℕ → ℕ,
      StrictMono φ ∧
      (∀ i, Tendsto (fun n => f (φ n) i) atTop (𝓝 (a i))) := by
  let Kc : TopologicalSpace.Compacts X := ⟨K, hK⟩
  let g : ℕ → (ℕ → Kc) := fun n i => ⟨f n i, hf n i⟩
  have hg : ∀ n, g n ∈ (Set.univ : Set (ℕ → Kc)) := by
    intro n
    exact Set.mem_univ _
  have hcompact : IsCompact (Set.univ : Set (ℕ → Kc)) := isCompact_univ
  obtain ⟨a, ha, φ, hφ, hconv⟩ := hcompact.tendsto_subseq hg
  let aX : ℕ → X := fun i => (a i : Kc)
  refine ⟨aX, φ, hφ, ?_⟩
  intro i
  have hev : Tendsto (fun q : (ℕ → Kc) => q i) (𝓝 a) (𝓝 (a i)) :=
    (continuous_apply i).tendsto a
  have hval : Tendsto (fun q : (ℕ → Kc) => (q i : X)) (𝓝 a)
      (𝓝 (aX i)) :=
    (continuous_subtype_val.tendsto _).comp hev
  have hseq := hval.comp hconv
  simpa [aX, Function.comp_def, g] using hseq

end Poincare.GromovHausdorff
