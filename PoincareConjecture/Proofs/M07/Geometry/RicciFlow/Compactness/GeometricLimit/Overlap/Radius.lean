import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Overlap.CompactCoverage
import PoincareConjecture.Proofs.M07.Topology.Exhaustion
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Overlap.Connectedness

set_option autoImplicit false
open Set Filter Metric
open scoped Topology NNReal

namespace PoincareConjecture.ChartDistance

variable {ι : Type*} {X : ι → Type*} [∀ i, MetricSpace (X i)]
    {M : ℕ → Type*} [∀ k, MetricSpace (M k)]
    {e : ∀ k i, X i → M k} {D : ∀ i j, C(X i × X j, ℝ)}
    (hD : ∀ i j x y, Tendsto (fun k => dist (e k i x) (e k j y)) atTop
      (𝓝 (D i j (x, y))))
    (O : Poincare.Gluing.OverlapSystem X)
    (hrel : ∀ i j (x : X i) (y : X j), O.Rel ⟨i, x⟩ ⟨j, y⟩ ↔ D i j (x, y) = 0)

include hD in
theorem eq_of_zero_right {i j l : ι} (p : X i) {x : X j} {y : X l}
    (hxy : D j l (x, y) = 0) : D i j (p, x) = D i l (p, y) := by
  apply le_antisymm
  · have hrev : D l j (y, x) = 0 := (comm hD l j y x).trans hxy
    simpa only [hrev, add_zero] using triangle hD i l j p y x
  · simpa only [hxy, add_zero] using triangle hD i j l p x y

noncomputable def quotientRadius {i₀ : ι} (p : X i₀) : C(Quotient O.setoid, ℝ) where
  toFun := Quotient.lift (fun x : Σ i, X i => D i₀ x.1 (p, x.2))
    (fun a b hab => eq_of_zero_right hD p ((hrel a.1 b.1 a.2 b.2).mp hab))
  continuous_toFun := continuous_quot_lift _ (continuous_sigma_iff.mpr fun i =>
    (D i₀ i).continuous.comp (continuous_const.prodMk continuous_id))

@[simp] theorem quotientRadius_include {i₀ : ι} (p : X i₀) (i : ι) (x : X i) :
    quotientRadius hD O hrel p (O.include i x) = D i₀ i (p, x) := rfl

theorem quotientRadius_nonneg {i₀ : ι} (p : X i₀) (q : Quotient O.setoid) :
    0 ≤ quotientRadius hD O hrel p q := by
  induction q using Quotient.inductionOn with
  | h x => exact nonneg hD i₀ x.1 p x.2

@[simp] theorem quotientRadius_base {i₀ : ι} (p : X i₀) :
    quotientRadius hD O hrel p (O.include i₀ p) = 0 := self hD i₀ p

theorem isCompact_radius_sublevel_of_source_ball_cover
    (L : ι → ℝ≥0) (he : ∀ k i, LipschitzWith (L i) (e k i))
    (s : Finset ι) (K : ∀ j, Set (X j)) (hK : ∀ j ∈ s, IsCompact (K j))
    {i₀ : ι} (p : X i₀) {r R : ℝ} (hr : r < R)
    (hcover : ∀ᶠ k in atTop, ball (e k i₀ p) R ⊆ ⋃ j ∈ s, e k j '' K j) :
    IsCompact {q | quotientRadius hD O hrel p q ≤ r} := by
  obtain ⟨hcompact, hcontains⟩ :=
    compact_cover_of_eventual_source_ball_cover hD L he O hrel s K hK p R hcover
  apply hcompact.of_isClosed_subset
    (isClosed_le (quotientRadius hD O hrel p).continuous continuous_const)
  intro q hq
  induction q using Quotient.inductionOn with
  | h x => exact hcontains x.1 x.2 (lt_of_le_of_lt hq hr)

theorem exists_precompact_radius_exhaustion
    (L : ι → ℝ≥0) (he : ∀ k i, LipschitzWith (L i) (e k i))
    {i₀ : ι} (p : X i₀)
    (hcover : ∀ R : ℝ, 0 < R → ∃ s : Finset ι, ∃ K : ∀ j, Set (X j),
      (∀ j ∈ s, IsCompact (K j)) ∧
        ∀ᶠ k in atTop, ball (e k i₀ p) R ⊆ ⋃ j ∈ s, e k j '' K j) :
    ∃ V : ℕ → Set (Quotient O.setoid),
      (∀ j, V j = {q | quotientRadius hD O hrel p q < (j : ℝ) + 1}) ∧
      (∀ j, IsOpen (V j)) ∧ (∀ j, O.include i₀ p ∈ V j) ∧
      (∀ j, IsCompact (closure (V j))) ∧
      (∀ j, closure (V j) ⊆ V (j + 1)) ∧ (⋃ j, V j) = univ := by
  let ρ := quotientRadius hD O hrel p
  let V : ℕ → Set (Quotient O.setoid) := fun j => {q | ρ q < (j : ℝ) + 1}
  have hclosure (j : ℕ) : closure (V j) ⊆ {q | ρ q ≤ (j : ℝ) + 1} :=
    (isClosed_le ρ.continuous continuous_const).closure_subset_iff.mpr
      (fun q h => show ρ q ≤ (j : ℝ) + 1 from le_of_lt h)
  have hc (j : ℕ) : IsCompact {q | ρ q ≤ (j : ℝ) + 1} := by
    obtain ⟨s, K, hK, hcov⟩ := hcover ((j : ℝ) + 2) (by positivity)
    exact isCompact_radius_sublevel_of_source_ball_cover hD O hrel L he s K hK p
      (by linarith) hcov
  refine ⟨V, fun _ => rfl, fun _ => isOpen_lt ρ.continuous continuous_const,
    ?_, ?_, ?_, ?_⟩
  · intro j
    change quotientRadius hD O hrel p (O.include i₀ p) < (j : ℝ) + 1
    rw [quotientRadius_base]
    positivity
  · intro j
    exact (hc j).of_isClosed_subset isClosed_closure (hclosure j)
  · intro j q hq
    have h : ρ q ≤ (j : ℝ) + 1 := hclosure j hq
    change ρ q < ((j + 1 : ℕ) : ℝ) + 1
    push_cast
    linarith
  · apply eq_univ_of_forall
    intro q
    obtain ⟨j, hj⟩ := exists_nat_gt (ρ q)
    exact mem_iUnion.mpr ⟨j, show ρ q < (j : ℝ) + 1 by linarith⟩

private theorem frontier_component_subset {Y : Type*} [TopologicalSpace Y]
    [LocallyConnectedSpace Y] {V : Set Y} (hV : IsOpen V) (p : Y) :
    frontier (connectedComponentIn V p) ⊆ frontier V := by
  intro q hq
  refine ⟨closure_mono (connectedComponentIn_subset V p) hq.1, ?_⟩
  rw [hV.interior_eq]
  intro hqV
  have hqC : q ∈ connectedComponentIn V q := mem_connectedComponentIn hqV
  obtain ⟨y, hyq, hyp⟩ := mem_closure_iff_nhds.mp hq.1
    (connectedComponentIn V q) (hV.connectedComponentIn.mem_nhds hqC)
  have heq : connectedComponentIn V q = connectedComponentIn V p :=
    (connectedComponentIn_eq hyq).trans (connectedComponentIn_eq hyp).symm
  apply hq.2
  rw [hV.connectedComponentIn.interior_eq]
  exact heq ▸ hqC

theorem exists_connected_radius_exhaustion
    [PreconnectedSpace (Quotient O.setoid)] [LocallyConnectedSpace (Quotient O.setoid)]
    (L : ι → ℝ≥0) (he : ∀ k i, LipschitzWith (L i) (e k i))
    {i₀ : ι} (p : X i₀)
    (hcover : ∀ R : ℝ, 0 < R → ∃ s : Finset ι, ∃ K : ∀ j, Set (X j),
      (∀ j ∈ s, IsCompact (K j)) ∧
        ∀ᶠ k in atTop, ball (e k i₀ p) R ⊆ ⋃ j ∈ s, e k j '' K j) :
    ∃ V : ℕ → Set (Quotient O.setoid),
      (∀ j, IsOpen (V j)) ∧ (∀ j, IsConnected (V j)) ∧
      (∀ j, O.include i₀ p ∈ V j) ∧ (∀ j, IsCompact (closure (V j))) ∧
      (∀ j, closure (V j) ⊆ V (j + 1)) ∧ (⋃ j, V j) = univ ∧
      ∀ j q, q ∈ frontier (V j) → quotientRadius hD O hrel p q = (j : ℝ) + 1 := by
  obtain ⟨U, hUeq, hUopen, hUp, hUc, hUstep, hUcover⟩ :=
    exists_precompact_radius_exhaustion hD O hrel L he p hcover
  let b := O.include i₀ p
  have hUmono : Monotone U := monotone_nat_of_le_succ fun j =>
    subset_closure.trans (hUstep j)
  refine ⟨fun j => connectedComponentIn (U j) b,
    fun j => (hUopen j).connectedComponentIn,
    fun j => isConnected_connectedComponentIn_iff.mpr (hUp j),
    fun j => mem_connectedComponentIn (hUp j), ?_, ?_,
    Poincare.iUnion_connectedComponentIn_eq_univ U hUopen hUmono hUcover b, ?_⟩
  · intro j
    exact (hUc j).of_isClosed_subset isClosed_closure
      (closure_mono (connectedComponentIn_subset _ _))
  · intro j
    exact isPreconnected_connectedComponentIn.closure.subset_connectedComponentIn
      (subset_closure (mem_connectedComponentIn (hUp j)))
      ((closure_mono (connectedComponentIn_subset _ _)).trans (hUstep j))
  · intro j q hq
    have hqU := frontier_component_subset (hUopen j) b hq
    rw [hUeq j] at hqU
    exact frontier_lt_subset_eq (quotientRadius hD O hrel p).continuous
      continuous_const hqU

theorem exists_connected_exhaustion_of_source_ball_covers
    [∀ i, LocallyConnectedSpace (X i)]
    (hlocal : ∀ i j, TendstoLocallyUniformly
      (fun k (p : X i × X j) => dist (e k i p.1) (e k j p.2)) (D i j) atTop)
    (L : ι → ℝ≥0) (he : ∀ k i, LipschitzWith (L i) (e k i))
    (hconn : ∀ k (p : M k) r, IsPreconnected (ball p r))
    {i₀ : ι} (p : X i₀)
    (hcover : ∀ R : ℝ, 0 < R → ∃ s : Finset ι, ∃ K : ∀ j, Set (X j),
      (∀ j ∈ s, IsCompact (K j)) ∧
        ∀ᶠ k in atTop, ball (e k i₀ p) R ⊆ ⋃ j ∈ s, e k j '' K j) :
    ConnectedSpace (Quotient O.setoid) ∧
    ∃ V : ℕ → Set (Quotient O.setoid),
      (∀ j, IsOpen (V j)) ∧ (∀ j, IsConnected (V j)) ∧
      (∀ j, O.include i₀ p ∈ V j) ∧ (∀ j, IsCompact (closure (V j))) ∧
      (∀ j, closure (V j) ⊆ V (j + 1)) ∧ (⋃ j, V j) = univ ∧
      ∀ j q, q ∈ frontier (V j) → quotientRadius hD O hrel p q = (j : ℝ) + 1 := by
  let : PreconnectedSpace (Quotient O.setoid) :=
    quotient_preconnected_of_source_ball_covers hlocal O hrel L he hconn p hcover
  let : LocallyConnectedSpace (Quotient O.setoid) := quotient_locallyConnected_of_charts O
  let : Nonempty (Quotient O.setoid) := ⟨O.include i₀ p⟩
  exact ⟨⟨⟨O.include i₀ p⟩⟩, exists_connected_radius_exhaustion hD O hrel L he p hcover⟩

end PoincareConjecture.ChartDistance
