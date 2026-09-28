import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Overlap.Coverage
import Mathlib.Topology.OpenPartialHomeomorph.Basic










set_option autoImplicit false
open Set Filter Metric
open scoped Topology NNReal

namespace PoincareConjecture.ChartDistance

variable {ι : Type*} {X : ι → Type*}


def overlap (D : ∀ i j, X i × X j → ℝ) (i j : ι) : Set (X i) :=
  {x | ∃ y, D i j (x, y) = 0}


noncomputable def transition [∀ i, Nonempty (X i)]
    (D : ∀ i j, X i × X j → ℝ) (i j : ι) (x : X i) : X j := by
  classical
  exact if h : x ∈ overlap D i j then Classical.choose h else Classical.ofNonempty

theorem transition_zero [∀ i, Nonempty (X i)]
    (D : ∀ i j, X i × X j → ℝ) {i j : ι} {x : X i}
    (hx : x ∈ overlap D i j) : D i j (x, transition D i j x) = 0 := by
  classical
  simpa only [transition, dif_pos hx] using Classical.choose_spec hx

variable [∀ i, MetricSpace (X i)]
    {M : ℕ → Type*} [∀ k, MetricSpace (M k)]
    {e : ∀ k i, X i → M k} {D : ∀ i j, X i × X j → ℝ}
    (hD : ∀ i j x y, Tendsto (fun k => dist (e k i x) (e k j y)) atTop
      (𝓝 (D i j (x, y))))
    (L : ι → ℝ≥0) (he : ∀ k i, LipschitzWith (L i) (e k i))
    (c : ι → ℝ) (hc : ∀ i, 0 < c i)
    (hlower : ∀ k i x y, c i * dist x y ≤ dist (e k i x) (e k i y))

include hD in
omit [∀ i, MetricSpace (X i)] in
theorem overlap_self (i : ι) : overlap D i i = univ := by
  ext x
  exact ⟨fun _ => mem_univ _, fun _ => ⟨x, self hD i x⟩⟩

include hD he hlower hc in
theorem isOpen_overlap [∀ i, LocallyCompactSpace (X i)]
    (hopen : ∀ k i, Topology.IsOpenEmbedding (e k i))
    (hconn : ∀ k (p : M k) r, IsPreconnected (ball p r)) (i j : ι) :
    IsOpen (overlap D i j) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro x ⟨y, hxy⟩
  exact exists_zero_nhds hD L he hopen c hc hlower hconn hxy

variable [∀ i, Nonempty (X i)]

include hD hlower hc in
theorem zero_iff_transition {i j : ι} {x : X i} {y : X j} :
    D i j (x, y) = 0 ↔ x ∈ overlap D i j ∧ transition D i j x = y := by
  constructor
  · intro h
    have hx : x ∈ overlap D i j := ⟨y, h⟩
    exact ⟨hx, zero_unique hD c hc hlower (transition_zero D hx) h⟩
  · rintro ⟨hx, rfl⟩
    exact transition_zero D hx

include hD in
omit [∀ i, MetricSpace (X i)] in
theorem transition_mem {i j : ι} {x : X i} (hx : x ∈ overlap D i j) :
    transition D i j x ∈ overlap D j i :=
  ⟨x, (comm hD j i _ _).trans (transition_zero D hx)⟩

include hD hlower hc in
theorem transition_inverse {i j : ι} {x : X i} (hx : x ∈ overlap D i j) :
    transition D j i (transition D i j x) = x :=
  (zero_iff_transition hD c hc hlower).mp
    ((comm hD j i _ _).trans (transition_zero D hx)) |>.2

include hD hlower hc in
theorem transition_self (i : ι) (x : X i) : transition D i i x = x :=
  (zero_iff_transition hD c hc hlower).mp (self hD i x) |>.2

include hD he hlower hc in
theorem lipschitzOn_transition (i j : ι) :
    LipschitzOnWith (Real.toNNReal ((L i : ℝ) / c j))
      (transition D i j) (overlap D i j) := by
  apply LipschitzOnWith.of_dist_le'
  intro x hx y hy
  have hx0 := transition_zero D hx
  have hy0 := transition_zero D hy
  have h1 := triangle hD j i j (transition D i j x) x (transition D i j y)
  have h2 := triangle hD i i j x y (transition D i j y)
  rw [(comm hD j i _ _).trans hx0, zero_add] at h1
  rw [hy0, add_zero] at h2
  have h := (lower hD c hlower j _ _).trans
    (h1.trans (h2.trans (upper hD L he i x y)))
  calc
    dist (transition D i j x) (transition D i j y) ≤
        ((L i : ℝ) * dist x y) / c j :=
      (le_div_iff₀ (hc j)).2 (by simpa only [mul_comm] using h)
    _ = (L i : ℝ) / c j * dist x y := by ring

include hD he hlower hc in


noncomputable def overlapHomeomorph [∀ i, LocallyCompactSpace (X i)]
    (hopen : ∀ k i, Topology.IsOpenEmbedding (e k i))
    (hconn : ∀ k (p : M k) r, IsPreconnected (ball p r)) (i j : ι) :
    OpenPartialHomeomorph (X i) (X j) where
  toFun := transition D i j
  invFun := transition D j i
  source := overlap D i j
  target := overlap D j i
  map_source' := fun _ hx => transition_mem hD hx
  map_target' := fun _ hx => transition_mem hD hx
  left_inv' := fun _ hx => transition_inverse hD c hc hlower hx
  right_inv' := fun _ hx => transition_inverse hD c hc hlower hx
  open_source := isOpen_overlap hD L he c hc hlower hopen hconn i j
  open_target := isOpen_overlap hD L he c hc hlower hopen hconn j i
  continuousOn_toFun := (lipschitzOn_transition hD L he c hc hlower i j).continuousOn
  continuousOn_invFun := (lipschitzOn_transition hD L he c hc hlower j i).continuousOn

include hD hlower hc in


theorem transition_cocycle {i j l : ι} {x : X i}
    (hx : x ∈ overlap D i j) (hy : transition D i j x ∈ overlap D j l) :
    x ∈ overlap D i l ∧
      transition D j l (transition D i j x) = transition D i l x := by
  have h := zero_trans hD (transition_zero D hx) (transition_zero D hy)
  obtain ⟨hx', heq⟩ := (zero_iff_transition hD c hc hlower).mp h
  exact ⟨hx', heq.symm⟩

end PoincareConjecture.ChartDistance
