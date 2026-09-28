import PoincareConjecture.Proofs.M76.Mathlib.ConvexBoundaryExtension

set_option autoImplicit false

open Set Metric

namespace Homeomorph

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  {s b : Set X} {t c : Set Y}

def restrictSubsets (e : s ≃ₜ t) (hb : b ⊆ s) (hc : c ⊆ t)
    (he : ∀ x : s, (x : X) ∈ b ↔ (e x : Y) ∈ c) : b ≃ₜ c where
  toFun x := ⟨e ⟨x, hb x.property⟩, (he ⟨x, hb x.property⟩).mp x.property⟩
  invFun y := ⟨e.symm ⟨y, hc y.property⟩,
    (he (e.symm ⟨y, hc y.property⟩)).mpr (by simp)⟩
  left_inv x := Subtype.ext (congrArg (fun z : s => (z : X)) (e.symm_apply_apply _))
  right_inv y := Subtype.ext (congrArg (fun z : t => (z : Y)) (e.apply_symm_apply _))
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem mem_subset_iff_of_extension (e : s ≃ₜ t) (eb : b ≃ₜ c)
    (hb : b ⊆ s) (hc : c ⊆ t)
    (he : ∀ x : b, e ⟨x, hb x.property⟩ = ⟨eb x, hc (eb x).property⟩)
    (x : s) : (x : X) ∈ b ↔ (e x : Y) ∈ c := by
  constructor
  · intro hx
    have h := congrArg (fun z : t => (z : Y)) (he ⟨x, hx⟩)
    exact h.symm ▸ (eb ⟨x, hx⟩).property
  · intro hx
    let y : b := eb.symm ⟨e x, hx⟩
    have hy : e ⟨y, hb y.property⟩ = e x := by
      rw [he]
      apply Subtype.ext
      exact congrArg (fun z : c => (z : Y)) (eb.apply_symm_apply ⟨e x, hx⟩)
    have hv := congrArg (fun z : s => (z : X)) (e.injective hy)
    exact hv ▸ y.property

end Homeomorph

namespace Set

variable (E : Type*) [NormedAddCommGroup E]
  {X : Type*} [TopologicalSpace X]

def IsUnitBallPair (s b : Set X) : Prop :=
  b ⊆ s ∧ ∃ e : s ≃ₜ closedBall (0 : E) 1,
    ∀ x : s, (x : X) ∈ b ↔ (e x : E) ∈ sphere (0 : E) 1

variable {E}

theorem IsUnitBallPair.of_homeomorph {Y : Type*} [TopologicalSpace Y]
    {s b : Set X} {t c : Set Y} (ht : IsUnitBallPair E t c)
    (hb : b ⊆ s) (H : s ≃ₜ t)
    (hH : ∀ x : s, (x : X) ∈ b ↔ (H x : Y) ∈ c) : IsUnitBallPair E s b := by
  obtain ⟨_, e, he⟩ := ht
  exact ⟨hb, H.trans e, fun x => (hH x).trans (he (H x))⟩

theorem isUnitBallPair_of_compact_convex [NormedSpace ℝ E] {s : Set E}
    (hs : IsCompact s) (hcv : Convex ℝ s) (hne : (interior s).Nonempty) :
    IsUnitBallPair E s (frontier s) := by
  obtain ⟨e, eb, he⟩ := hs.exists_compatible_unitBall_models hcv hne
  exact ⟨hs.isClosed.frontier_subset, e, fun x =>
    e.mem_subset_iff_of_extension eb hs.isClosed.frontier_subset sphere_subset_closedBall he x⟩

theorem IsUnitBallPair.exists_extension [NormedSpace ℝ E] [ProperSpace E] [Nontrivial E]
    {F Y : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [ProperSpace F] [Nontrivial F]
    [TopologicalSpace Y] {s b : Set X} {t c : Set Y}
    (hs : IsUnitBallPair E s b) (ht : IsUnitBallPair F t c) (eb : b ≃ₜ c) :
    ∃ e : s ≃ₜ t,
      (∀ x : b, e ⟨x, hs.1 x.property⟩ = ⟨eb x, ht.1 (eb x).property⟩) ∧
      (∀ x : s, (x : X) ∈ b ↔ (e x : Y) ∈ c) := by
  obtain ⟨hb, hX, hXb⟩ := hs
  obtain ⟨hc, hY, hYc⟩ := ht
  let hA := hX.restrictSubsets hb sphere_subset_closedBall hXb
  let hB := hY.restrictSubsets hc sphere_subset_closedBall hYc
  obtain ⟨e, he⟩ := Homeomorph.exists_extension_of_unitBall_models
    (fun x : b => (⟨x, hb x.property⟩ : s))
    (fun y : c => (⟨y, hc y.property⟩ : t)) hX hY hA hB
    (fun _ => Subtype.ext rfl) (fun _ => Subtype.ext rfl) eb
  exact ⟨e, he, e.mem_subset_iff_of_extension eb hb hc he⟩

end Set
