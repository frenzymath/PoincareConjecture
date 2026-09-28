import PoincareConjecture.Proofs.Horizon.Topology.Connected.FourContacts
import PoincareConjecture.Proofs.Horizon.Topology.Connected.FiniteBoundaryComponents
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Tactic.Linarith







noncomputable section
set_option autoImplicit false

open Set

namespace Poincare.Topology

variable {X : Type*} [TopologicalSpace X]

private theorem exists_path_in_interval_image
    {C : Set X} {γ : ℝ → X} (hγ : Continuous γ) {a b : ℝ}
    (hC : γ '' Icc a b = C) {x y : X} (hx : x ∈ C) (hy : y ∈ C) :
    ∃ α : ℝ → X, Continuous α ∧ MapsTo α (Icc (0 : ℝ) 1) C ∧
      α 0 = x ∧ α 1 = y := by
  obtain ⟨s, hs, hxs⟩ := hC.symm ▸ hx
  obtain ⟨t, ht, hyt⟩ := hC.symm ▸ hy
  let u : ℝ → ℝ := fun v => (1 - v) * s + v * t
  have hu : Continuous u :=
    ((continuous_const.sub continuous_id).mul continuous_const).add
      (continuous_id.mul continuous_const)
  refine ⟨γ ∘ u, hγ.comp hu, ?_, ?_, ?_⟩
  · intro v hv
    rw [← hC]
    refine ⟨u v, ?_, rfl⟩
    dsimp only [u]
    constructor
    · nlinarith [mul_nonneg (sub_nonneg.mpr hv.2) (sub_nonneg.mpr hs.1),
        mul_nonneg hv.1 (sub_nonneg.mpr ht.1)]
    · nlinarith [mul_nonneg (sub_nonneg.mpr hv.2) (sub_nonneg.mpr hs.2),
        mul_nonneg hv.1 (sub_nonneg.mpr ht.2)]
  · simpa [u] using hxs
  · simpa [u] using hyt



theorem pairing_of_interval_components
    {K : Set X} (b : Fin 2 × Fin 2 → K) (hb : Function.Injective b)
    (hinterval : ∀ q ∈ K, ∃ (γ : ℝ → X) (a d : ℝ),
      Continuous γ ∧ Function.Injective γ ∧ a < d ∧
      γ '' Icc a d = connectedComponentIn K q ∧
      range (fun i => (b i : X)) ∩ connectedComponentIn K q = {γ a, γ d})
    (hnoncrossing : ∀ (α β : ℝ → X),
      ContinuousOn α (Icc (0 : ℝ) 1) → ContinuousOn β (Icc (0 : ℝ) 1) →
      MapsTo α (Icc (0 : ℝ) 1) K → MapsTo β (Icc (0 : ℝ) 1) K →
      α 0 = b (1, 1) → α 1 = b (0, 0) →
      β 0 = b (0, 1) → β 1 = b (1, 0) →
      ¬ Disjoint (α '' Icc (0 : ℝ) 1) (β '' Icc (0 : ℝ) 1)) :
    (∀ i j, (b i : X) ∈ connectedComponentIn K (b j) ↔ i.1 = j.1) ∨
      (∀ i j, (b i : X) ∈ connectedComponentIn K (b j) ↔ i.2 = j.2) := by
  classical
  have hbi : Function.Injective (fun i => (b i : X)) :=
    fun i j hij => hb (Subtype.ext hij)
  have hfiber (q : K) : Nat.card {i // (b i : X) ∈ connectedComponentIn K q} = 2 := by
    obtain ⟨γ, a, d, _, hγi, had, _, hcontacts⟩ := hinterval q q.property
    exact card_preimage_eq_two_of_range_inter_eq_pair hbi
      (fun h => had.ne (hγi h)) hcontacts
  obtain ⟨E⟩ := nonempty_connectedComponents_equiv_fin_two_of_boundary_fibers b
    (by simp [Nat.card_eq_fintype_card]) hfiber
  let c : Fin 2 × Fin 2 → Fin 2 := fun i => E (ConnectedComponents.mk (b i))
  have hc (i) (q : K) : c i = E (ConnectedComponents.mk q) ↔
      (b i : X) ∈ connectedComponentIn K q := by
    change E (ConnectedComponents.mk (b i)) = E (ConnectedComponents.mk q) ↔ _
    rw [E.injective.eq_iff]
    exact connectedComponents_eq_iff_mem (b i) q
  have hcard (j : Fin 2) : (Finset.univ.filter (fun i => c i = j)).card = 2 := by
    obtain ⟨q, hq⟩ := ConnectedComponents.surjective_coe (E.symm j)
    have hj : E (ConnectedComponents.mk q) = j := by rw [hq]; exact E.apply_symm_apply j
    have heq : {i | c i = j} = {i | (b i : X) ∈ connectedComponentIn K q} := by
      ext i
      rw [← hj]
      exact hc i q
    have hh := hfiber q
    change Nat.card {i : Fin 2 × Fin 2 | (b i : X) ∈ connectedComponentIn K q} = 2 at hh
    rw [← heq, Nat.card_eq_fintype_card, Fintype.card_subtype] at hh
    exact hh
  have hopposite : c (0, 0) ≠ c (1, 1) := by
    intro hdiag
    obtain ⟨hother, hsep⟩ := four_contacts_opposite_pairing c hcard hdiag
    obtain ⟨γ, a, d, hγ, _, _, hγC, _⟩ := hinterval (b (0, 0)) (b (0, 0)).property
    obtain ⟨δ, l, u, hδ, _, _, hδC, _⟩ := hinterval (b (0, 1)) (b (0, 1)).property
    obtain ⟨α, hα, hαC, hα0, hα1⟩ := exists_path_in_interval_image hγ hγC
      ((hc (1, 1) (b (0, 0))).mp hdiag.symm)
      (mem_connectedComponentIn (b (0, 0)).property)
    obtain ⟨β, hβ, hβC, hβ0, hβ1⟩ := exists_path_in_interval_image hδ hδC
      (mem_connectedComponentIn (b (0, 1)).property)
      ((hc (1, 0) (b (0, 1))).mp hother.symm)
    apply hnoncrossing α β hα.continuousOn hβ.continuousOn
      (fun t ht => connectedComponentIn_subset K (b (0, 0)) (hαC ht))
      (fun t ht => connectedComponentIn_subset K (b (0, 1)) (hβC ht))
      hα0 hα1 hβ0 hβ1
    apply disjoint_left.mpr
    rintro x ⟨s, hs, rfl⟩ ⟨t, ht, hts⟩
    have hx₀ := hαC hs
    have hx₁ : α s ∈ connectedComponentIn K (b (0, 1)) := hts ▸ hβC ht
    have heq := (connectedComponentIn_eq hx₀).trans (connectedComponentIn_eq hx₁).symm
    have hmem : (b (0, 0) : X) ∈ connectedComponentIn K (b (0, 1)) :=
      heq ▸ mem_connectedComponentIn (b (0, 0)).property
    exact hsep ((hc (0, 0) (b (0, 1))).mpr hmem)
  rcases four_contacts_pairing c hcard hopposite with hfirst | hsecond
  · exact Or.inl (fun i j => (hc i (b j)).symm.trans (hfirst i j))
  · exact Or.inr (fun i j => (hc i (b j)).symm.trans (hsecond i j))

end Poincare.Topology
