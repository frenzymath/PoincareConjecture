import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Separation
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geometry.Transport.Charts

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.EpsilonNeck

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} {N N' N'' : EpsilonNeck g}

private theorem sign_mul_mem_Ioo {σ a s : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hs : s ∈ Set.Ioo (-a) a) : σ * s ∈ Set.Ioo (-a) a := by
  rcases hσ with rfl | rfl
  · simpa only [one_mul] using hs
  · simp only [Set.mem_Ioo, neg_one_mul] at *
    constructor <;> linarith [hs.1, hs.2]

namespace SameUpToReversal

@[refl] theorem refl (N : EpsilonNeck g) : N.SameUpToReversal N := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, 1, Or.inl rfl, ?_⟩
  intro z _
  simp only [one_mul, Prod.eta]

theorem epsilon_eq (h : N.SameUpToReversal N') : N.epsilon = N'.epsilon := h.1

theorem scale_eq (h : N.SameUpToReversal N') : N.scale = N'.scale := h.2.1

theorem center_eq (h : N.SameUpToReversal N') : N.center = N'.center := h.2.2.1

theorem carrier_eq (h : N.SameUpToReversal N') : N.carrier = N'.carrier := h.2.2.2.1

theorem central_sphere_eq (h : N.SameUpToReversal N') :
    N.central_sphere = N'.central_sphere := h.2.2.2.2.1

@[symm] theorem symm (h : N.SameUpToReversal N') : N'.SameUpToReversal N := by
  rcases h with ⟨he, hs, hc, hu, hS, σ, hσ, hcoord⟩
  refine ⟨he.symm, hs.symm, hc.symm, hu.symm, hS.symm, σ, hσ, ?_⟩
  intro z hz
  have hz' : σ * z.2 ∈ Set.Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
    rw [he]
    exact sign_mul_mem_Ioo hσ hz
  have h := hcoord (z.1, σ * z.2) hz'
  rcases hσ with rfl | rfl
  · simpa only [one_mul, Prod.eta] using h.symm
  · simpa only [neg_one_mul, neg_neg, Prod.eta] using h.symm

@[trans] theorem trans (h : N.SameUpToReversal N') (h' : N'.SameUpToReversal N'') :
    N.SameUpToReversal N'' := by
  rcases h with ⟨he, hs, hc, hu, hS, σ, hσ, hcoord⟩
  rcases h' with ⟨he', hs', hc', hu', hS', τ, hτ, hcoord'⟩
  refine ⟨he.trans he', hs.trans hs', hc.trans hc', hu.trans hu', hS.trans hS',
    τ * σ, ?_, ?_⟩
  · rcases hσ with rfl | rfl <;> rcases hτ with rfl | rfl <;> norm_num
  · intro z hz
    have hz' : σ * z.2 ∈ Set.Ioo (-N'.epsilon⁻¹) N'.epsilon⁻¹ := by
      rw [← he]
      exact sign_mul_mem_Ioo hσ hz
    rw [hcoord z hz, hcoord' (z.1, σ * z.2) hz']
    simp only [mul_assoc]

theorem isSeparating_iff (h : N.SameUpToReversal N') :
    N.IsSeparating ↔ N'.IsSeparating := by
  simp only [IsSeparating, h.center_eq, h.central_sphere_eq]

theorem isNonseparating_iff (h : N.SameUpToReversal N') :
    N.IsNonseparating ↔ N'.IsNonseparating := by
  simp only [IsNonseparating, h.center_eq, h.central_sphere_eq]

theorem exists_coordinate_inverse (h : N.SameUpToReversal N') :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      ∀ x ∈ N.carrier, N'.coordinate_inverse x =
        ((N.coordinate_inverse x).1, σ * (N.coordinate_inverse x).2) := by
  obtain ⟨σ, hσ, hcoord⟩ := h.2.2.2.2.2
  refine ⟨σ, hσ, ?_⟩
  intro x hx
  have hz := (N.coordinate_inverse_mem x hx).2
  have hz' : ((N.coordinate_inverse x).1, σ * (N.coordinate_inverse x).2) ∈
      N'.cylinderDomain := by
    refine ⟨Set.mem_univ _, ?_⟩
    rw [← h.epsilon_eq]
    exact sign_mul_mem_Ioo hσ hz
  calc
    N'.coordinate_inverse x =
        N'.coordinate_inverse (N.coordinate_map (N.coordinate_inverse x)) :=
      congrArg N'.coordinate_inverse (N.coordinate_map_coordinate_inverse hx).symm
    _ = N'.coordinate_inverse (N'.coordinate_map
        ((N.coordinate_inverse x).1, σ * (N.coordinate_inverse x).2)) :=
      congrArg N'.coordinate_inverse (hcoord (N.coordinate_inverse x) hz)
    _ = ((N.coordinate_inverse x).1, σ * (N.coordinate_inverse x).2) :=
      N'.coordinate_inverse_coordinate_map hz'

theorem regions_eq_or_reversed (h : N.SameUpToReversal N') :
    (∀ a b : ℝ, N.region a b = N'.region a b) ∨
      (∀ a b : ℝ, N.region a b = N'.region (-b) (-a)) := by
  obtain ⟨σ, hσ, hinverse⟩ := h.exists_coordinate_inverse
  rcases hσ with rfl | rfl
  · left
    intro a b
    ext x
    by_cases hx : x ∈ N.carrier
    · simp only [region, Set.mem_ofPred_eq, ← h.carrier_eq, hx, true_and,
        hinverse x hx, one_mul]
    · simp only [region, Set.mem_ofPred_eq, ← h.carrier_eq, hx, false_and]
  · right
    intro a b
    ext x
    by_cases hx : x ∈ N.carrier
    · simp only [region, Set.mem_ofPred_eq, ← h.carrier_eq, hx, true_and,
        hinverse x hx, neg_one_mul]
      constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
    · simp only [region, Set.mem_ofPred_eq, ← h.carrier_eq, hx, false_and]

end SameUpToReversal

theorem sameUpToReversal_equivalence : Equivalence (SameUpToReversal (g := g)) :=
  ⟨SameUpToReversal.refl, fun h => h.symm, fun h h' => h.trans h'⟩

end PoincareConjecture.EpsilonNeck
