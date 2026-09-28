import PoincareConjecture.Proofs.M35.Uniqueness.Heat.Exhaustion.TensorTestSlab

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {n : ℕ}
local notation "V" => EuclideanSpace ℝ (Fin n)

theorem exists_raw_covariant_derivative_test_slab_bound
    {J I : Set ℝ} (F : RicciFlow n V J) (hI : IsCompact I) (hIJ : I ⊆ J)
    {E : Set V} (hE : IsCompact E) (a : ℝ → V → ℝ)
    (ha : ContDiffOn ℝ ∞ (Function.uncurry a) (I ×ˢ univ))
    (has : ∀ t ∈ I, ContDiff ℝ ∞ (a t))
    (ha0 : ∀ t ∈ I, ∀ x ∉ E, a t x = 0) (u v w : V) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ I, ∀ H : V → (Fin 2 → V) → ℝ,
      IsSmoothCovariantTensor H → ∀ δ : ℝ, 0 ≤ δ →
      (∀ x ∈ E, ((F.metric t).tensorNorm H x) ^ 2 ≤ δ ^ 2) →
      |∫ x, a t x * (F.connection t).covariantTensorDerivative H x ![u, v, w]| ≤ C * δ := by
  have hsupport (t : ℝ) (ht : t ∈ I) : tsupport (a t) ⊆ E := by
    apply closure_minimal _ hE.isClosed
    intro x hx
    by_contra hn
    exact hx (ha0 t ht x hn)
  have hader : ContinuousOn (fun p : ℝ × V => fderiv ℝ (a p.1) p.2 u) (I ×ˢ univ) :=
    ((raw_family_spatial_fderiv_contDiffOn (f := a) ha).clm_apply contDiffOn_const).continuousOn
  have hader0 (t : ℝ) (ht : t ∈ I) (x : V) (hx : x ∉ E) : fderiv ℝ (a t) x u = 0 := by
    have hz : fderiv ℝ (a t) x = 0 := by
      apply fderiv_of_notMem_tsupport
      exact fun hh => hx (hsupport t ht hh)
    rw [hz, zero_apply]
  have hΓv := (raw_connection_pair_family_contDiffOn F u v).continuousOn.mono
    (prod_mono hIJ Subset.rfl)
  have hΓw := (raw_connection_pair_family_contDiffOn F u w).continuousOn.mono
    (prod_mono hIJ Subset.rfl)
  obtain ⟨C₀, hC₀, h₀⟩ := exists_raw_tensor_pair_test_slab_bound F hI hIJ hE
    (fun t x => fderiv ℝ (a t) x u) (fun _ _ => v) (fun _ _ => w)
    hader continuousOn_const continuousOn_const hader0
  obtain ⟨C₁, hC₁, h₁⟩ := exists_raw_tensor_pair_test_slab_bound F hI hIJ hE a
    (fun t x => rawConnectionCoefficient (F.connection t) x u v) (fun _ _ => w)
    ha.continuousOn hΓv continuousOn_const ha0
  obtain ⟨C₂, hC₂, h₂⟩ := exists_raw_tensor_pair_test_slab_bound F hI hIJ hE a
    (fun _ _ => v) (fun t x => rawConnectionCoefficient (F.connection t) x u w)
    ha.continuousOn continuousOn_const hΓw ha0
  refine ⟨C₀ + C₁ + C₂, by positivity, ?_⟩
  intro t ht H hH δ hδ hbound
  have hac : HasCompactSupport (a t) :=
    hE.of_isClosed_subset (isClosed_tsupport (a t)) (hsupport t ht)
  rw [integral_mul_covariant_twoTensor_derivative (F.connection t) hH (has t ht) hac]
  have hb₀ := h₀ t ht H hH δ hδ hbound
  have hb₁ := h₁ t ht H hH δ hδ hbound
  have hb₂ := h₂ t ht H hH δ hδ hbound
  calc
    _ ≤ |-(∫ x, fderiv ℝ (a t) x u * H x ![v, w]) -
        (∫ x, a t x * H x ![rawConnectionCoefficient (F.connection t) x u v, w])| +
        |∫ x, a t x * H x ![v, rawConnectionCoefficient (F.connection t) x u w]| :=
      abs_sub _ _
    _ ≤ (|∫ x, fderiv ℝ (a t) x u * H x ![v, w]| +
        |∫ x, a t x * H x ![rawConnectionCoefficient (F.connection t) x u v, w]|) +
        |∫ x, a t x * H x ![v, rawConnectionCoefficient (F.connection t) x u w]| := by
      exact add_le_add (by simpa only [abs_neg] using (abs_sub
        (-(∫ x, fderiv ℝ (a t) x u * H x ![v, w]))
        (∫ x, a t x * H x ![rawConnectionCoefficient (F.connection t) x u v, w]))) le_rfl
    _ ≤ (C₀ * δ + C₁ * δ) + C₂ * δ := add_le_add (add_le_add hb₀ hb₁) hb₂
    _ = (C₀ + C₁ + C₂) * δ := by ring

end PoincareConjecture.M35.Uniqueness.Heat
