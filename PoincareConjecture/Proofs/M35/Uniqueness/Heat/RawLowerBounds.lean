import PoincareConjecture.Proofs.M35.Uniqueness.Heat.RawJointLowerOrder
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.LowerOrderDifference

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set
open scoped SchwartzMap

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)

def rawLowerCoefficientArray {g : RiemannianMetric n V} (D : LeviCivitaData g) (x : V) :
    (Fin n → Fin n → Fin n → ℝ) × (Fin n → Fin n → ℝ) :=
  (fun k j i => rawFirstComponent D k j i x, fun k j => rawZeroComponent D k j x)

theorem rawLowerCoefficientArray_family_continuousOn {J : Set ℝ} (F : RicciFlow n V J) :
    ContinuousOn (fun p : ℝ × V => rawLowerCoefficientArray (F.connection p.1) p.2)
      (J ×ˢ univ) := by
  apply ContinuousOn.prodMk
  · apply continuousOn_pi.mpr
    intro k
    apply continuousOn_pi.mpr
    intro j
    apply continuousOn_pi.mpr
    intro i
    exact (rawFirstComponent_family_contDiffOn F k j i).continuousOn
  · apply continuousOn_pi.mpr
    intro k
    apply continuousOn_pi.mpr
    intro j
    exact (rawZeroComponent_family_contDiffOn F k j).continuousOn

theorem rawFirstComponent_le_array_norm {g : RiemannianMetric n V}
    (D : LeviCivitaData g) (x : V) (k j i : Fin n) :
    ‖rawFirstComponent D k j i x‖ ≤ ‖rawLowerCoefficientArray D x‖ :=
  (((norm_le_pi_norm ((rawLowerCoefficientArray D x).1 k j) i).trans
    (norm_le_pi_norm ((rawLowerCoefficientArray D x).1 k) j)).trans
      (norm_le_pi_norm (rawLowerCoefficientArray D x).1 k)).trans (norm_fst_le _)

theorem rawZeroComponent_le_array_norm {g : RiemannianMetric n V}
    (D : LeviCivitaData g) (x : V) (k j : Fin n) :
    ‖rawZeroComponent D k j x‖ ≤ ‖rawLowerCoefficientArray D x‖ :=
  ((norm_le_pi_norm ((rawLowerCoefficientArray D x).2 k) j).trans
    (norm_le_pi_norm (rawLowerCoefficientArray D x).2 k)).trans (norm_snd_le _)

theorem exists_raw_slab_lower_component_bound {J I : Set ℝ} (F : RicciFlow n V J)
    (hI : IsCompact I) (hIJ : I ⊆ J) {K : Set V} (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ t ∈ I, ∀ x ∈ K,
      (∀ k j i, ‖rawFirstComponent (F.connection t) k j i x‖ ≤ C) ∧
      (∀ k j, ‖rawZeroComponent (F.connection t) k j x‖ ≤ C) := by
  have hc := (rawLowerCoefficientArray_family_continuousOn F).mono
    (prod_mono hIJ (subset_univ K))
  obtain ⟨C, hC, hb⟩ := ((hI.prod hK).image_of_continuousOn hc).isBounded.exists_pos_norm_le
  refine ⟨C, hC, ?_⟩
  intro t ht x hx
  have hp : ‖rawLowerCoefficientArray (F.connection t) x‖ ≤ C :=
    hb _ ⟨(t, x), ⟨ht, hx⟩, rfl⟩
  exact ⟨fun k j i => (rawFirstComponent_le_array_norm _ x k j i).trans hp,
    fun k j => (rawZeroComponent_le_array_norm _ x k j).trans hp⟩

def rawLowerFormOperator {g : RiemannianMetric n V} (D : LeviCivitaData g)
    {K : Set V} (hK : IsClosed K) (η : 𝓢(V, ℝ)) (hη : HasCompactSupport η) :
    PiLp 2 (fun _ : Fin n => dirichletForm K) →L[ℝ]
      PiLp 2 (fun _ : Fin n => dirichletValue K) :=
  dirichletVectorLowerOrder hK (rawCutoffFirstComponent D η hη) (rawCutoffZeroComponent D η hη)

theorem exists_raw_slab_lower_form_bound {J I : Set ℝ} (F : RicciFlow n V J)
    (hI : IsCompact I) (hIJ : I ⊆ J) {K : Set V} (hK : IsClosed K)
    (η : 𝓢(V, ℝ)) (hη : HasCompactSupport η) (hη1 : ∀ x, ‖η x‖ ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ t ∈ I, ‖rawLowerFormOperator (F.connection t) hK η hη‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := exists_raw_slab_lower_component_bound F hI hIJ hη
  have hcut {f : V → ℝ} (hf : ∀ x ∈ tsupport η, ‖f x‖ ≤ C) (x : V) :
      ‖η x * f x‖ ≤ C := by
    by_cases hx : η x = 0
    · simpa only [hx, zero_mul, norm_zero] using hC.le
    · rw [norm_mul]
      exact (mul_le_mul (hη1 x) (hf x (subset_closure hx)) (norm_nonneg _) zero_le_one).trans_eq
        (one_mul C)
  refine ⟨((n : ℝ) ^ 2 * ((n : ℝ) + 1) + 1) * C, by positivity, ?_⟩
  intro t ht
  have hB (k j i : Fin n) (x : V) : ‖rawCutoffFirstComponent (F.connection t) η hη k j i x‖ ≤ C :=
    hcut (fun y hy => (hb t ht y hy).1 k j i) x
  have hZ (k j : Fin n) (x : V) : ‖rawCutoffZeroComponent (F.connection t) η hη k j x‖ ≤ C :=
    hcut (fun y hy => (hb t ht y hy).2 k j) x
  exact (norm_dirichletVectorLowerOrder_le hK _ _ hC.le hB hZ).trans (by nlinarith only [hC.le])

end PoincareConjecture.M35.Uniqueness.Heat
