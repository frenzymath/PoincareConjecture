import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeakStrongCompactness
import PoincareConjecture.Proofs.M03.Existence.LpFiniteCoordinatesNative
import PoincareConjecture.Proofs.M03.Existence.FiniteLocalizationCompactnessNative











set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace PoincareConjecture

open Poincare.Analysis.Sobolev.Weak

variable {m : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S



theorem m64Annulus_weak_vector_l2_isCompact
    (u : ℕ → LoopPlane → E) (V : ℕ → Fin 2 → LoopPlane → E)
    (hu : ∀ j, MemLp (u j) 2 mu) (hV : ∀ j i, MemLp (V j i) 2 mu)
    (hweak : ∀ j i b, HasWeakPartialDeriv i (fun p => V j i p b) (fun p => u j p b) S)
    {A C : ℝ} (hA : ∀ j p, ‖u j p‖ ≤ A)
    (hC : ∀ j i, (∫ p in S, ‖V j i p‖ ^ 2) ≤ C) :
    ∃ hU : ∀ j, MemLp ((S).indicator (u j)) 2 volume,
      IsCompact (closure (range (fun j => (hU j).toLp ((S).indicator (u j))))) := by
  have hS : MeasurableSet S := isOpen_interior.measurableSet
  have hU (j : ℕ) : MemLp ((S).indicator (u j)) 2 volume :=
    (memLp_indicator_iff_restrict hS).mpr (hu j)
  let W (b : Fin m) (j : ℕ) : MemW1pWitness 2 (fun p => u j p b) S :=
    { memLp := (EuclideanSpace.proj (𝕜 := ℝ) b).comp_memLp' (hu j)
      weakGrad := fun p => WithLp.toLp 2 (fun i => V j i p b)
      weakGrad_component_memLp := fun i =>
        (EuclideanSpace.proj (𝕜 := ℝ) b).comp_memLp' (hV j i)
      isWeakGrad := fun i => hweak j i b }
  have hcoord (b : Fin m) :
      ∃ hU : ∀ j, MemLp ((S).indicator (fun p => u j p b)) 2 volume,
        IsCompact (closure (range (fun j => (hU j).toLp
          ((S).indicator (fun p => u j p b))))) := by
    apply m64Annulus_weak_l2_isCompact (fun j p => u j p b) (W b) (C := C)
      (fun j p => (PiLp.norm_apply_le (u j p) b).trans (hA j p))
    intro j i
    change (∫ p in S, (V j i p b) ^ 2) ≤ C
    apply le_trans _ (hC j i)
    apply integral_mono ((W b j).weakGrad_component_memLp i).integrable_sq
      ((memLp_two_iff_integrable_sq_norm (hV j i).aestronglyMeasurable).mp (hV j i))
    intro p
    simpa only [Real.norm_eq_abs, sq_abs] using
      (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (PiLp.norm_apply_le (V j i p) b)
  choose hcoordLp hcompact using hcoord
  have heq (b : Fin m) (j : ℕ) :
      LpFiniteCoordinatesNative.coordinateLp volume b ((hU j).toLp ((S).indicator (u j))) =
        (hcoordLp b j).toLp ((S).indicator (fun p => u j p b)) := by
    apply Lp.ext
    filter_upwards [LpFiniteCoordinatesNative.coordinateLp_toLp_coe volume b (hU j),
      (hcoordLp b j).coeFn_toLp] with p hp hq
    rw [hp, hq]
    by_cases hpS : p ∈ S <;> simp [hpS]
  refine ⟨hU, FiniteLocalizationCompactnessNative.isCompact_closure_of_finite_reconstruction
    (fun b v => LpFiniteCoordinatesNative.coordinateLp volume b v)
    (fun b => LpFiniteCoordinatesNative.insertionLp volume b) ?_ ?_⟩
  · intro b
    apply (hcompact b).totallyBounded.subset
    rintro _ ⟨v, ⟨j, rfl⟩, rfl⟩
    exact subset_closure ⟨j, (heq b j).symm⟩
  · intro v _
    exact LpFiniteCoordinatesNative.sum_insertion_coordinate volume v

end PoincareConjecture
