import PoincareConjecture.Proofs.M64.Mathlib.QuadraticWeakMapRegularity
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryReflectedEnergy
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryReflectedHolder
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryOddReflection

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open Set Metric MeasureTheory Filter Function
open scoped ContDiff
open Poincare.Analysis.Sobolev.Weak
open Poincare.Analysis.Sobolev.BoundaryExtension
open Poincare.Analysis.Sobolev.BoundaryTangential

namespace PoincareConjecture

theorem m64MixedBoundary_quadratic_contDiffOn {N : ℕ}
    (u : LoopPlane → EuclideanSpace ℝ (Fin N))
    (V : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin N))
    (b : Fin N → LoopPlane → ℝ)
    (epsilon : Fin N → ℝ) (hepsilon : ∀ j, epsilon j ^ 2 = 1)
    (hu : Continuous u) (huc : HasCompactSupport u)
    (hV : ∀ i, MemLp (V i) 2 (volume.restrict (halfSpace 2)))
    (hVc : ∀ i, HasCompactSupport (V i))
    (hweak : ∀ j i, HasWeakPartialDeriv i (fun p => V i p j) (fun p => u p j) (halfSpace 2))
    (hface : ∀ j p, p 0 = 0 → u p j = epsilon j * u p j)
    (hb : ∀ j, IntegrableOn (b j) (halfSpace 2))
    {S : ℝ} (hbs : ∀ j, support (b j) ⊆ closedBall (0 : LoopPlane) S)
    {R : ℝ}
    (heq : ∀ j (φ : LoopPlane → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → tsupport φ ⊆ ball (0 : LoopPlane) R →
      (epsilon j = -1 → ∀ p : LoopPlane, p 0 = 0 → φ p = 0) →
      (∫ p in halfSpace 2, ∑ i : Fin 2, V i p j *
        fderiv ℝ φ p (EuclideanSpace.single i 1)) = ∫ p in halfSpace 2, b j p * φ p)
    {C H β Λ rho : ℝ} (hC : 0 ≤ C) (hH : 0 ≤ H) (hβ : 0 < β)
    (hΛ : 0 ≤ Λ) (hrho : 0 < rho)
    (hgrowth : ∀ j, ∀ᵐ p ∂volume.restrict (halfSpace 2), p ∈ ball (0 : LoopPlane) R →
      |b j p| ≤ C * ∑ k : Fin N, ∑ i : Fin 2, (V i p k) ^ 2)
    (hholder : ∀ j x, x ∈ ball (0 : LoopPlane) R → 0 ≤ x 0 →
      ∀ y ∈ ball (0 : LoopPlane) R, 0 ≤ y 0 → |u x j - u y j| ≤ H * ‖x - y‖ ^ β)
    (henergy : ∀ x ∈ ball (0 : LoopPlane) R, ∀ r ∈ Ioc (0 : ℝ) rho,
      (∫ p in closedBall x r, ∑ j : Fin N, ∑ i : Fin 2,
        (halfSpace 2).indicator (fun q => V i q j) p ^ 2) ≤ Λ * r ^ (2 * β)) :
    ContDiffOn ℝ 1 u (ball (0 : LoopPlane) R ∩ {p : LoopPlane | 0 ≤ p 0}) := by
  classical
  let U : LoopPlane → EuclideanSpace ℝ (Fin N) := fun p =>
    WithLp.toLp 2 (fun j => m64ContinuousBoundaryReflect (epsilon j) (fun q => u q j) p)
  let W : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin N) := fun i p =>
    WithLp.toLp 2 (fun j =>
      m64BoundaryReflect (epsilon j * coordinateSign i) (fun q => V i q j) p)
  let f : Fin N → LoopPlane → ℝ := fun j p => -m64BoundaryReflect (epsilon j) (b j) p
  have hcompact {v w : LoopPlane → EuclideanSpace ℝ (Fin N)}
      (hv : HasCompactSupport v)
      (hz : ∀ p, v p = 0 → v (reflect p) = 0 → w p = 0) : HasCompactSupport w := by
    apply HasCompactSupport.intro
      (hv.isCompact.union (hv.comp_homeomorph reflect.toHomeomorph).isCompact)
    intro p hp
    exact hz p (image_eq_zero_of_notMem_tsupport (fun h => hp (Or.inl h)))
      (image_eq_zero_of_notMem_tsupport (f := v ∘ reflect.toHomeomorph)
        (fun h => hp (Or.inr h)))
  have hUc : HasCompactSupport U := by
    apply hcompact huc
    intro p hp hr
    ext j
    change m64ContinuousBoundaryReflect (epsilon j) (fun q => u q j) p = 0
    simp only [m64ContinuousBoundaryReflect, hp, hr, PiLp.zero_apply, mul_zero, ite_self]
  have hWc (i : Fin 2) : HasCompactSupport (W i) := by
    apply hcompact (hVc i)
    intro p hp hr
    ext j
    change m64BoundaryReflect (epsilon j * coordinateSign i) (fun q => V i q j) p = 0
    simp only [m64BoundaryReflect, indicator_apply, hp, hr, PiLp.zero_apply,
      ite_self, mul_zero, add_zero]
  have hU : Continuous U := by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin N => ℝ)).comp
    exact continuous_pi fun j => m64ContinuousBoundaryReflect_continuous
      ((EuclideanSpace.proj j).continuous.comp hu) (epsilon j) (hface j)
  have huL (j : Fin N) : MemLp (fun p => u p j) 2 (volume.restrict (halfSpace 2)) :=
    ((hu.memLp_of_hasCompactSupport huc).eval_piLp j).restrict (halfSpace 2)
  have hVL (j : Fin N) (i : Fin 2) :
      MemLp (fun p => V i p j) 2 (volume.restrict (halfSpace 2)) := (hV i).eval_piLp j
  have hWL (i : Fin 2) : MemLp (W i) 2 volume :=
    MemLp.of_eval_piLp fun j => m64BoundaryReflect_memLp (hVL j i) _
  have hWweak (j : Fin N) (i : Fin 2) :
      HasWeakPartialDeriv i (fun p => W i p j) (fun p => U p j) univ := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp
      (show epsilon j ^ 2 = (1 : ℝ) ^ 2 by simpa using hepsilon j) with hj | hj
    · simpa only [U, W, hj, one_mul] using
        m64EvenBoundaryReflect_weak i (huL j) (hVL j i) (hweak j i)
    · have hz (p : LoopPlane) (hp : p 0 = 0) : u p j = 0 := by
        have hh := hface j p hp
        rw [hj] at hh
        linarith
      simpa only [U, W, hj, neg_one_mul] using! m64OddBoundaryReflect_weak
        (u := fun p => u p j) (v := fun p => V i p j) i
        ((EuclideanSpace.proj j).continuous.comp hu) hz (huL j) (hVL j i) (hweak j i)
  have hf (j : Fin N) : Integrable (f j) :=
    (m64BoundaryReflect_integrable (hb j) (epsilon j)).neg
  have hfs (j : Fin N) : support (f j) ⊆ closedBall (0 : LoopPlane) S := by
    intro p hp
    by_contra hn
    have hrn : reflect p ∉ closedBall (0 : LoopPlane) S := by
      simpa only [mem_closedBall_zero_iff, LinearIsometryEquiv.norm_map] using hn
    have hp0 : b j p = 0 := notMem_support.mp (fun h => hn (hbs j h))
    have hr0 : b j (reflect p) = 0 := notMem_support.mp (fun h => hrn (hbs j h))
    exact hp (by simp only [f, m64BoundaryReflect, indicator_apply, hp0, hr0,
      ite_self, mul_zero, add_zero, neg_zero])
  have heqR (j : Fin N) (φ : LoopPlane → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
      (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ ball (0 : LoopPlane) R) :
      (∫ p, ∑ i : Fin 2, W i p j * fderiv ℝ φ p (EuclideanSpace.single i 1)) =
        -(∫ p, f j p * φ p) := by
    simpa only [W, f, neg_mul, integral_neg, neg_neg] using
      m64HalfSpace_mixed_equation_reflect_of_one_le le_rfl (hVL j)
        (memLp_one_iff_integrable.mpr (hb j)) (heq j) φ hφ hφc hφs
  have hgR : ∀ j, ∀ᵐ p ∂volume, p ∈ ball (0 : LoopPlane) R →
      |f j p| ≤ C * ∑ k : Fin N, ∑ i : Fin 2, (W i p k) ^ 2 := by
    simpa only [f, W, abs_neg] using
      m64BoundaryReflect_quadratic_growth epsilon hepsilon (fun j i p => V i p j) b hgrowth
  have hHR : ∀ x ∈ ball (0 : LoopPlane) R, ∀ z ∈ ball (0 : LoopPlane) R, ∀ j,
      |U z j - U x j| ≤ (3 * H) * ‖z - x‖ ^ β := by
    intro x hx z hz j
    exact m64ContinuousBoundaryReflect_holder (hepsilon j) hH hβ.le
      (fun p _ hp => hface j p hp) (hholder j) z hz x hx
  have hER : ∀ p ∈ ball (0 : LoopPlane) R, ∃ L ≥ 0, ∃ r0 > 0,
      ∀ x ∈ ball p r0, ∀ r : ℝ, 0 < r → r ≤ r0 →
        (∫ z in closedBall x r, ∑ j : Fin N, ∑ i : Fin 2, (W i z j) ^ 2) ≤
          L * r ^ (2 * β) := by
    intro p hp
    have hpR : ‖p‖ < R := mem_ball_zero_iff.mp hp
    let r0 := min rho ((R - ‖p‖) / 2)
    have hr0 : 0 < r0 := lt_min hrho (half_pos (sub_pos.mpr hpR))
    refine ⟨2 * Λ, by positivity, r0, hr0, ?_⟩
    intro x hx r hr hrr
    have hxR : x ∈ ball (0 : LoopPlane) R := by
      have hxp : ‖x - p‖ < r0 := mem_ball_iff_norm.mp hx
      have hn : ‖x‖ ≤ ‖x - p‖ + ‖p‖ := by
        simpa only [sub_add_cancel] using norm_add_le (x - p) p
      rw [mem_ball_zero_iff]
      have hsmall : r0 ≤ (R - ‖p‖) / 2 := min_le_right _ _
      linarith
    have hxr : reflect x ∈ ball (0 : LoopPlane) R := by
      simpa only [mem_ball_zero_iff, LinearIsometryEquiv.norm_map] using hxR
    have hrrho : r ≤ rho := hrr.trans (min_le_left _ _)
    change (∫ z in closedBall x r, ∑ j : Fin N, ∑ i : Fin 2,
      m64BoundaryReflect (epsilon j * coordinateSign i) (fun q => V i q j) z ^ 2) ≤ _
    rw [m64BoundaryReflect_integral_energy epsilon hepsilon (fun j i p => V i p j) hVL]
    linarith [henergy x hxR r ⟨hr, hrrho⟩, henergy (reflect x) hxr r ⟨hr, hrrho⟩]
  have hregular := m64QuadraticWeakMap_contDiffOn U W f hU hUc hWL hWc hWweak hf
    isOpen_ball hfs heqR hC (show 0 ≤ 3 * H by positivity) hβ hgR hHR hER
  apply (hregular.mono inter_subset_left).congr
  intro p hp
  ext j
  change u p j = m64ContinuousBoundaryReflect (epsilon j) (fun q => u q j) p
  simp only [m64ContinuousBoundaryReflect, if_pos (show 0 ≤ p 0 from hp.2)]

end PoincareConjecture
