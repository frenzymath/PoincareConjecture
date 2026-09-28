import PoincareConjecture.Proofs.M64.Mathlib.QuadraticSystemRegularity
import PoincareConjecture.Proofs.M64.Mathlib.WeakPartialSchwartz
import Mathlib.MeasureTheory.SpecificCodomains.WithLp












set_option autoImplicit false
set_option warningAsError true

noncomputable section

open Set Metric MeasureTheory Filter
open scoped ContDiff SchwartzMap LineDeriv InnerProductSpace

namespace PoincareConjecture

open EuclideanTranslationNative Poincare.Analysis.Sobolev.Weak






theorem m64QuadraticWeakMap_contDiffOn {N : ℕ}
    (u : LoopPlane → EuclideanSpace ℝ (Fin N))
    (V : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin N))
    (f : Fin N → LoopPlane → ℝ)
    (hu : Continuous u) (huc : HasCompactSupport u)
    (hV : ∀ i, MemLp (V i) 2 volume) (hVc : ∀ i, HasCompactSupport (V i))
    (hweak : ∀ j i, HasWeakPartialDeriv i (fun z => V i z j) (fun z => u z j) univ)
    (hf : ∀ j, Integrable (f j)) {U : Set LoopPlane} (hU : IsOpen U)
    {S : ℝ} (hfs : ∀ j, Function.support (f j) ⊆ closedBall (0 : LoopPlane) S)
    (heq : ∀ j (φ : LoopPlane → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → tsupport φ ⊆ U →
      (∫ z, ∑ i : Fin 2, V i z j * fderiv ℝ φ z (EuclideanSpace.single i 1)) =
        -(∫ z, f j z * φ z))
    {C H β : ℝ} (hC : 0 ≤ C) (hH : 0 ≤ H) (hβ : 0 < β)
    (hgrowth : ∀ j, ∀ᵐ z ∂volume, z ∈ U →
      |f j z| ≤ C * (∑ k : Fin N, ∑ i : Fin 2, (V i z k) ^ 2))
    (hholder : ∀ x ∈ U, ∀ z ∈ U, ∀ j, |u z j - u x j| ≤ H * ‖z - x‖ ^ β)
    (hdecay : ∀ p ∈ U, ∃ Λ ≥ 0, ∃ R > 0,
      ∀ x ∈ ball p R, ∀ r : ℝ, 0 < r → r ≤ R →
        (∫ z in closedBall x r, ∑ j : Fin N, ∑ i : Fin 2, (V i z j) ^ 2) ≤
          Λ * r ^ (2 * β)) :
    ContDiffOn ℝ 1 u U := by
  have huL (j : Fin N) : MemLp (fun z => u z j) 2 volume :=
    (hu.memLp_of_hasCompactSupport huc).eval_piLp j
  have hVL (j : Fin N) (i : Fin 2) : MemLp (fun z => V i z j) 2 volume :=
    (hV i).eval_piLp j
  let a : Fin N → ScalarL2 2 := fun j => (huL j).toLp (fun z => u z j)
  let d : Fin N → Fin 2 → ScalarL2 2 := fun j i => (hVL j i).toLp (fun z => V i z j)
  have ha (j : Fin N) : (a j : LoopPlane → ℝ) =ᵐ[volume] fun z => u z j :=
    (huL j).coeFn_toLp
  have hd : ∀ᵐ z ∂volume, ∀ j i, d j i z = V i z j :=
    ae_all_iff.mpr fun j => ae_all_iff.mpr fun i => (hVL j i).coeFn_toLp
  have henergy : (fun z => ∑ j : Fin N, ∑ i : Fin 2, (d j i z) ^ 2) =ᵐ[volume]
      (fun z => ∑ j : Fin N, ∑ i : Fin 2, (V i z j) ^ 2) := by
    filter_upwards [hd] with z hz
    simp only [hz]
  obtain ⟨B, hB⟩ := huc.isCompact.exists_bound_of_continuousOn hu.continuousOn
  have hub (z : LoopPlane) : ‖u z‖ ≤ max B 0 := by
    by_cases hz : z ∈ tsupport u
    · exact (hB z hz).trans (le_max_left B 0)
    · rw [image_eq_zero_of_notMem_tsupport hz, norm_zero]
      exact le_max_right B 0
  refine m64QuadraticSystem_contDiffOn a d f u hf hU hfs ?_ ?_
    (B := max B 0) hC hH hβ ?_ ?_
    hu.continuousOn (fun j => ae_restrict_of_ae (ha j)) hholder ?_
  · intro j i φ
    exact (hweak j i).inner_toLp_schwartz (huL j) (hVL j i)
      (huc.comp_left (g := fun v : EuclideanSpace ℝ (Fin N) => v j) rfl)
      ((hVc i).comp_left (g := fun v : EuclideanSpace ℝ (Fin N) => v j) rfl) φ
  · intro j φ hφc hφU
    have hpair (i : Fin 2) :
        ⟪d j i, (∂_{EuclideanSpace.single i (1 : ℝ)} φ).toLp 2 volume⟫_ℝ =
          ∫ z, V i z j * fderiv ℝ φ z (EuclideanSpace.single i 1) := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [(hVL j i).coeFn_toLp,
        (∂_{EuclideanSpace.single i (1 : ℝ)} φ).coeFn_toLp 2 volume] with z hz hφz
      simp only [d, hz, hφz, Real.inner_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv]
    calc
      _ = ∑ i : Fin 2, ∫ z, V i z j * fderiv ℝ φ z (EuclideanSpace.single i 1) :=
        Finset.sum_congr rfl fun i _ => hpair i
      _ = ∫ z, ∑ i : Fin 2, V i z j * fderiv ℝ φ z (EuclideanSpace.single i 1) := by
        apply (integral_finsetSum _ _).symm
        intro i _
        simpa +instances only [Pi.mul_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv] using!
          (hVL j i).integrable_mul
            ((∂_{EuclideanSpace.single i (1 : ℝ)} φ).memLp 2 volume)
      _ = _ := heq j φ (φ.smooth ⊤) hφc hφU
  · intro j
    filter_upwards [hgrowth j, henergy] with z hz he hzU
    rw [he]
    exact hz hzU
  · intro j
    filter_upwards [ha j] with z hz
    rw [hz]
    exact (PiLp.norm_apply_le (u z) j).trans (hub z)
  · intro p hp
    obtain ⟨Λ, hΛ, R, hR, hlocal⟩ := hdecay p hp
    refine ⟨Λ, hΛ, R, hR, ?_⟩
    intro x hx r hr hrR
    rw [integral_congr_ae (ae_restrict_of_ae henergy)]
    exact hlocal x hx r hr hrR

end PoincareConjecture
