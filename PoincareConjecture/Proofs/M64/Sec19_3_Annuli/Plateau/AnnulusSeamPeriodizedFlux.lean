import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusSeamPullbackTest

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff NNReal

namespace PoincareConjecture

open Poincare.Analysis.Sobolev.Weak

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e : M → EuclideanSpace ℝ (Fin m)} {c0 c1 : ℝ → M}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => m64AnnulusSeamDomain

theorem M64ObservedWeakAnnulus.exists_seam_matching_periodic_circle
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    {O : Set LoopPlane} (hO : IsOpen O) (a : LoopPlane)
    {rho : ℝ} (hrho : 0 < rho) (hKO : Metric.closedBall a rho ⊆ O)
    (hKS : Metric.closedBall a rho ⊆ S)
    (f : LoopPlane → M) (V : Fin 2 → LoopPlane → E)
    (hf : MemLp (e ∘ f) 2 (volume.restrict O))
    (hV : ∀ i, MemLp (V i) 2 (volume.restrict O))
    (hw : ∀ i b, HasWeakPartialDeriv i (fun p => V i p b) (fun p => e (f p) b) O)
    (hmatch : ∀ p : LoopPlane, rho * Real.exp (-1) ≤ dist p a →
      dist p a ≤ rho → f p = m64AnnulusSeamExtend A.map p) :
    ∃ r : ℝ, 0 < r ∧ rho * Real.exp (-1) ≤ r ∧ r ≤ rho ∧
      ∀ phi : LoopPlane → ℝ, ContDiff ℝ 1 phi →
        (∀ s ∈ Icc (0 : ℝ) 1,
          phi (annulusPoint curvePeriod s) = phi (annulusPoint 0 s)) →
        ∀ i : Fin 2,
          (∫ p in Metric.closedBall a r, m64AnnulusSeamExtend phi p • V i p) +
            (∫ p in Metric.closedBall a r,
              m64AnnulusSeamExtend (fun q => fderiv ℝ phi q (EuclideanSpace.single i 1)) p •
                e (f p)) =
          (∫ p in Metric.closedBall a r,
            m64AnnulusSeamExtend phi p • m64AnnulusSeamExtend (A.column i : LoopPlane → E) p) +
            (∫ p in Metric.closedBall a r,
              m64AnnulusSeamExtend (fun q => fderiv ℝ phi q (EuclideanSpace.single i 1)) p •
                e (m64AnnulusSeamExtend A.map p)) := by
  obtain ⟨r, hr, hlo, hhi, hflux⟩ :=
    A.exists_seam_matching_circle_of_outer_agreement hO a hrho hKO hKS f V hf hV hw hmatch
  refine ⟨r, hr, hlo, hhi, ?_⟩
  intro phi hp hseam i
  have hsmall : Metric.closedBall a r ⊆ S :=
    (Metric.closedBall_subset_closedBall hhi).trans hKS
  obtain ⟨psi, L, hL, hc, heq⟩ :=
    m64_exists_compact_lipschitz_seam_test (isCompact_closedBall a r) hsmall hp hseam
  have h := hflux psi L hL hc i
  have hn : ∀ᵐ p ∂volume.restrict (Metric.closedBall a r), p 0 ≠ 0 := by
    apply ae_restrict_of_ae
    apply ae_iff.mpr
    simpa only [not_not] using m64_cut_line_null 0
  have hval (w : LoopPlane → E) : (∫ p in Metric.closedBall a r, psi p • w p) =
      ∫ p in Metric.closedBall a r, m64AnnulusSeamExtend phi p • w p := by
    apply integral_congr_ae
    filter_upwards [hn, ae_restrict_mem Metric.isClosed_closedBall.measurableSet] with p hp0 hpK
    rw [(heq p hpK hp0).1]
    rfl
  have hder (w : LoopPlane → E) :
      (∫ p in Metric.closedBall a r, fderiv ℝ psi p (EuclideanSpace.single i 1) • w p) =
      ∫ p in Metric.closedBall a r,
        m64AnnulusSeamExtend (fun q => fderiv ℝ phi q (EuclideanSpace.single i 1)) p • w p := by
    apply integral_congr_ae
    filter_upwards [hn, ae_restrict_mem Metric.isClosed_closedBall.measurableSet] with p hp0 hpK
    rw [(heq p hpK hp0).2 i]
    rfl
  rw [hval, hder, hval, hder] at h
  exact h

end PoincareConjecture
