import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusSeamLocalEnergy
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.H1CircleShift
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.LocalConeUniformH1
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.LocalConeRescaled













set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped Topology Manifold ContDiff

namespace PoincareConjecture

open Proofs.M58

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [CompactSpace M] [T2Space M]
  {e : M → EuclideanSpace ℝ (Fin m)} {c0 c1 : ℝ → M}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "O" => m64AnnulusSeamDomain



theorem M64ObservedWeakAnnulus.seam_circle_energy_comparison
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (g : RiemannianMetric n M) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (hei : IsClosedEmbedding e) (hread : M60.SUChartReadable (n := n) e)
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (hQ : Continuous Q) (hpos : ∀ q w, 0 ≤ Q q w w)
    (hmin : ∀ B : M64ObservedWeakAnnulus (n := n) e c0 c1, A.energy Q ≤ B.energy Q) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : LoopPlane) (rho : ℝ), 0 < rho →
      2 * rho < curvePeriod → Metric.closedBall a rho ⊆ O →
      ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) 1),
        A.seamDiskEnergy Q a (rho * Real.exp (-s)) ≤ C * A.seamAngularEnergy a rho s := by
  let : TopologicalSpace.PseudoMetrizableSpace M :=
    hei.isEmbedding.isInducing.pseudoMetrizableSpace
  obtain ⟨epsilon, hepsilon, C0, hC0, hfill⟩ :=
    m64ChartReadable_uniform_H1_cone_energy g e he hei.isEmbedding hread Q hQ
  have hbounded : Bornology.IsBounded (range Q) := (isCompact_range hQ).isBounded
  obtain ⟨K, hK⟩ := hbounded.exists_norm_le
  have hbound (q : M) : ‖Q q‖ ≤ K := hK _ (mem_range_self q)
  have hE := A.energy_nonneg Q hpos
  let C := C0 + 2 * A.energy Q / epsilon + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hCC : C0 ≤ C := by
    dsimp [C]
    linarith [div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hE) hepsilon.le]
  have hEC : 2 * A.energy Q / epsilon ≤ C := by dsimp [C]; linarith
  refine ⟨C, hC, ?_⟩
  intro a rho hrho hwidth hKO
  have hcircles := A.seam_local_circle_traces hei a hrho hKO
  have hgreens := A.seam_local_circle_green a hrho hKO
  filter_upwards [hcircles, hgreens, ae_restrict_mem measurableSet_Icc] with s hcircle hgreen hs
  let r := rho * Real.exp (-s)
  let v := fun x => m64MorreyPolarAngularColumn a rho
    (fun i => m64AnnulusSeamExtend (A.column i : LoopPlane → E)) (annulusPoint x s)
  have hr : 0 < r := mul_pos hrho (Real.exp_pos _)
  have hrrho : r ≤ rho := mul_le_of_le_one_right hrho.le
    (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hs.1))
  have hsmallO : Metric.closedBall a r ⊆ O :=
    (Metric.closedBall_subset_closedBall hrrho).trans hKO
  have hball : Metric.ball a r ⊆ O := Metric.ball_subset_closedBall.trans hsmallO
  have hang := A.seamAngularEnergy_nonneg a rho s
  by_cases hsmall : A.seamAngularEnergy a rho s < epsilon
  · obtain ⟨gamma, w, hgc, hgp, hga, hv, -, -, hw, hwp, huni, hder⟩ := hcircle
    have hvp : Function.Periodic v curvePeriod :=
      m64MorreyPolarAngularColumn_periodic a rho
        (fun i => m64AnnulusSeamExtend (A.column i : LoopPlane → E)) s
    have hUp : Function.Periodic (e ∘ gamma) curvePeriod := fun x => congrArg e (hgp x)
    obtain ⟨hva, hunia, hdera, hFTCa, hEshift⟩ :=
      m64Periodic_H1_shift w hw hwp (e ∘ gamma) v hUp hvp hv huni hder Real.pi
    have hwa (j : ℕ) : ContDiff ℝ 1 (fun x => w j (x + Real.pi)) :=
      (hw j).comp (contDiff_id.add contDiff_const)
    have hshiftSmall : (∫ x in Icc (0 : ℝ) curvePeriod, ‖v (x + Real.pi)‖ ^ 2) < epsilon := by
      rw [hEshift]
      exact hsmall
    obtain ⟨B, hBE⟩ := hfill (fun x => gamma (x + Real.pi))
      (hgc.comp (continuous_id.add continuous_const)) (hgp.add_const Real.pi)
      (fun j x => w j (x + Real.pi)) hwa (fun j => (hwp j).add_const Real.pi)
      hunia (fun x => v (x + Real.pi)) hva
      (by simpa +instances only [Function.comp_def, zero_add] using! hFTCa) hdera hshiftSmall
    have hnull := M60.haar_ball_ae_eq_closedBall volume a r
    have hmu := Measure.restrict_congr_set hnull
    have hmatching (phi : LoopPlane → ℝ) (hphi : ContDiff ℝ 1 phi) (i : Fin 2) :
        (∫ p in Metric.closedBall a r, phi p • B.affineColumn a r i p) +
          (∫ p in Metric.closedBall a r, fderiv ℝ phi p (EuclideanSpace.single i 1) •
            e (B.affineMap a r p)) =
        (∫ p in Metric.closedBall a r,
          phi p • m64AnnulusSeamExtend (A.column i : LoopPlane → E) p) +
          (∫ p in Metric.closedBall a r, fderiv ℝ phi p (EuclideanSpace.single i 1) •
            e (m64AnnulusSeamExtend A.map p)) := by
      have hBgreen := B.affine_green a hr phi hphi i
      rw [m64CircleIntegral_shift] at hBgreen
      simp only [sub_add_cancel] at hBgreen
      rw [setIntegral_congr_set hnull, setIntegral_congr_set hnull] at hBgreen
      refine hBgreen.trans ((congrArg (fun z => r • z) (integral_congr_ae ?_)).trans
        (hgreen phi hphi i).symm)
      filter_upwards [hga] with x hx
      change gamma x = m64AnnulusSeamExtend A.map (a + r • angularPoint (x - Real.pi)) at hx
      rw [hx]
    have hVl (i : Fin 2) : MemLp (B.affineColumn a r i) 2
        (volume.restrict (Metric.closedBall a r)) := by
      rw [← hmu]
      exact B.affine_column_memLp a hr i
    have hfl : MemLp (e ∘ B.affineMap a r) 2 (volume.restrict (Metric.closedBall a r)) := by
      rw [← hmu]
      exact B.affine_memLp a hr
    have hft (i : Fin 2) : ∀ᵐ p ∂volume.restrict (Metric.closedBall a r),
        B.affineColumn a r i p ∈ range (mfderiv (𝓡 n) (𝓡 m) e (B.affineMap a r p)) := by
      rw [← hmu]
      exact B.affine_tangent a hr i
    have hlocal := A.seam_local_energy_le_of_matching_flux Q hQ hei.isEmbedding hbound hmin
      (isCompact_closedBall a r) hsmallO
      (m64AnnulusSeamDisk_disjoint a (r := r) (by linarith))
      (B.affineMap a r) (B.affine_continuous a r).aestronglyMeasurable
      (B.affineColumn a r) hVl hfl hft hmatching
    rw [← setIntegral_congr_set hnull, ← setIntegral_congr_set hnull,
      B.affine_energy a hr Q] at hlocal
    have hBE' : B.energy Q ≤ C0 * A.seamAngularEnergy a rho s := by
      simpa +instances only [hEshift, M64ObservedWeakAnnulus.seamAngularEnergy, v] using! hBE
    exact (hlocal.trans hBE').trans (mul_le_mul_of_nonneg_right hCC hang)
  · have hlarge : epsilon ≤ A.seamAngularEnergy a rho s := le_of_not_gt hsmall
    calc
      _ ≤ 2 * A.energy Q := A.seamDiskEnergy_le_energy Q hQ hei.isEmbedding hbound hpos a r hball
      _ = (2 * A.energy Q / epsilon) * epsilon := (div_mul_cancel₀ _ hepsilon.ne').symm
      _ ≤ (2 * A.energy Q / epsilon) * A.seamAngularEnergy a rho s :=
        mul_le_mul_of_nonneg_left hlarge (div_nonneg (by positivity) hepsilon.le)
      _ ≤ C * A.seamAngularEnergy a rho s := mul_le_mul_of_nonneg_right hEC hang

end PoincareConjecture
