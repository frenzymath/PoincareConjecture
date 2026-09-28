import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.VariableModulusReplacement
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.CircleConeComparison

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
local notation "S" => interior m64AnnulusDomain

theorem M64ObservedWeakAnnulus.weighted_circle_energy_comparison
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (g : RiemannianMetric n M) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (hei : IsClosedEmbedding e) (hread : M60.SUChartReadable (n := n) e)
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (hQ : Continuous Q) (hpos : ∀ q v, 0 ≤ Q q v v)
    {modulus : ℝ} (hmodulus : 0 < modulus)
    (hmin : ∀ W : M64ObservedWeakAnnulus (n := n) e c0 c1,
      A.weightedEnergy Q modulus ≤ W.weightedEnergy Q modulus) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : LoopPlane) (rho : ℝ), 0 < rho →
      Metric.closedBall a rho ⊆ S →
      ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) 1),
        A.diskEnergy Q a (rho * Real.exp (-s)) ≤ C * A.angularEnergy a rho s := by
  let : TopologicalSpace.PseudoMetrizableSpace M :=
    hei.isEmbedding.isInducing.pseudoMetrizableSpace
  obtain ⟨epsilon, hepsilon, C0, hC0, hfill⟩ :=
    m64ChartReadable_uniform_H1_cone_energy g e he hei.isEmbedding hread Q hQ
  have hbounded : Bornology.IsBounded (range Q) := (isCompact_range hQ).isBounded
  obtain ⟨K, hK⟩ := hbounded.exists_norm_le
  have hbound (q : M) : ‖Q q‖ ≤ K := hK _ (mem_range_self q)
  let D := (max modulus modulus⁻¹) ^ 2
  have hD : 0 ≤ D := sq_nonneg _
  have hE := A.energy_nonneg Q hpos
  let C := D * C0 + A.energy Q / epsilon + 1
  have hC : 0 < C := by dsimp only [C]; positivity
  have hCC : D * C0 ≤ C := by dsimp only [C]; linarith [div_nonneg hE hepsilon.le]
  have hEC : A.energy Q / epsilon ≤ C := by
    dsimp only [C]
    linarith [mul_nonneg hD hC0]
  refine ⟨C, hC, ?_⟩
  intro a rho hrho hKS
  have hcircles := A.local_circle_traces hei a hrho hKS
  have hgreens := m64WeakMap_local_circle_green isOpen_interior a hrho hKS
    (e ∘ A.map) (fun i p => A.column i p) A.observed_memLp
    (fun i => Lp.memLp (A.column i)) A.weak_partial
  filter_upwards [hcircles, hgreens, ae_restrict_mem measurableSet_Icc] with s hcircle hgreen hs
  let r := rho * Real.exp (-s)
  let v := fun x => m64MorreyPolarAngularColumn a rho (fun i p => A.column i p)
    (annulusPoint x s)
  have hr : 0 < r := mul_pos hrho (Real.exp_pos _)
  have hrrho : r ≤ rho := mul_le_of_le_one_right hrho.le
    (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hs.1))
  have hball : Metric.ball a r ⊆ S :=
    Metric.ball_subset_closedBall.trans ((Metric.closedBall_subset_closedBall hrrho).trans hKS)
  have hang : 0 ≤ A.angularEnergy a rho s := A.angularEnergy_nonneg a rho s
  by_cases hsmall : A.angularEnergy a rho s < epsilon
  · obtain ⟨gamma, w, hgc, hgp, hga, hv, -, -, hw, hwp, huni, hder⟩ := hcircle
    have hvp : Function.Periodic v curvePeriod :=
      m64MorreyPolarAngularColumn_periodic a rho (fun i p => A.column i p) s
    have hUp : Function.Periodic (e ∘ gamma) curvePeriod :=
      fun x => congrArg e (hgp x)
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
    have hmatching (phi : LoopPlane → ℝ) (hphi : ContDiff ℝ 1 phi) (i : Fin 2) :
        (∫ p in Metric.ball a r, phi p • B.affineColumn a r i p) +
          (∫ p in Metric.ball a r, fderiv ℝ phi p (EuclideanSpace.single i 1) •
            e (B.affineMap a r p)) =
        (∫ p in Metric.ball a r, phi p • A.column i p) +
          (∫ p in Metric.ball a r, fderiv ℝ phi p (EuclideanSpace.single i 1) •
            e (A.map p)) := by
      have hBgreen := B.affine_green a hr phi hphi i
      rw [m64CircleIntegral_shift] at hBgreen
      simp only [sub_add_cancel] at hBgreen
      have hAgreen := hgreen phi hphi i
      have hnull := M60.haar_ball_ae_eq_closedBall volume a r
      rw [← setIntegral_congr_set hnull, ← setIntegral_congr_set hnull] at hAgreen
      refine hBgreen.trans ((congrArg (fun z => r • z) (integral_congr_ae ?_)).trans
        hAgreen.symm)
      filter_upwards [hga] with x hx
      change gamma x = A.map (a + r • angularPoint (x - Real.pi)) at hx
      rw [hx]
      rfl
    have hlocal := A.weighted_local_energy_le_of_matching_flux Q hQ hei.isEmbedding hbound
      hpos hmodulus hmin measurableSet_ball hball (B.affineMap a r)
      (B.affine_continuous a r).aestronglyMeasurable (B.affineColumn a r)
      (B.affine_column_memLp a hr) (B.affine_memLp a hr) (B.affine_tangent a hr) hmatching
    rw [B.affine_energy a hr Q] at hlocal
    have hBE' : B.energy Q ≤ C0 * A.angularEnergy a rho s := by
      simpa +instances only [hEshift, M64ObservedWeakAnnulus.angularEnergy, v] using! hBE
    calc
      _ ≤ D * B.energy Q := hlocal
      _ ≤ D * (C0 * A.angularEnergy a rho s) := mul_le_mul_of_nonneg_left hBE' hD
      _ = (D * C0) * A.angularEnergy a rho s := by ring
      _ ≤ C * A.angularEnergy a rho s := mul_le_mul_of_nonneg_right hCC hang
  · have hlarge : epsilon ≤ A.angularEnergy a rho s := le_of_not_gt hsmall
    calc
      _ ≤ A.energy Q := A.diskEnergy_le_energy Q hQ hei.isEmbedding hbound hpos a r hball
      _ = (A.energy Q / epsilon) * epsilon := (div_mul_cancel₀ _ hepsilon.ne').symm
      _ ≤ (A.energy Q / epsilon) * A.angularEnergy a rho s :=
        mul_le_mul_of_nonneg_left hlarge (div_nonneg hE hepsilon.le)
      _ ≤ C * A.angularEnergy a rho s := mul_le_mul_of_nonneg_right hEC hang

end PoincareConjecture
