import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusRadialBoundaryEnergy
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusRadialUniformPowerGrowth












set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Metric Topology
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.M64ObservedWeakAnnulus

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e : M → EuclideanSpace ℝ (Fin m)} {c0 c1 : ℝ → M}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "O" => m64AnnulusLowerDomain
local notation "L" => m64AnnulusLowerStrip
local notation "v" => m64AnnulusRadialTranslation



theorem lower_extension_column_bound
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (hc0 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 c0)
    (hc0P : Function.Periodic c0 curvePeriod) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ p ∈ O, p 1 < 0 → ∀ i : Fin 2,
      ‖A.lowerExtensionColumn i p‖ ≤ D := by
  have hce : ContDiff ℝ 1 (e ∘ c0) := contMDiff_iff_contDiff.mp (he.comp hc0)
  obtain ⟨D, hD, hbound⟩ := m64Periodic_contDiff_deriv_bound hce
    (fun x => congrArg e (hc0P x))
  refine ⟨D, hD, ?_⟩
  intro p hp hneg i
  have hL : p ∈ L := (m64AnnulusLowerStrip_coordinates p).mpr
    ⟨hp.1, hp.2.1, hp.2.2.1, hneg⟩
  unfold M64ObservedWeakAnnulus.lowerExtensionColumn
  rw [m64AnnulusLowerExtend_left _ _ hL]
  have hcol := m64RadialBoundaryPlane_column hce (0 : LoopPlane) 1 (v + p) i
  fin_cases i
  · have hcol' : fderiv ℝ (fun q : LoopPlane => e (c0 (q 0))) (v + p)
        (EuclideanSpace.single (⟨0, by decide⟩ : Fin 2) 1) = deriv (e ∘ c0) ((v + p) 0) := by
      simpa [Function.comp_apply, Fin.ext_iff] using hcol
    rw [hcol']
    exact hbound ((v + p) 0)
  · have hcol' : fderiv ℝ (fun q : LoopPlane => e (c0 (q 0))) (v + p)
        (EuclideanSpace.single (⟨1, by decide⟩ : Fin 2) 1) = 0 := by
      simpa [Function.comp_apply, Fin.ext_iff] using hcol
    rw [hcol']
    simpa using hD



theorem lower_smooth_column_power_growth
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (hc0 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 c0)
    (hc0P : Function.Periodic c0 curvePeriod) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ a ∈ O, a 1 < 0 → ∀ rho : ℝ, 0 < rho →
      closedBall a (2 * rho) ⊆ L → ∀ b ∈ closedBall a rho,
        ∀ r ∈ Ioc (0 : ℝ) rho, ∀ i : Fin 2,
          (∫ p in ball b r, ‖A.lowerExtensionColumn i p‖ ^ 2) ≤
            (volume (ball b r)).toReal * D ^ 2 := by
  obtain ⟨D, hD, hbound⟩ := A.lower_extension_column_bound he hc0 hc0P
  refine ⟨D, hD, ?_⟩
  intro a ha hapos rho hrho hsub b hb r hr i
  have hba : closedBall b r ⊆ closedBall a (2 * rho) :=
    Metric.closedBall_subset_closedBall'
      (show r + dist b a ≤ 2 * rho from by
        have hba0 := Metric.mem_closedBall.mp hb
        linarith [hba0, hr.2])
  have hball : ball b r ⊆ L :=
    ball_subset_closedBall.trans (hba.trans hsub)
  have hballO : ball b r ⊆ O := hball.trans m64AnnulusLower_strip_subset
  have hLp := ((A.lower_extension_memLp (contMDiff_iff_contDiff.mp (he.comp hc0))).2 i).mono_measure
    (Measure.restrict_mono hballO le_rfl)
  have hi := (memLp_two_iff_integrable_sq_norm hLp.aestronglyMeasurable).mp hLp
  calc
    _ ≤ ∫ _ in ball b r, D ^ 2 := by
      apply integral_mono_ae hi integrableOn_const
      filter_upwards [ae_restrict_mem measurableSet_ball] with p hp
      have hpL : p ∈ L := hball hp
      have hpO : p ∈ O := m64AnnulusLower_strip_subset hpL
      have hpneg : p 1 < 0 :=
        (m64AnnulusLowerStrip_coordinates p).mp hpL |>.2.2.2
      exact sq_le_sq₀ (norm_nonneg _) (by positivity) |>.mpr (hbound p hpO hpneg i)
    _ = _ := by rw [EuclideanSpace.volume_ball_fin_two]; simp [Measure.real, smul_eq_mul]

end PoincareConjecture.M64ObservedWeakAnnulus
