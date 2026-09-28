import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreePhaseTargetCircleTrace
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreePhaseConeWeak
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreePhaseDiskReplacement
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.LocalConeRescaled
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeakAnnulusReplacement
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Stabilization.TwoCircleObservation









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

attribute [local instance] Classical.propDecidable

open Set Filter MeasureTheory Metric Topology
open scoped Manifold ContDiff

namespace PoincareConjecture.M64

open Proofs.M58 Poincare.Analysis.Sobolev.Weak

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference auxiliary : ℝ}

local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S
local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "circleMu" => volume.restrict (Icc (0 : ℝ) curvePeriod)



theorem auxiliaryCircle_free_phase_circle_replacements
    (P : M62.CircleProductData F circumference)
    (Q : M62.CircleProductData P.flow auxiliary)
    {e : Q.charts.Point → E} (he : Continuous e)
    {R : E →L[ℝ] LoopPlane} (hR : ∀ q, R (e q) = planarCircleObservation q.1.2)
    {c0 c1 : ℝ → Q.charts.Point} {H0 H1 : ℝ ≃o ℝ} {D : ℝ}
    (A : M64FreeWeakPhaseAnnulus (n := (n + 1) + 1)
      e R c0 c1 H0 H1 (curvePeriod / circumference) D)
    (a : LoopPlane) {rho : ℝ} (hrho : 0 < rho) (hKS : closedBall a rho ⊆ S) :
    ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) 1),
      let r := rho * Real.exp (-s)
      ∀ gamma : ℝ → Q.charts.Point, Continuous gamma →
        Function.Periodic gamma curvePeriod →
        gamma =ᵐ[circleMu]
          (fun x => A.annulus.map (m64MorreyPolarStrip a rho (annulusPoint x s))) →
        ∀ B : M64ObservedConeDisk (n := (n + 1) + 1) e (fun x => gamma (x + Real.pi)),
          ∃ C : M64FreeWeakPhaseAnnulus (n := (n + 1) + 1)
              e R c0 c1 H0 H1 (curvePeriod / circumference) D,
            C.label0 = A.label0 ∧ C.label1 = A.label1 ∧
            C.annulus.map = (ball a r).piecewise (B.affineMap a r) A.annulus.map ∧
            ∀ i, (C.annulus.column i : LoopPlane → E) =ᵐ[mu]
              (ball a r).piecewise (B.affineColumn a r i) (A.annulus.column i) := by
  have hphases := A.local_circle_phase he a hrho hKS
  have hgreens := m64WeakMap_local_circle_green isOpen_interior a hrho hKS
    (e ∘ A.annulus.map) (fun i p => A.annulus.column i p) A.annulus.observed_memLp
    (fun i => Lp.memLp (A.annulus.column i)) A.annulus.weak_partial
  filter_upwards [hphases, hgreens, ae_restrict_mem measurableSet_Icc] with s hs hg hsI
  obtain ⟨L, hL, -, -, hLG, hLO⟩ := hs
  let r := rho * Real.exp (-s)
  have hr : 0 < r := mul_pos hrho (Real.exp_pos _)
  have hrho' : r ≤ rho := mul_le_of_le_one_right hrho.le
    (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hsI.1))
  have hball : ball a r ⊆ S :=
    ball_subset_closedBall.trans ((closedBall_subset_closedBall hrho').trans hKS)
  dsimp only
  intro gamma hgamma hgammaP hgammaAE B
  have hLquot (x : ℝ) : P.circle.quotient (L x) = (gamma x).1.2 := by
    apply planarCircleObservation_injective P.circle
    rw [planarCircleObservation_quotient, ← hR]
    exact (hLO gamma hgamma hgammaP hgammaAE x).symm
  obtain ⟨u, V, hu, hquotu, hboundary, huLp, hV, hw, -, -⟩ :=
    auxiliaryCircle_cone_weak_phase P Q he R hR B
      (hL.comp (continuous_id.add continuous_const)) (fun x => hLquot (x + Real.pi))
  have hnull := M60.haar_ball_ae_eq_closedBall volume a r
  have hmatching (phi : LoopPlane → ℝ) (hphi : ContDiff ℝ 1 phi) (i : Fin 2) :
      (∫ p in ball a r, phi p • B.affineColumn a r i p) +
        (∫ p in ball a r, fderiv ℝ phi p (EuclideanSpace.single i 1) •
          e (B.affineMap a r p)) =
      (∫ p in ball a r, phi p • A.annulus.column i p) +
        (∫ p in ball a r, fderiv ℝ phi p (EuclideanSpace.single i 1) •
          e (A.annulus.map p)) := by
    have hB := B.affine_green a hr phi hphi i
    rw [m64CircleIntegral_shift] at hB
    simp only [sub_add_cancel] at hB
    have hA := hg phi hphi i
    rw [← setIntegral_congr_set hnull, ← setIntegral_congr_set hnull] at hA
    refine hB.trans ((congrArg (fun z => r • z) (integral_congr_ae ?_)).trans hA.symm)
    filter_upwards [hgammaAE] with x hx
    change gamma x = A.annulus.map (a + r • angularPoint (x - Real.pi)) at hx
    rw [hx]
    rfl
  obtain ⟨W, hWm, hWc⟩ := A.annulus.replace measurableSet_ball hball
    (B.affineMap a r) (B.affineColumn a r) (B.affine_memLp a hr)
    (B.affine_column_memLp a hr) (B.affine_tangent a hr) hmatching
  let f := u ∘ m64ConeNormalize a r
  let Z := fun i p => r⁻¹ * V i (m64ConeNormalize a r p)
  have hf : MemLp f 2 (volume.restrict (ball a r)) := m64ConeNormalize_memLp huLp a hr
  have hZ (i : Fin 2) : MemLp (Z i) 2 (volume.restrict (ball a r)) :=
    (m64ConeNormalize_memLp (hV i) a hr).const_mul r⁻¹
  have hphaseMatching (phi : LoopPlane → ℝ) (hphi : ContDiff ℝ 1 phi) (i : Fin 2) :
      (∫ p in ball a r, phi p * Z i p) +
        (∫ p in ball a r, fderiv ℝ phi p (EuclideanSpace.single i 1) * f p) =
      (∫ p in ball a r, phi p * A.phaseColumn i p) +
        (∫ p in ball a r, fderiv ℝ phi p (EuclideanSpace.single i 1) * A.phase p) := by
    have hB := m64ContinuousScalarH1Disk_affine_green huLp hV hw hu a hr phi hphi i
    simp only [hboundary] at hB
    rw [m64CircleIntegral_shift] at hB
    simp only [Function.comp_apply, Pi.add_apply, id_eq, sub_add_cancel] at hB
    have hA := hLG phi hphi i
    rw [← setIntegral_congr_set hnull, ← setIntegral_congr_set hnull] at hA
    exact hB.trans hA.symm
  have hobs : (fun p => R (e (W.map p))) =ᵐ[mu]
      fun p => angularPoint ((curvePeriod / circumference) * (ball a r).piecewise f A.phase p) := by
    filter_upwards [A.phase_observation] with p hp
    rw [hWm]
    by_cases hpr : p ∈ ball a r
    · rw [piecewise_eq_of_mem _ _ _ hpr, piecewise_eq_of_mem _ _ _ hpr,
        hR]
      change planarCircleObservation (B.map (m64ConeNormalize a r p)).1.2 = _
      rw [← hquotu, planarCircleObservation_quotient]
      rfl
    · rw [piecewise_eq_of_notMem _ _ _ hpr, piecewise_eq_of_notMem _ _ _ hpr]
      exact hp
  obtain ⟨C, hC0, hC1, hCm, hCc⟩ :=
    A.exists_phase_disk_replacement W measurableSet_ball hball hf hZ hphaseMatching hobs
  refine ⟨C, hC0, hC1, hCm.trans hWm, ?_⟩
  intro i
  rw [hCc]
  exact hWc i

end PoincareConjecture.M64
