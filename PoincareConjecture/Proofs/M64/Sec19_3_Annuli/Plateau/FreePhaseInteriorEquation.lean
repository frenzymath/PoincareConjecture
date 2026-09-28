import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreePhaseLocalVariations
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreePhaseCoordinateMinimum
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeightedCoordinateVariation









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Metric Topology
open scoped Manifold ContDiff

namespace PoincareConjecture.M64

open Poincare.Analysis.Sobolev.Weak

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference auxiliary : ℝ}

local notation "S" => interior m64AnnulusDomain
local notation "E" => EuclideanSpace ℝ (Fin ((n + 1) + 1))




theorem auxiliaryCircle_free_phase_local_equation
    (P : M62.CircleProductData F circumference)
    (Q : M62.CircleProductData P.flow auxiliary)
    (e : Q.charts.Point → EuclideanSpace ℝ (Fin m))
    (he : ContMDiff (𝓡 ((n + 1) + 1)) (𝓡 m) 1 e) (hei : IsEmbedding e)
    (Robs : EuclideanSpace ℝ (Fin m) →L[ℝ] LoopPlane)
    (hRobs : ∀ q, Robs (e q) = planarCircleObservation q.1.2)
    {c0 c1 : ℝ → Q.charts.Point} {H0 H1 : ℝ ≃o ℝ} {degree : ℝ}
    (A : M64FreeWeakPhaseAnnulus (n := (n + 1) + 1)
      e Robs c0 c1 H0 H1 (curvePeriod / circumference) degree)
    (g : RiemannianMetric ((n + 1) + 1) Q.charts.Point)
    (B : Q.charts.Point → EuclideanSpace ℝ (Fin m) →L[ℝ]
      EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) (hB : Continuous B)
    {bound : ℝ} (hb : ∀ q, ‖B q‖ ≤ bound)
    (hdiag : ∀ (q : Q.charts.Point) (v : TangentSpace (𝓡 ((n + 1) + 1)) q),
      B q (mfderiv (𝓡 ((n + 1) + 1)) (𝓡 m) e q v)
        (mfderiv (𝓡 ((n + 1) + 1)) (𝓡 m) e q v) = g.inner q v v)
    (modulus : ℝ)
    (hminimum : ∀ C : M64FreeWeakPhaseAnnulus (n := (n + 1) + 1)
        e Robs c0 c1 H0 H1 (curvePeriod / circumference) degree,
      A.annulus.weightedEnergy B modulus ≤ C.annulus.weightedEnergy B modulus)
    (q : Q.charts.Point) {u : LoopPlane → E} {W : Fin 2 → LoopPlane → E}
    {p0 : LoopPlane} {R : ℝ} (hR : 0 < R) (hRS : closedBall p0 R ⊆ S)
    (hu : Continuous u)
    (huT : MapsTo u (closedBall p0 R) (extChartAt (𝓡 ((n + 1) + 1)) q).target)
    (hW : ∀ i, MemLp (W i) 2 (volume.restrict (ball p0 R)))
    (hw : ∀ i j, HasWeakPartialDeriv i (fun p => W i p j) (fun p => u p j) (ball p0 R))
    (hmap : EqOn ((extChartAt (𝓡 ((n + 1) + 1)) q).symm ∘ u)
      A.annulus.map (closedBall p0 R)) :
    ∃ rho : ℝ, 0 < rho ∧ rho < R ∧
      ∀ phi : LoopPlane → E, ContDiff ℝ ∞ phi →
        tsupport phi ⊆ ball p0 ((rho / 4) * Real.exp (-1)) →
        let G := g.pullbackCoefficients (extChartAt (𝓡 ((n + 1) + 1)) q).symm
        let rate := fun p =>
          (modulus * (fderiv ℝ G (u p) (phi p) (W 0 p) (W 0 p) +
              2 * G (u p) (W 0 p) (fderiv ℝ phi p (EuclideanSpace.single 0 1))) +
            modulus⁻¹ * (fderiv ℝ G (u p) (phi p) (W 1 p) (W 1 p) +
              2 * G (u p) (W 1 p) (fderiv ℝ phi p (EuclideanSpace.single 1 1)))) / 2
        IntegrableOn rate (ball p0 (rho / 2)) ∧ (∫ p in ball p0 (rho / 2), rate p) = 0 := by
  obtain ⟨rho, hrho, hrhoR, hvariations⟩ := auxiliaryCircle_phase_local_variations P Q
    e he Robs hRobs A q hR hRS hu.continuousOn huT hW hw hmap
  have hsmall : closedBall p0 rho ⊆ closedBall p0 R := closedBall_subset_closedBall hrhoR.le
  have hWrho (i : Fin 2) : MemLp (W i) 2 (volume.restrict (ball p0 rho)) :=
    (hW i).mono_measure (Measure.restrict_mono (ball_subset_ball hrhoR.le) le_rfl)
  have hwrho (i : Fin 2) (j : Fin ((n + 1) + 1)) :
      HasWeakPartialDeriv i (fun p => W i p j) (fun p => u p j) (ball p0 rho) :=
    (hw i j).restrict isOpen_ball (ball_subset_ball hrhoR.le)
  refine ⟨rho, hrho, hrhoR, ?_⟩
  intro phi hp hs
  obtain ⟨epsilon, hepsilon, hcompetitors⟩ := hvariations phi hp hs
  obtain ⟨eta, K, heta, hK, hKt, hrange⟩ := m64_affine_variation_compact_range
    (isCompact_closedBall p0 rho) hu.continuousOn hp.continuous.continuousOn
    (isOpen_extChartAt_target q) (huT.mono hsmall Subset.rfl)
  have hhalf : closedBall p0 (rho / 2) ⊆ closedBall p0 rho :=
    closedBall_subset_closedBall (half_le_self hrho.le)
  have hWH (i : Fin 2) : MemLp (W i) 2 (volume.restrict (ball p0 (rho / 2))) :=
    (hWrho i).mono_measure
      (Measure.restrict_mono (ball_subset_ball (half_le_self hrho.le)) le_rfl)
  have hvar := m64WeightedCoordinate_integral_firstVariation g q modulus u phi hu hp W
    p0 (rho / 2) hWH hK hKt heta (fun t ht p hp => hrange t ht (hhalf hp))
  refine ⟨hvar.1, ?_⟩
  apply IsLocalMin.hasDerivAt_eq_zero ?_ hvar.2
  filter_upwards [ball_mem_nhds (0 : ℝ) (lt_min hepsilon heta)] with t ht
  have ht' : |t| < min epsilon eta := by
    simpa only [mem_ball, Real.dist_eq, sub_zero] using ht
  obtain ⟨r, -, hrl, hrh, C, hC0, hC1, hCm, hCc⟩ :=
    hcompetitors t (ht'.trans_le (min_le_left _ _))
  exact A.weighted_coordinate_replacement_minimum C hC0 hC1 g he hei B hB hb hdiag
    modulus (hminimum C) q hrho (hsmall.trans hRS) hrl hrh hu.continuousOn hp hs
    hWrho hwrho (hmap.mono hsmall) heta hK hKt hrange t
    (ht'.trans_le (min_le_right _ _)) hCm hCc

end PoincareConjecture.M64
