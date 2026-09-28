import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreePhaseInteriorReplacement

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

attribute [local instance] Classical.propDecidable

open Set Filter MeasureTheory Metric
open scoped Topology Manifold ContDiff ENNReal

namespace PoincareConjecture.M64

open Poincare.Analysis.Sobolev.Weak

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference auxiliary : ℝ}

local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S
local notation "E" => EuclideanSpace ℝ (Fin ((n + 1) + 1))

theorem auxiliaryCircle_phase_local_variations
    (P : M62.CircleProductData F circumference)
    (Q : M62.CircleProductData P.flow auxiliary)
    (e : Q.charts.Point → EuclideanSpace ℝ (Fin m))
    (he : ContMDiff (𝓡 ((n + 1) + 1)) (𝓡 m) 1 e)
    (Robs : EuclideanSpace ℝ (Fin m) →L[ℝ] LoopPlane)
    (hRobs : ∀ q, Robs (e q) = planarCircleObservation q.1.2)
    {c0 c1 : ℝ → Q.charts.Point} {H0 H1 : ℝ ≃o ℝ} {degree : ℝ}
    (A : M64FreeWeakPhaseAnnulus (n := (n + 1) + 1)
      e Robs c0 c1 H0 H1 (curvePeriod / circumference) degree)
    (q : Q.charts.Point) {u : LoopPlane → E}
    {W : Fin 2 → LoopPlane → E} {p0 : LoopPlane} {R : ℝ}
    (hR : 0 < R) (hRS : closedBall p0 R ⊆ S)
    (hu : ContinuousOn u (closedBall p0 R))
    (huT : MapsTo u (closedBall p0 R) (extChartAt (𝓡 ((n + 1) + 1)) q).target)
    (hW : ∀ i, MemLp (W i) 2 (volume.restrict (ball p0 R)))
    (hw : ∀ i j, HasWeakPartialDeriv i (fun p => W i p j) (fun p => u p j) (ball p0 R))
    (hmap : EqOn ((extChartAt (𝓡 ((n + 1) + 1)) q).symm ∘ u)
      A.annulus.map (closedBall p0 R)) :
    ∃ rho : ℝ, 0 < rho ∧ rho < R ∧
      ∀ phi : LoopPlane → E, ContDiff ℝ ∞ phi →
        tsupport phi ⊆ ball p0 ((rho / 4) * Real.exp (-1)) →
        ∃ epsilon : ℝ, 0 < epsilon ∧ ∀ t : ℝ, |t| < epsilon →
          let c := extChartAt (𝓡 ((n + 1) + 1)) q
          let f := fun p => c.symm (u p + t • phi p)
          let V := fun i p => fderiv ℝ (e ∘ c.symm) (u p + t • phi p)
            (W i p + t • fderiv ℝ phi p (EuclideanSpace.single i 1))
          ∃ r : ℝ, 0 < r ∧ (rho / 4) * Real.exp (-1) ≤ r ∧ r ≤ rho / 4 ∧
            ∃ C : M64FreeWeakPhaseAnnulus (n := (n + 1) + 1)
                e Robs c0 c1 H0 H1 (curvePeriod / circumference) degree,
              C.label0 = A.label0 ∧ C.label1 = A.label1 ∧
              C.annulus.map = (closedBall p0 r).piecewise f A.annulus.map ∧
              ∀ i, (C.annulus.column i : LoopPlane → EuclideanSpace ℝ (Fin m)) =ᵐ[mu]
                (closedBall p0 r).piecewise (V i) (A.annulus.column i) := by
  have hp0 : p0 ∈ closedBall p0 R := mem_closedBall_self hR.le
  obtain ⟨O, beta, hO, hzO, hOt, hbeta, hquot⟩ :=
    auxiliaryCircle_originalPhase_chart P Q q (huT hp0)
  have hpre : u ⁻¹' O ∈ 𝓝 p0 :=
    (hu.continuousAt (closedBall_mem_nhds p0 hR)) (hO.mem_nhds hzO)
  obtain ⟨eta, heta, hetaO⟩ := Metric.mem_nhds_iff.mp hpre
  let rho := min (eta / 2) (R / 2)
  have hrho : 0 < rho := lt_min (half_pos heta) (half_pos hR)
  have hrhoR : rho < R := (min_le_right _ _).trans_lt (half_lt_self hR)
  have hrhoeta : rho < eta := (min_le_left _ _).trans_lt (half_lt_self heta)
  have hsmall : closedBall p0 rho ⊆ closedBall p0 R := closedBall_subset_closedBall hrhoR.le
  have hmapO : MapsTo u (closedBall p0 rho) O :=
    (closedBall_subset_ball hrhoeta).trans hetaO
  have hWrho (i : Fin 2) : MemLp (W i) 2 (volume.restrict (ball p0 rho)) :=
    (hW i).mono_measure (Measure.restrict_mono (ball_subset_ball hrhoR.le) le_rfl)
  have hwrho (i : Fin 2) (j : Fin ((n + 1) + 1)) :
      HasWeakPartialDeriv i (fun p => W i p j) (fun p => u p j) (ball p0 rho) :=
    (hw i j).restrict isOpen_ball (ball_subset_ball hrhoR.le)
  refine ⟨rho, hrho, hrhoR, ?_⟩
  intro phi hp hs
  obtain ⟨epsilon, K, hepsilon, hK, hKO, hrange⟩ := m64_affine_variation_compact_range
    (isCompact_closedBall p0 rho) (hu.mono hsmall) hp.continuous.continuousOn hO hmapO
  have hrange0 : MapsTo u (closedBall p0 rho) K := by
    simpa only [zero_smul, add_zero] using hrange 0 (by simpa using hepsilon)
  refine ⟨epsilon, hepsilon, ?_⟩
  intro t ht
  exact auxiliaryCircle_phase_chart_replacement P Q e he Robs hRobs A q
    hrho (hsmall.trans hRS) (hu.mono hsmall) hp hs hWrho hwrho (hmap.mono hsmall)
    hO hK hKO hOt (hbeta.of_le (by simp)) hquot t hrange0 (hrange t ht)

end PoincareConjecture.M64
