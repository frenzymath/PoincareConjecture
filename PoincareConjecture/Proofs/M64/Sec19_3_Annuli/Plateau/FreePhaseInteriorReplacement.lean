import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreePhaseChartAngle
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreePhaseCompactCorrection
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreePhaseCoordinateCorrection
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusRegularityReplacement
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Stabilization.TwoCircleObservation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

attribute [local instance] Classical.propDecidable

open Set Filter MeasureTheory Metric Topology
open scoped Manifold ContDiff ENNReal

namespace PoincareConjecture.M64

open Poincare.Analysis.Sobolev.Weak Proofs.M58

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference auxiliary : ℝ}

local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S
local notation "E" => EuclideanSpace ℝ (Fin ((n + 1) + 1))

theorem auxiliaryCircle_phase_chart_replacement
    (P : M62.CircleProductData F circumference)
    (Q : M62.CircleProductData P.flow auxiliary)
    (e : Q.charts.Point → EuclideanSpace ℝ (Fin m))
    (he : ContMDiff (𝓡 ((n + 1) + 1)) (𝓡 m) 1 e)
    (Robs : EuclideanSpace ℝ (Fin m) →L[ℝ] LoopPlane)
    (hRobs : ∀ q, Robs (e q) = planarCircleObservation q.1.2)
    {c0 c1 : ℝ → Q.charts.Point} {H0 H1 : ℝ ≃o ℝ} {degree : ℝ}
    (A : M64FreeWeakPhaseAnnulus (n := (n + 1) + 1)
      e Robs c0 c1 H0 H1 (curvePeriod / circumference) degree)
    (q : Q.charts.Point) {u phi : LoopPlane → E}
    {W : Fin 2 → LoopPlane → E} {p0 : LoopPlane} {R : ℝ}
    (hR : 0 < R) (hRS : closedBall p0 R ⊆ S)
    (hu : ContinuousOn u (closedBall p0 R)) (hp : ContDiff ℝ ∞ phi)
    (hs : tsupport phi ⊆ ball p0 ((R / 4) * Real.exp (-1)))
    (hW : ∀ i, MemLp (W i) 2 (volume.restrict (ball p0 R)))
    (hw : ∀ i j, HasWeakPartialDeriv i (fun p => W i p j) (fun p => u p j) (ball p0 R))
    (hmap : EqOn ((extChartAt (𝓡 ((n + 1) + 1)) q).symm ∘ u)
      A.annulus.map (closedBall p0 R))
    {O K : Set E} (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    (hOt : O ⊆ (extChartAt (𝓡 ((n + 1) + 1)) q).target)
    {beta : E → ℝ} (hbeta : ContDiffOn ℝ 1 beta O)
    (hquot : ∀ y ∈ O, P.circle.quotient (beta y) =
      ((extChartAt (𝓡 ((n + 1) + 1)) q).symm y).1.2)
    (t : ℝ) (hrange0 : MapsTo u (closedBall p0 R) K)
    (hranget : MapsTo (fun p => u p + t • phi p) (closedBall p0 R) K) :
    let c := extChartAt (𝓡 ((n + 1) + 1)) q
    let f := fun p => c.symm (u p + t • phi p)
    let V := fun i p => fderiv ℝ (e ∘ c.symm) (u p + t • phi p)
      (W i p + t • fderiv ℝ phi p (EuclideanSpace.single i 1))
    ∃ r : ℝ, 0 < r ∧ (R / 4) * Real.exp (-1) ≤ r ∧ r ≤ R / 4 ∧
      ∃ C : M64FreeWeakPhaseAnnulus (n := (n + 1) + 1)
          e Robs c0 c1 H0 H1 (curvePeriod / circumference) degree,
        C.label0 = A.label0 ∧ C.label1 = A.label1 ∧
        C.annulus.map = (closedBall p0 r).piecewise f A.annulus.map ∧
        ∀ i, (C.annulus.column i : LoopPlane → EuclideanSpace ℝ (Fin m)) =ᵐ[mu]
          (closedBall p0 r).piecewise (V i) (A.annulus.column i) := by
  classical
  let c := extChartAt (𝓡 ((n + 1) + 1)) q
  let f := fun p => c.symm (u p + t • phi p)
  let V := fun i p => fderiv ℝ (e ∘ c.symm) (u p + t • phi p)
    (W i p + t • fderiv ℝ phi p (EuclideanSpace.single i 1))
  have hquarter : 0 < R / 4 := div_pos hR (by norm_num)
  have hsmall : (R / 4) * Real.exp (-1) ≤ R / 4 :=
    mul_le_of_le_one_right hquarter.le (Real.exp_le_one_iff.mpr (by norm_num))
  have hsquarter : tsupport phi ⊆ closedBall p0 (R / 4) :=
    hs.trans ((ball_subset_ball hsmall).trans ball_subset_closedBall)
  have hc : HasCompactSupport phi :=
    (isCompact_closedBall p0 (R / 4)).of_isClosed_subset (isClosed_tsupport phi) hsquarter
  have hhalfR : R / 2 < R := half_lt_self hR
  have hquarterHalf : closedBall p0 (R / 4) ⊆ ball p0 (R / 2) :=
    closedBall_subset_ball (by linarith)
  have hhalfS : ball p0 (R / 2) ⊆ S :=
    ((ball_subset_ball hhalfR.le).trans ball_subset_closedBall).trans hRS
  obtain ⟨hut, hWt, hwt⟩ := m64_affine_weak_coordinates hu hp hW hw t
  obtain ⟨hf, hV, hwV, htV⟩ := m64InverseChart_observed_weak_columns e he q
    (half_pos hR) hhalfR hut hWt hwt hK (hKO.trans hOt) hranget
  have hmatch (p : LoopPlane) (hl : (R / 4) * Real.exp (-1) ≤ dist p p0)
      (hh : dist p p0 ≤ R / 4) : f p = A.annulus.map p := by
    have hnot : p ∉ tsupport phi := fun h => (not_lt_of_ge hl) (hs h)
    have hpR : p ∈ closedBall p0 R := hh.trans (by linarith)
    simpa only [f, c, Function.comp_apply, image_eq_zero_of_notMem_tsupport hnot,
      smul_zero, add_zero]
      using hmap hpR
  obtain ⟨r, hr, hrl, hrh, B, hBm, hBc⟩ :=
    A.annulus.exists_replacement_of_outer_agreement isOpen_ball p0 hquarter hquarterHalf
      (hquarterHalf.trans hhalfS) f V hf hV hwV htV hmatch
  let delta := fun p => beta (u p + t • phi p) - beta (u p)
  obtain ⟨hdelta, hzero⟩ := m64Coordinate_compact_phase_change (half_pos hR) hhalfR
    hu hp hc (hsquarter.trans hquarterHalf) hW hw hO hK hKO t hrange0 hranget hbeta
  choose Z hZ hwZ using hdelta.2
  have hdLp : MemLp delta 2 volume := by
    simpa only [Measure.restrict_univ] using hdelta.1
  have hZLp (i : Fin 2) : MemLp (Z i) 2 volume := by
    simpa only [Measure.restrict_univ] using hZ i
  have hobs : (fun p => Robs (e (B.map p))) =ᵐ[mu]
      fun p => angularPoint (curvePeriod / circumference * (A.phase p + delta p)) := by
    filter_upwards [A.phase_observation] with p hp
    have hqold : P.circle.quotient (A.phase p) = (A.annulus.map p).1.2 := by
      apply planarCircleObservation_injective P.circle
      rw [planarCircleObservation_quotient, ← hp, hRobs]
    change (A.phase p : AddCircle circumference) = (A.annulus.map p).1.2 at hqold
    rw [hRobs, ← planarCircleObservation_quotient P.circle]
    apply congrArg planarCircleObservation
    by_cases hpr : p ∈ closedBall p0 r
    · have hpR : p ∈ closedBall p0 R :=
        (closedBall_subset_closedBall (hrh.trans (by linarith))) hpr
      have hnew := hquot _ (hKO (hranget hpR))
      have hold := hquot _ (hKO (hrange0 hpR))
      change (beta (u p + t • phi p) : AddCircle circumference) =
        (c.symm (u p + t • phi p)).1.2 at hnew
      change (beta (u p) : AddCircle circumference) = (c.symm (u p)).1.2 at hold
      rw [hBm, piecewise_eq_of_mem _ _ _ hpr]
      change (c.symm (u p + t • phi p)).1.2 =
        (A.phase p : AddCircle circumference) +
          ((beta (u p + t • phi p) : AddCircle circumference) -
            (beta (u p) : AddCircle circumference))
      rw [hqold, hnew, hold, ← hmap hpR]
      change (c.symm (u p + t • phi p)).1.2 =
        (c.symm (u p)).1.2 + ((c.symm (u p + t • phi p)).1.2 - (c.symm (u p)).1.2)
      abel
    · have hpnot : p ∉ tsupport phi := by
        intro h
        exact hpr (show dist p p0 ≤ r from (hs h).le.trans hrl)
      have hd : delta p = 0 := hzero p hpnot
      rw [hBm, piecewise_eq_of_notMem _ _ _ hpr, hd, add_zero]
      exact hqold.symm
  obtain ⟨C, hC0, hC1, hCm, hCc⟩ := A.exists_compact_phase_correction B
    hc ((hsquarter.trans (closedBall_subset_closedBall (by linarith))).trans hRS)
    hdLp hZLp hwZ hzero hobs
  refine ⟨r, hr, hrl, hrh, C, hC0, hC1, hCm.trans hBm, ?_⟩
  intro i
  rw [hCc]
  exact hBc i

end PoincareConjecture.M64
