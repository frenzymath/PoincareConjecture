import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryScalarEquation
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryIndicatorEquation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Metric Topology
open scoped Manifold ContDiff ENNReal

namespace PoincareConjecture

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)

set_option maxHeartbeats 1000000 in

theorem m64WeightedChart_scalar_indicator_equation
    (g : RiemannianMetric n M) (b : M) (modulus : ℝ)
    {u : LoopPlane → E} {W : Fin 2 → LoopPlane → E} {a : LoopPlane} {R : ℝ}
    (hR : 0 < R) (hu : ContinuousOn u (closedBall a R))
    (huT : MapsTo u (closedBall a R) (extChartAt (𝓡 n) b).target)
    (hW : ∀ i, MemLp (W i) 2 (volume.restrict (ball a R)))
    (hvar : ∀ phi : LoopPlane → E, ContDiff ℝ ∞ phi →
      tsupport phi ⊆ ball a ((R / 4) * Real.exp (-1)) →
      (∀ p : LoopPlane, p 1 ≤ 0 → phi p = 0) →
      let G := g.pullbackCoefficients (extChartAt (𝓡 n) b).symm
      (∫ p in ball a (R / 2),
        (modulus * (fderiv ℝ G (u p) (phi p) (W 0 p) (W 0 p) +
            2 * G (u p) (W 0 p) (fderiv ℝ phi p (EuclideanSpace.single 0 1))) +
          modulus⁻¹ * (fderiv ℝ G (u p) (phi p) (W 1 p) (W 1 p) +
            2 * G (u p) (W 1 p) (fderiv ℝ phi p (EuclideanSpace.single 1 1)))) / 2) = 0)
    (j : Fin n) {psi : LoopPlane → ℝ} (hp : ContDiff ℝ ∞ psi)
    (hc : HasCompactSupport psi)
    (hs : tsupport psi ⊆
      ball a ((R / 4) * Real.exp (-1)) ∩ {p : LoopPlane | 0 < p 1}) :
    let G := g.pullbackCoefficients (extChartAt (𝓡 n) b).symm
    let S := ball a ((R / 4) * Real.exp (-1)) ∩ {p : LoopPlane | 0 < p 1}
    (∫ p, ∑ i : Fin 2, S.indicator
        (fun q => (if i = 0 then modulus else modulus⁻¹) *
          G (u q) (W i q) (EuclideanSpace.single j 1)) p *
          fderiv ℝ psi p (EuclideanSpace.single i 1)) =
      ∫ p, S.indicator
        (fun q => -(modulus * fderiv ℝ G (u q) (EuclideanSpace.single j 1)
            (W 0 q) (W 0 q) +
          modulus⁻¹ * fderiv ℝ G (u q) (EuclideanSpace.single j 1)
            (W 1 q) (W 1 q)) / 2) p * psi p := by
  let G := g.pullbackCoefficients (extChartAt (𝓡 n) b).symm
  let r := (R / 4) * Real.exp (-1)
  let H : Set LoopPlane := {p : LoopPlane | 0 < p 1}
  let S : Set LoopPlane := ball a r ∩ H
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hexp : Real.exp (-1 : ℝ) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    norm_num
  have hrr : r < R / 2 := by
    dsimp [r]
    nlinarith [Real.exp_pos (-1 : ℝ)]
  have hU : MeasurableSet (ball a (R / 2)) := measurableSet_ball
  have hO : IsOpen (ball a r) := isOpen_ball
  have hOU : ball a r ⊆ ball a (R / 2) := ball_subset_ball hrr.le
  obtain ⟨hF, hB⟩ := m64WeightedChart_flux_source_memLp g b modulus hu huT hW
  have hF' (i : Fin 2) : MemLp
      (fun p => (if i = 0 then modulus else modulus⁻¹) *
        G (u p) (W i p) (EuclideanSpace.single j 1))
      2 (volume.restrict (ball a (R / 2))) := by
    have hi := (hF j i).mono_measure
      (Measure.restrict_mono (ball_subset_ball (half_le_self hR.le)) le_rfl)
    simpa only [G] using hi
  have hB' : IntegrableOn (fun p =>
      -(modulus * fderiv ℝ G (u p) (EuclideanSpace.single j 1)
          (W 0 p) (W 0 p) +
        modulus⁻¹ * fderiv ℝ G (u p) (EuclideanSpace.single j 1)
          (W 1 p) (W 1 p)) / 2) (ball a (R / 2)) := by
    have hi := (hB j).mono_set (ball_subset_ball (half_le_self hR.le))
    simpa only [G] using hi
  let F : Fin 2 → LoopPlane → ℝ := fun i p =>
    (if i = 0 then modulus else modulus⁻¹) *
      G (u p) (W i p) (EuclideanSpace.single j 1)
  let bsource : LoopPlane → ℝ := fun p =>
    -(modulus * fderiv ℝ G (u p) (EuclideanSpace.single j 1)
        (W 0 p) (W 0 p) +
      modulus⁻¹ * fderiv ℝ G (u p) (EuclideanSpace.single j 1)
        (W 1 p) (W 1 p)) / 2
  have hscalar' : ∀ phi : LoopPlane → ℝ, ContDiff ℝ ∞ phi →
      HasCompactSupport phi → tsupport phi ⊆ ball a r ∩ H →
      (∫ p in ball a (R / 2),
        ∑ i : Fin 2, F i p * fderiv ℝ phi p (EuclideanSpace.single i 1)) =
      ∫ p in ball a (R / 2), bsource p * phi p := by
    intro phi hphi hpc hps
    have hscalar := m64WeightedChart_scalar_equation g b modulus hR hu huT hW hvar j
      hphi hpc (by simpa only [r, S, H] using hps)
    simpa only [F, bsource, G, Function.comp_apply, Fin.sum_univ_two,
      one_ne_zero, ↓reduceIte] using hscalar
  obtain ⟨-, -, hindicator⟩ := m64ScalarBoundary_indicator_equation
    hU hO hOU (fun i => hF' i) hB' hscalar'
  have hres := hindicator psi hp hc hs
  simpa only [S, F, bsource, G, Function.comp_apply] using hres

end PoincareConjecture

namespace PoincareConjecture.M64ObservedWeakAnnulus

open Poincare.Analysis.Sobolev.Weak

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  {e : M → EuclideanSpace ℝ (Fin m)} {c0 c1 : ℝ → M}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "O" => m64AnnulusLowerDomain

set_option maxHeartbeats 1000000 in

theorem weighted_lower_scalar_indicator_equation_of_minimum
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (g : RiemannianMetric n M) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (hei : IsClosedEmbedding e) (hc0 : ContDiff ℝ 1 (e ∘ c0))
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (hQ : Continuous Q)
    {C : ℝ} (hb : ∀ q, ‖Q q‖ ≤ C)
    (hdiag : ∀ (q : M) (v : TangentSpace (𝓡 n) q),
      Q q (mfderiv (𝓡 n) (𝓡 m) e q v) (mfderiv (𝓡 n) (𝓡 m) e q v) = g.inner q v v)
    (modulus : ℝ)
    (hmin : ∀ B : M64ObservedWeakAnnulus (n := n) e c0 c1,
      A.weightedEnergy Q modulus ≤ B.weightedEnergy Q modulus)
    {F : LoopPlane → M} (hFae : F =ᵐ[volume.restrict O] A.lowerExtensionMap)
    (hfixed : ∀ p ∈ O, p 1 < 0 → F p = c0 (p 0))
    (b : M) {u : LoopPlane → EuclideanSpace ℝ (Fin n)}
    {W : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin n)} {a : LoopPlane} {R : ℝ}
    (hR : 0 < R) (hRO : closedBall a R ⊆ O)
    (hu : Continuous u)
    (huT : MapsTo u (closedBall a R) (extChartAt (𝓡 n) b).target)
    (hW : ∀ i, MemLp (W i) 2 (volume.restrict (ball a R)))
    (hwu : ∀ i j, HasWeakPartialDeriv i (fun p => W i p j) (fun p => u p j)
      (ball a R))
    (hmap : EqOn ((extChartAt (𝓡 n) b).symm ∘ u) F (closedBall a R))
    (j : Fin n) {psi : LoopPlane → ℝ} (hp : ContDiff ℝ ∞ psi)
    (hc : HasCompactSupport psi)
    (hs : tsupport psi ⊆
      ball a ((R / 4) * Real.exp (-1)) ∩ {p : LoopPlane | 0 < p 1}) :
    let G := g.pullbackCoefficients (extChartAt (𝓡 n) b).symm
    let S := ball a ((R / 4) * Real.exp (-1)) ∩ {p : LoopPlane | 0 < p 1}
    (∫ p, ∑ i : Fin 2, S.indicator
        (fun q => (if i = 0 then modulus else modulus⁻¹) *
          G (u q) (W i q) (EuclideanSpace.single j 1)) p *
          fderiv ℝ psi p (EuclideanSpace.single i 1)) =
      ∫ p, S.indicator
        (fun q => -(modulus * fderiv ℝ G (u q) (EuclideanSpace.single j 1)
            (W 0 q) (W 0 q) +
          modulus⁻¹ * fderiv ℝ G (u q) (EuclideanSpace.single j 1)
            (W 1 q) (W 1 q)) / 2) p * psi p := by
  have hvar : ∀ phi : LoopPlane → EuclideanSpace ℝ (Fin n), ContDiff ℝ ∞ phi →
      tsupport phi ⊆ ball a ((R / 4) * Real.exp (-1)) →
      (∀ p : LoopPlane, p 1 ≤ 0 → phi p = 0) →
      let G := g.pullbackCoefficients (extChartAt (𝓡 n) b).symm
      (∫ p in ball a (R / 2),
        (modulus * (fderiv ℝ G (u p) (phi p) (W 0 p) (W 0 p) +
            2 * G (u p) (W 0 p) (fderiv ℝ phi p (EuclideanSpace.single 0 1))) +
          modulus⁻¹ * (fderiv ℝ G (u p) (phi p) (W 1 p) (W 1 p) +
            2 * G (u p) (W 1 p) (fderiv ℝ phi p (EuclideanSpace.single 1 1)))) / 2) = 0 := by
    intro phi hphi hsupport hzero
    have hv := A.weighted_lower_coordinate_variation_eq_zero g he hei.isEmbedding hc0 Q hQ
      hb hdiag modulus hmin F hFae hfixed b hR hRO hu huT hW hwu hmap phi hphi hsupport hzero
    simpa only using hv.2
  exact m64WeightedChart_scalar_indicator_equation g b modulus hR
    hu.continuousOn huT hW hvar j hp hc hs

end PoincareConjecture.M64ObservedWeakAnnulus
