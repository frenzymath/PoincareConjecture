import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryWeightedInteriorSmooth
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerBubbleLimitStrongEquation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Metric Topology
open scoped Manifold ContDiff

namespace PoincareConjecture.M64ObservedWeakAnnulus

open Poincare.Analysis.Sobolev.Weak CoordinateExponential ConnectionVariation
  ConjugateVariation

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {e : M → EuclideanSpace ℝ (Fin m)} {c0 c1 : ℝ → M}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => interior m64AnnulusDomain

theorem exists_rescaled_harmonic_chart_of_weighted_minimum
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (g : RiemannianMetric n M) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (hei : IsEmbedding e) (hread : M60.SUChartReadable (n := n) e)
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (hQ : Continuous Q)
    {C : ℝ} (hb : ∀ q, ‖Q q‖ ≤ C)
    (hdiag : ∀ (q : M) (v : TangentSpace (𝓡 n) q),
      Q q (mfderiv (𝓡 n) (𝓡 m) e q v) (mfderiv (𝓡 n) (𝓡 m) e q v) =
        g.inner q v v)
    {modulus : ℝ} (hmodulus : 0 < modulus)
    (hmin : ∀ B : M64ObservedWeakAnnulus (n := n) e c0 c1,
      A.weightedEnergy Q modulus ≤ B.weightedEnergy Q modulus)
    (hA : ContinuousOn A.map S) {a : LoopPlane} (ha : a ∈ S) :
    let D := m64SourceScale (Real.sqrt modulus) (Real.sqrt_pos.mpr hmodulus).ne'
    ∃ (b : M) (u : LoopPlane → EuclideanSpace ℝ (Fin n)) (R : ℝ),
      0 < R ∧ closedBall a R ⊆ S ∧
      ContDiffOn ℝ ∞ (u ∘ D) (D ⁻¹' ball a R) ∧
      MapsTo u (closedBall a R) (extChartAt (𝓡 n) b).target ∧
      EqOn ((extChartAt (𝓡 n) b).symm ∘ u) A.map (closedBall a R) ∧
      ∀ p ∈ D ⁻¹' ball a R, (∑ i : Fin 2,
        covDerivAlong (christoffelBilinear
          (g.pullbackCoefficients (extChartAt (𝓡 n) b).symm)) (u ∘ D)
          (fun q => fderiv ℝ (u ∘ D) q (EuclideanSpace.basisFun (Fin 2) ℝ i))
          (EuclideanSpace.basisFun (Fin 2) ℝ i) p) = 0 := by
  let s := Real.sqrt modulus
  let D := m64SourceScale s (Real.sqrt_pos.mpr hmodulus).ne'
  obtain ⟨b, L, R, hR, hRS, hchart, hu0, -, hW, hw⟩ :=
    A.exists_local_chart_columns he.continuous hread hA ha
  obtain ⟨u, hu, heq⟩ := m64_exists_continuous_extension isClosed_closedBall hu0
  have hcoord (p : LoopPlane) (hp : p ∈ closedBall a R) :
      u p = extChartAt (𝓡 n) b (A.map p) := (heq hp).trans (hchart p hp).2
  have huT : MapsTo u (closedBall a R) (extChartAt (𝓡 n) b).target := by
    intro p hp
    rw [hcoord p hp]
    exact (extChartAt (𝓡 n) b).map_source (hchart p hp).1
  have hmap : EqOn ((extChartAt (𝓡 n) b).symm ∘ u) A.map (closedBall a R) := by
    intro p hp
    change (extChartAt (𝓡 n) b).symm (u p) = A.map p
    rw [hcoord p hp, (extChartAt (𝓡 n) b).left_inv (hchart p hp).1]
  have hwu (i : Fin 2) (j : Fin n) : HasWeakPartialDeriv i
      (fun p => L (A.column i p) j) (fun p => u p j) (ball a R) := by
    apply m64WeakPartialDeriv_ae_congr ?_ (Eventually.of_forall fun _ => rfl) (hw i j)
    filter_upwards [ae_restrict_mem isOpen_ball.measurableSet] with p hp
    exact congrArg (fun v : EuclideanSpace ℝ (Fin n) => v j)
      (heq (ball_subset_closedBall hp)).symm
  have hlocal (p : LoopPlane) (hp : p ∈ ball a R) :
      ContDiffAt ℝ ∞ (u ∘ D) (D.symm p) ∧ (∑ i : Fin 2,
        covDerivAlong (christoffelBilinear
          (g.pullbackCoefficients (extChartAt (𝓡 n) b).symm)) (u ∘ D)
          (fun q => fderiv ℝ (u ∘ D) q (EuclideanSpace.basisFun (Fin 2) ℝ i))
          (EuclideanSpace.basisFun (Fin 2) ℝ i) (D.symm p)) = 0 := by
    obtain ⟨rho, hrho, hsmall⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
      (isOpen_ball.mem_nhds hp)
    have hsmallR : closedBall p rho ⊆ closedBall a R :=
      hsmall.trans ball_subset_closedBall
    have hsmallB : ball p rho ⊆ ball a R := ball_subset_closedBall.trans hsmall
    obtain ⟨radius, hcritical⟩ := A.weighted_coordinates_rescaled_critical g he hei Q hQ
      hb hdiag hmodulus hmin b hrho (hsmallR.trans hRS) hu
      (fun q hq => huT (hsmallR hq))
      (fun i => (hW i).mono_measure (Measure.restrict_mono hsmallB le_rfl))
      (fun i j => (hwu i j).restrict isOpen_ball hsmallB)
      (fun q hq => hmap (hsmallR hq))
    have hsm := M60.suWeakAlphaCoordinate_smooth_alpha_one g b (u ∘ D)
      (fun i q => m64SourceScaleFactor s i • L (A.column i (D q)))
      (D.symm p) radius hcritical
    exact ⟨hsm, M60.suWeakAlphaCoordinate_harmonic_of_smooth hcritical hsm⟩
  refine ⟨b, u, R, hR, hRS, ?_, huT, hmap, ?_⟩
  · intro p hp
    have h := (hlocal (D p) hp).1
    rw [D.symm_apply_apply] at h
    exact h.contDiffWithinAt
  · intro p hp
    have h := (hlocal (D p) hp).2
    simpa only [D.symm_apply_apply] using h

end PoincareConjecture.M64ObservedWeakAnnulus
