import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryChartMinimum
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeightedCoordinateVariation












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Metric Topology
open scoped Manifold ContDiff

namespace PoincareConjecture.M64ObservedWeakAnnulus

open Poincare.Analysis.Sobolev.Weak

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {e : M → EuclideanSpace ℝ (Fin m)} {c0 c1 : ℝ → M}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "O" => m64AnnulusLowerDomain

set_option maxHeartbeats 1200000 in






theorem weighted_lower_coordinate_variation_eq_zero
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (g : RiemannianMetric n M) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (hei : IsEmbedding e) (hc0 : ContDiff ℝ 1 (e ∘ c0))
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (hQ : Continuous Q)
    {C : ℝ} (hb : ∀ q, ‖Q q‖ ≤ C)
    (hdiag : ∀ (q : M) (w : TangentSpace (𝓡 n) q),
      Q q (mfderiv (𝓡 n) (𝓡 m) e q w) (mfderiv (𝓡 n) (𝓡 m) e q w) = g.inner q w w)
    (modulus : ℝ)
    (hmin : ∀ B : M64ObservedWeakAnnulus (n := n) e c0 c1,
      A.weightedEnergy Q modulus ≤ B.weightedEnergy Q modulus)
    (v : LoopPlane → M) (hvae : v =ᵐ[volume.restrict O] A.lowerExtensionMap)
    (hvfixed : ∀ p ∈ O, p 1 < 0 → v p = c0 (p 0))
    (b : M) {u : LoopPlane → EuclideanSpace ℝ (Fin n)}
    {W : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin n)}
    {a : LoopPlane} {R : ℝ} (hR : 0 < R) (hRO : closedBall a R ⊆ O)
    (hu : Continuous u) (huT : MapsTo u (closedBall a R) (extChartAt (𝓡 n) b).target)
    (hW : ∀ i, MemLp (W i) 2 (volume.restrict (ball a R)))
    (hw : ∀ i j, HasWeakPartialDeriv i (fun p => W i p j) (fun p => u p j) (ball a R))
    (hmap : EqOn ((extChartAt (𝓡 n) b).symm ∘ u) v (closedBall a R))
    (phi : LoopPlane → EuclideanSpace ℝ (Fin n)) (hp : ContDiff ℝ ∞ phi)
    (hps : tsupport phi ⊆ ball a ((R / 4) * Real.exp (-1)))
    (hpzero : ∀ p : LoopPlane, p 1 ≤ 0 → phi p = 0) :
    let G := g.pullbackCoefficients (extChartAt (𝓡 n) b).symm
    let rate := fun p =>
      (modulus * (fderiv ℝ G (u p) (phi p) (W 0 p) (W 0 p) +
          2 * G (u p) (W 0 p) (fderiv ℝ phi p (EuclideanSpace.single 0 1))) +
        modulus⁻¹ * (fderiv ℝ G (u p) (phi p) (W 1 p) (W 1 p) +
          2 * G (u p) (W 1 p) (fderiv ℝ phi p (EuclideanSpace.single 1 1)))) / 2
    IntegrableOn rate (ball a (R / 2)) ∧ (∫ p in ball a (R / 2), rate p) = 0 := by
  obtain ⟨delta, K, hd, hK, hKt, hrange⟩ := m64_affine_variation_compact_range
    (isCompact_closedBall a R) hu.continuousOn hp.continuous.continuousOn
    (isOpen_extChartAt_target b) huT
  have hlocal := A.weighted_lower_affine_chart_minimum g he hei hc0 Q hQ hb hdiag
    modulus hmin v hvae hvfixed b hR hRO hu.continuousOn hp hps hpzero hW hw hmap hd hK hKt hrange
  have hhalf : closedBall a (R / 2) ⊆ closedBall a R :=
    closedBall_subset_closedBall (half_le_self hR.le)
  have hWH (i : Fin 2) : MemLp (W i) 2 (volume.restrict (ball a (R / 2))) :=
    (hW i).mono_measure (Measure.restrict_mono (ball_subset_ball (half_le_self hR.le)) le_rfl)
  have hvar := m64WeightedCoordinate_integral_firstVariation g b modulus u phi hu hp W
    a (R / 2) hWH hK hKt hd (fun t ht p hp => hrange t ht (hhalf hp))
  refine ⟨hvar.1, ?_⟩
  apply IsLocalMin.hasDerivAt_eq_zero ?_ hvar.2
  filter_upwards [ball_mem_nhds (0 : ℝ) hd] with t ht
  exact (hlocal t (by simpa only [mem_ball, Real.dist_eq, sub_zero] using ht)).2

end PoincareConjecture.M64ObservedWeakAnnulus
