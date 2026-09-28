import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusWeakMinimizerInteriorSmooth
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeakMinimizerExistence
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.SmoothAnnulusAdmission
import PoincareConjecture.Proofs.M64.Sec19_4_Approximation.LipschitzAnnulusAdapter















set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Topology
open scoped Manifold ContDiff Bundle Topology ENNReal NNReal

universe u

namespace PoincareConjecture

noncomputable section

variable {n m : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {c0 c1 : ℝ → M}
  {e : M → EuclideanSpace ℝ (Fin m)}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => interior m64AnnulusDomain



theorem m64ObservedWeakAnnulus.exists_admissible_heinz_regularization
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (g : RiemannianMetric n M)
    (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (hei : IsClosedEmbedding e)
    (hread : M60.SUChartReadable (n := n) e)
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ)
    (hQ : Continuous Q)
    {C : ℝ} (hb : ∀ q, ‖Q q‖ ≤ C)
    (hdiag : ∀ (q : M) (v : TangentSpace (𝓡 n) q),
      Q q (mfderiv (𝓡 n) (𝓡 m) e q v) (mfderiv (𝓡 n) (𝓡 m) e q v) =
        g.inner q v v)
    (hmin : ∀ B : M64ObservedWeakAnnulus (n := n) e c0 c1,
      A.energy Q ≤ B.energy Q)
    {U : Set LoopPlane}
    (hU : IsOpen U)
    (hdom : m64AnnulusDomain ⊆ U)
    (hglobal : ContMDiffOn (𝓡 2) (𝓡 n) ∞ A.map U)
    (hperiodic : ∀ x s : ℝ,
      A.map (annulusPoint (x + curvePeriod) s) = A.map (annulusPoint x s))
    (hlower : ∀ x : ℝ, A.map (annulusPoint x 0) = c0 x)
    (hupper : ∀ x : ℝ, A.map (annulusPoint x 1) = c1 x) :
    ∃ B : M64Annulus g c0 c1,
      B.map = A.map ∧
      ContMDiffOn (𝓡 2) (𝓡 n) ∞ B.map S ∧
      M64PiecewiseC1Annulus B := by
  have hSsub : S ⊆ U := interior_subset.trans hdom
  have hA : ContinuousOn A.map S := hglobal.continuousOn.mono hSsub
  have hinterior := A.contMDiffOn_of_energy_minimum g (he.of_le (by simp))
    hei.isEmbedding hread Q hQ hb hdiag hmin hA
  obtain ⟨B, hB⟩ := m64Annulus_exists_eq_of_contMDiffOn g hU hdom
    (hglobal.of_le (by simp)) hperiodic hlower hupper
  have hcuts : M64PiecewiseC1Annulus B := by
    let cut : Fin (1 + 1) → ℝ := fun i => (i : ℝ) * curvePeriod
    have hcut : StrictMono cut := by
      intro i j hij
      dsimp [cut]
      exact mul_lt_mul_of_pos_right (by exact_mod_cast hij)
        (by unfold curvePeriod; positivity)
    have hcut_zero : cut 0 = 0 := by simp [cut]
    have hcut_last : cut (Fin.last 1) = curvePeriod := by simp [cut]
    apply m64PiecewiseC1Annulus_of_cuts B (by norm_num) cut hcut hcut_zero hcut_last
    intro j
    have hj : j = 0 := Fin.eq_zero j
    subst j
    rw [hB]
    apply (hglobal.of_le (by simp)).mono
    intro p hp
    simp only [Set.mem_ofPred_eq] at hp
    dsimp [cut] at hp
    have hp0 : 0 ≤ p 0 := by simpa using hp.1
    have hp1 : p 0 ≤ curvePeriod := by simpa using hp.2.1
    exact hdom ⟨hp0, hp1, hp.2.2.1, hp.2.2.2⟩
  refine ⟨B, hB, ?_, hcuts⟩
  simpa [hB] using hinterior

end

end PoincareConjecture
