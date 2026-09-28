import PoincareConjecture.Proofs.M47.TerminalCurvatureInverseChart










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u v w

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)



theorem terminalSource_atlas_inverse_coefficient_jets
    {X : Type u} {Y : Type v} {M : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace M]
    [ChartedSpace E X] [ChartedSpace E Y] [ChartedSpace E M]
    [IsManifold (𝓡 3) ∞ X] [IsManifold (𝓡 3) ∞ Y] [IsManifold (𝓡 3) ∞ M]
    (gY : RiemannianMetric 3 Y) (gM : RiemannianMetric 3 M)
    (j : PartialDiffeomorph (𝓡 3) (𝓡 3) Y M ∞) (hj : j.source = univ)
    (hmetric : ∀ z (v w : TangentSpace (𝓡 3) z),
      gY.inner z v w = gM.inner (j z)
        (mfderiv (𝓡 3) (𝓡 3) j z v) (mfderiv (𝓡 3) (𝓡 3) j z w))
    (phi : PartialDiffeomorph (𝓡 3) (𝓡 3) X Y ∞) (f : X → M)
    (hfactor : ∀ x ∈ phi.source, j (phi x) = f x)
    (c : PartialDiffeomorph (𝓡 3) (𝓡 3) X E ∞)
    {y : E} (hy : y ∈ c.target) (hcapture : c.symm y ∈ phi.source) :
    (gY.pullbackCoefficients (phi ∘ c.symm) =ᶠ[𝓝 y]
      gM.pullbackCoefficients (f ∘ c.symm)) ∧
    ∀ m : ℕ, iteratedFDeriv ℝ m (gY.pullbackCoefficients (phi ∘ c.symm)) y =
      iteratedFDeriv ℝ m (gM.pullbackCoefficients (f ∘ c.symm)) y := by
  let q := c.symm.trans phi
  have hyq : y ∈ q.source := ⟨hy, hcapture⟩
  have hisometry : gY.pullbackCoefficients q =ᶠ[𝓝 y]
      gM.pullbackCoefficients (j ∘ q) := by
    filter_upwards [q.open_source.mem_nhds hyq] with z hz
    have hq := q.contMDiffOn_toFun.contMDiffAt (q.open_source.mem_nhds hz)
    have hjs : q z ∈ j.source := hj.symm ▸ mem_univ _
    have hjq := j.contMDiffOn_toFun.contMDiffAt (j.open_source.mem_nhds hjs)
    have hd := mfderiv_comp z (hjq.mdifferentiableAt (by simp))
      (hq.mdifferentiableAt (by simp))
    ext v w
    change gY.inner (q z) (mfderiv (𝓡 3) (𝓡 3) q z v)
      (mfderiv (𝓡 3) (𝓡 3) q z w) =
        gM.inner (j (q z)) (mfderiv (𝓡 3) (𝓡 3) (j ∘ q) z v)
          (mfderiv (𝓡 3) (𝓡 3) (j ∘ q) z w)
    rw [hd]
    exact hmetric (q z) _ _
  have hmaps : j ∘ q =ᶠ[𝓝 y] f ∘ c.symm := by
    filter_upwards [q.open_source.mem_nhds hyq] with z hz
    exact hfactor (c.symm z) hz.2
  have hcoeff := hisometry.trans (terminalCurvature_pullback_coefficient_germ gM hmaps)
  refine ⟨hcoeff, ?_⟩
  intro m
  exact (hcoeff.iteratedFDeriv (𝕜 := ℝ) m).eq_of_nhds

end PoincareConjecture.M47
