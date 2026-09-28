import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.IntrinsicEnergy
import PoincareConjecture.Proofs.M60.Mathlib.CompactManifoldIntegralDerivative

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

omit [IsManifold (𝓡 n) ∞ M] in

theorem m60SphereVariation_contMDiff_slice {v : ℝ × UnitTwoSphere → M}
    {ε s : ℝ} (hv : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 2)) (𝓡 n) ∞ v
      (Ioo (-ε) ε ×ˢ univ)) (hs : s ∈ Ioo (-ε) ε) :
    ContMDiff (𝓡 2) (𝓡 n) ∞ (fun p => v (s, p)) := by
  intro p
  have h : ContMDiffAt ((𝓘(ℝ, ℝ)).prod (𝓡 2)) (𝓡 n) ∞ v (s, p) :=
    hv.contMDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨hs, mem_univ p⟩)
  exact h.comp p (contMDiffAt_const.prodMk contMDiffAt_id)

theorem m60SphereEnergy_differentiableAt_of_variation (g : RiemannianMetric n M)
    {v : ℝ × UnitTwoSphere → M} {ε : ℝ} (hε : 0 < ε)
    (hv : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 2)) (𝓡 n) ∞ v
      (Ioo (-ε) ε ×ˢ univ)) :
    DifferentiableAt ℝ (fun s => m60SphereEnergy g (fun p => v (s, p))) 0 := by
  let E := fun q : ℝ × UnitTwoSphere => m60SphereIntrinsicEnergy g (fun p => v (q.1, p)) q.2
  have hE : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞ E (Ioo (-ε) ε ×ˢ univ) := by
    intro q hq
    exact (m60SphereIntrinsicEnergy_family_contMDiffAt g v q
      (hv.contMDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds hq))).contMDiffWithinAt
  have hd := M60.differentiableAt_integral_of_contMDiffOn
    (μ := m60RoundSphereMetric.volumeMeasure) hε hE
  apply hd.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds (show (0 : ℝ) ∈ Ioo (-ε) ε from ⟨by linarith, hε⟩)]
    with s hs
  exact m60SphereEnergy_eq_intrinsic_integral g (fun p => v (s, p))
    (m60SphereVariation_contMDiff_slice hv hs)

end PoincareConjecture
