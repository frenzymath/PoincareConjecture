import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.EnergyDifferentiability
import PoincareConjecture.Proofs.M60.Mathlib.HomotopyOnInterval
import PoincareConjecture.Definitions.M53SphereSeparation
import Mathlib.Analysis.Calculus.LocalExtr.Basic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

omit [IsManifold (𝓡 n) ∞ M] in

theorem m60SphereVariation_nullHomotopic_center {v : ℝ × UnitTwoSphere → M}
    {ε s : ℝ} (hε : 0 < ε) (hs : s ∈ Ioo (-ε) ε)
    (hv : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 2)) (𝓡 n) ∞ v (Ioo (-ε) ε ×ˢ univ))
    (hnull : IsNullHomotopicSphere (fun p => v (s, p))) :
    IsNullHomotopicSphere (fun p => v (0, p)) := by
  have hzero : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨by linarith, hε⟩
  have h0 := (m60SphereVariation_contMDiff_slice hv hzero).continuous
  have h1 := (m60SphereVariation_contMDiff_slice hv hs).continuous
  obtain ⟨_, p, hp⟩ := hnull
  refine ⟨h0, p, ?_⟩
  exact (M60.homotopic_of_continuousOn_interval hε hs hv.continuousOn h0 h1).trans hp

theorem m60EnergyStationary_of_least_energy (g : RiemannianMetric n M)
    (f : UnitTwoSphere → M) (hnull : ¬ IsNullHomotopicSphere f)
    (hmin : ∀ h : UnitTwoSphere → M, ContMDiff (𝓡 2) (𝓡 n) 1 h →
      ¬ IsNullHomotopicSphere h → m60SphereEnergy g f ≤ m60SphereEnergy g h) :
    M60EnergyStationary g f := by
  intro ε hε v hv hv0
  have hcenter : (fun p => v (0, p)) = f := funext hv0
  have hd := m60SphereEnergy_differentiableAt_of_variation g hε hv
  have hlocal : IsLocalMin (fun s => m60SphereEnergy g (fun p => v (s, p))) 0 := by
    filter_upwards [isOpen_Ioo.mem_nhds (show (0 : ℝ) ∈ Ioo (-ε) ε from ⟨by linarith, hε⟩)]
      with s hs
    rw [hcenter]
    apply hmin (fun p => v (s, p)) ((m60SphereVariation_contMDiff_slice hv hs).of_le (by simp))
    intro h
    apply hnull
    rw [← hcenter]
    exact m60SphereVariation_nullHomotopic_center hε hs hv h
  simpa only [hlocal.deriv_eq_zero] using hd.hasDerivAt

end PoincareConjecture
