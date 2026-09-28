import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusBoundaryC1Transfer

noncomputable section
set_option autoImplicit false
set_option warningAsError true

open Set Filter Metric
open scoped Topology Manifold ContDiff

namespace PoincareConjecture

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

theorem m64AnnulusRadialCompletion_contMDiffOn
    (f : LoopPlane → M) (c0 c1 : ℝ → M)
    (hf : ContMDiffOn (𝓡 2) (𝓡 n) 1 f (interior m64AnnulusDomain))
    (h0 : ∀ x ∈ Ioo (0 : ℝ) curvePeriod,
      ContMDiffWithinAt (𝓡 2) (𝓡 n) 1 (m64AnnulusRadialCompletion f c0 c1)
        {p : LoopPlane | 0 ≤ p 1} (annulusPoint x 0))
    (h1 : ∀ x ∈ Ioo (0 : ℝ) curvePeriod,
      ContMDiffWithinAt (𝓡 2) (𝓡 n) 1 (m64AnnulusRadialCompletion f c0 c1)
        {p : LoopPlane | p 1 ≤ 1} (annulusPoint x 1)) :
    ContMDiffOn (𝓡 2) (𝓡 n) 1 (m64AnnulusRadialCompletion f c0 c1)
      {p : LoopPlane | p 0 ∈ Ioo (0 : ℝ) curvePeriod ∧ p 1 ∈ Icc (0 : ℝ) 1} := by
  let D : Set LoopPlane :=
    {p | p 0 ∈ Ioo (0 : ℝ) curvePeriod ∧ p 1 ∈ Icc (0 : ℝ) 1}
  intro p hp
  have hpoint : annulusPoint (p 0) (p 1) = p := by ext i; fin_cases i <;> rfl
  by_cases hp0 : p 1 = 0
  · have hh := (h0 (p 0) hp.1).mono (t := D) (fun q hq => hq.2.1)
    rwa [← hp0, hpoint] at hh
  by_cases hp1 : p 1 = 1
  · have hh := (h1 (p 0) hp.1).mono (t := D) (fun q hq => hq.2.2)
    rwa [← hp1, hpoint] at hh
  have hpS : p ∈ interior m64AnnulusDomain :=
    (m64AnnulusInterior_coordinates p).mpr
      ⟨hp.1.1, hp.1.2, lt_of_le_of_ne hp.2.1 (Ne.symm hp0), lt_of_le_of_ne hp.2.2 hp1⟩
  have heq : m64AnnulusRadialCompletion f c0 c1 =ᶠ[𝓝 p] f := by
    filter_upwards [isOpen_interior.mem_nhds hpS] with q hq
    have hc := (m64AnnulusInterior_coordinates q).mp hq
    exact m64AnnulusRadialCompletion_interior f c0 c1 ⟨hc.2.2.1, hc.2.2.2⟩
  exact ((hf.contMDiffAt (isOpen_interior.mem_nhds hpS)).congr_of_eventuallyEq
    heq).contMDiffWithinAt

end PoincareConjecture
