import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.PeriodicTwoChartRegularity
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.AnnulusClosedConformality

noncomputable section
set_option autoImplicit false
set_option warningAsError true

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff

namespace PoincareConjecture

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "S" => interior m64AnnulusDomain
local notation "D" => Set.ofPred (fun p : LoopPlane =>
  p 0 ∈ Ioo (0 : ℝ) curvePeriod ∧ p 1 ∈ Icc (0 : ℝ) 1)

theorem m64Annulus_periodic_classical_regularity
    {g : RiemannianMetric n M} {c0 c1 : ℝ → M} (A : M64Annulus g c0 c1)
    (hA : ContMDiffOn (𝓡 2) (𝓡 n) 1 A.map m64AnnulusDomain)
    (hAi : ContMDiffOn (𝓡 2) (𝓡 n) ∞ A.map S)
    {G : LoopPlane → M} (hG : ContMDiffOn (𝓡 2) (𝓡 n) 1 G D)
    (hGi : ContMDiffOn (𝓡 2) (𝓡 n) ∞ G S)
    (hae : G =ᵐ[volume.restrict S] A.map ∘ m64AnnulusHalfTurn) :
    ContMDiffOn (𝓡 2) (𝓡 n) 1 A.map {p : LoopPlane | p 1 ∈ Icc (0 : ℝ) 1} ∧
      ContMDiffOn (𝓡 2) (𝓡 n) ∞ A.map {p : LoopPlane | p 1 ∈ Ioo (0 : ℝ) 1} := by
  have hD : D ⊆ m64AnnulusDomain := fun _ hp => ⟨hp.1.1.le, hp.1.2.le, hp.2⟩
  have hAD := hA.mono hD
  have hleft := m64AnnulusHalfTurn_left_overlap hAD.continuousOn hG.continuousOn hae
  have hright := m64AnnulusHalfTurn_right_overlap hAD.continuousOn hG.continuousOn hae
  have hcut := m64AnnulusCutCompletion_contMDiffOn hAD hG hleft hright
  have heq : EqOn (m64AnnulusCutCompletion A.map G) A.map S := by
    intro p hp
    have hc := (m64AnnulusInterior_coordinates p).mp hp
    exact m64AnnulusCutCompletion_interior _ _ ⟨hc.1, hc.2.1⟩
  have hclosed : EqOn (m64AnnulusCutCompletion A.map G) A.map m64AnnulusDomain :=
    heq.of_subset_closure hcut.continuousOn hA.continuousOn interior_subset (by
      have hsub : m64AnnulusInterior ⊆ S := by
        apply interior_maximal _ isOpen_m64AnnulusInterior
        rw [← m64AnnulusInterior_closure]
        exact subset_closure
      calc
        m64AnnulusDomain = closure m64AnnulusInterior := m64AnnulusInterior_closure.symm
        _ ⊆ closure S := closure_mono hsub)
  have hzero (y : ℝ) (hy : y ∈ Icc (0 : ℝ) 1) :
      A.map (annulusPoint 0 y) = G (annulusPoint (curvePeriod / 2) y) :=
    (hclosed (show annulusPoint 0 y ∈ m64AnnulusDomain from
      ⟨le_rfl, by unfold curvePeriod; positivity, hy⟩)).symm.trans
        (m64AnnulusCutCompletion_edges A.map G y).1
  refine ⟨m64PeriodicMap_contMDiffOn_of_two_charts hAD hG A.periodic hleft hright hzero, ?_⟩
  have hset : {p : LoopPlane | p 0 ∈ Ioo (0 : ℝ) curvePeriod ∧ p 1 ∈ Ioo (0 : ℝ) 1} =
      S := by
    ext p
    rw [m64AnnulusInterior_coordinates]
    simp only [mem_ofPred_eq, mem_Ioo, and_assoc]
  apply m64PeriodicMap_contMDiffOn_of_two_charts (Y := Ioo (0 : ℝ) 1)
    (hset.symm ▸ hAi) (hset.symm ▸ hGi) A.periodic
  · intro p hp
    exact hleft ⟨hp.1, hp.2.1.le, hp.2.2.le⟩
  · intro p hp
    exact hright ⟨hp.1, hp.2.1.le, hp.2.2.le⟩
  · exact fun y hy => hzero y ⟨hy.1.le, hy.2.le⟩

end PoincareConjecture
