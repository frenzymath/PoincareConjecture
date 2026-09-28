import PoincareConjecture.Proofs.M65.Claim19_23_SweptArea.FillingWitnesses
import PoincareConjecture.Proofs.M65.Sec19_6_Transfer.AnnularInfimum

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [ChartedSpace LoopAmbient M]
  [IsManifold (𝓡 3) ∞ M]
  {a b : ℝ} {F : RicciFlow 3 M (Set.Icc a b)}
  {Gamma : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M))}
  {zeta mu : ℝ}

theorem m65NetFillingDifference (hM64 : M64ComparisonTheory.{u})
    (compact : IsCompact (Set.univ : Set M))
    (V : M64ThreeDimensionalFlowConclusion F)
    (C : M63FamilyConclusion V.flow.geometry Gamma zeta)
    (net : M64FamilyAnnulusNet V.flow.geometry C.approximation.family mu)
    (z : LoopTwoSphere) :
    ∃ i : Fin net.node_count,
      ∀ circumference (h : 0 < circumference), circumference < net.circumference_cutoff →
        ∀ t : Set.Icc a b,
          |fillingArea (F.metric t) ((C.solutions circumference h).projected t (net.nodes i)) -
            fillingArea (F.metric t) ((C.solutions circumference h).projected t z)| <
              Real.exp (5 * V.flow.geometry.K0 * ((t : ℝ) - a)) * mu := by
  obtain ⟨i, hi⟩ := net.covers z
  refine ⟨i, ?_⟩
  intro circumference h hcutoff t
  obtain ⟨A, hA⟩ := hi circumference h hcutoff
  let S := C.solutions circumference h
  have E := m65FamilyAnnulusFlow S V.flow.evolution z (net.nodes i) A
  obtain ⟨D⟩ := m65ProjectedDisk_nonempty hM64 compact S t z
  exact ((m65ProjectedAreaDifference_le_infimum S
    (V.flow.projection circumference h) (V.disks circumference h) z (net.nodes i) E t D).trans
      (m65FamilyAnnulusArea_le_initial S z (net.nodes i) E A t)).trans_lt
        (mul_lt_mul_of_pos_left hA (Real.exp_pos _))

end PoincareConjecture
