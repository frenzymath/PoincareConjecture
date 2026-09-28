import PoincareConjecture.Proofs.M38.ResidualAssembly
import PoincareConjecture.Proofs.M38.ResidualCutConnectivity
import PoincareConjecture.Proofs.M38.ForestReversal
import PoincareConjecture.Proofs.M38.NonseparatingCut
import PoincareConjecture.Proofs.M38.PartialCutEmpty
import PoincareConjecture.Proofs.M38.AssemblyTransport

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

variable (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
  [Nonempty (F.slice T).carrier] (P : ∀ i, EventCapCoordinates F T hT i)

theorem exists_actualResidualAssembly
    {n : ℕ} {pieces : Fin n → GeneralizedSliceCarrier.{u}}
    (S : SmoothFiniteConnectedSumAssembly pieces (partialCappedCarrier F T hT P Set.univ)) :
    ∃ m : ℕ, ∃ beta : Fin m → Diffeomorph (𝓡 2) (𝓡 2) UnitTwoSphere UnitTwoSphere ∞,
      Nonempty (SmoothFiniteConnectedSumAssembly
        (Fin.append pieces (fun j => monodromyCarrier.{u} (beta j)))
          (F.slice (F.event T hT).tMinus)) := by
  classical
  obtain ⟨H⟩ := exists_eventSpanningForest F T hT P
  let R := S.trans H.reverse_selected
  have hnext : ∀ s ⊆ H.residualCaps, s.Nonempty →
      ∃ i ∈ s, ∃ beta : Diffeomorph (𝓡 2) (𝓡 2) UnitTwoSphere UnitTwoSphere ∞,
        Nonempty (SmoothConnectedSumData (partialCappedCarrier F T hT P s)
          (monodromyCarrier.{u} beta) (partialCappedCarrier F T hT P (s \ {i}))) := by
    intro s hs hnonempty
    obtain ⟨i, hi⟩ := hnonempty
    have hsub : s \ {i} ⊆ H.residualCaps := Set.diff_subset.trans hs
    have hin : i ∉ s \ {i} := by simp
    have hsame := H.residual_singleCut_centers (s \ {i}) hsub i (hs hi)
    have hinsert : insert i (s \ {i}) = s := by
      ext j
      by_cases hji : j = i
      · subst j
        simp [hi]
      · simp [hji]
    obtain ⟨beta, hK⟩ := singleCut_nonseparating_data F T hT P (s \ {i}) i hin hsame
    rw [hinsert] at hK
    exact ⟨i, hi, beta, hK⟩
  obtain ⟨m, beta, ⟨Q⟩⟩ := exists_residualAssembly (partialCappedCarrier F T hT P)
    H.residualCaps (Set.toFinite _) hnext R
  exact ⟨m, beta, exists_transportAssembly Q (partialEmptyDiffeomorph F T hT P)⟩

end PoincareConjecture.M38
