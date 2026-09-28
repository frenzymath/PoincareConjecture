import PoincareConjecture.Proofs.M51.InitialRawFlow
import PoincareConjecture.Proofs.M01.NormalizationTensorNorm
import PoincareConjecture.Proofs.M05













set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M51Initial

variable {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]

omit [T2Space M] [SecondCountableTopology M] in

theorem initial_pinched (I : NormalizedInitialMetric (M := M))
    {J : Set ℝ} (F : RicciFlow 3 M J) (h0 : F.metric 0 = I.metric) :
    HamiltonIveyPinchedAt (F.connection 0) 0 :=
  m01HamiltonIveyPinchedAt_zero_of_norm_le (F.connection 0) (initial_norm_bound I F h0)


theorem pinched_on [CompactSpace M] (I : NormalizedInitialMetric (M := M))
    {J : Set ℝ} (F : RicciFlow 3 M J) (h0 : F.metric 0 = I.metric)
    (hshape : J = Ici 0 ∨ ∃ T : ℝ, 0 < T ∧ J = Ico 0 T) :
    ∀ t ∈ J, SurgeryPinchedAt (F.connection t) t := by
  intro t ht
  have hwindow : ∃ b : ℝ, 0 < b ∧ Ico 0 b ⊆ J ∧ t ∈ Ico 0 b := by
    rcases hshape with hJ | ⟨b, hb, hJ⟩
    · have ht0 : 0 ≤ t := by simpa only [hJ, mem_Ici] using ht
      refine ⟨t + 1, by linarith, ?_, ⟨ht0, by linarith⟩⟩
      intro s hs
      simpa only [hJ, mem_Ici] using hs.1
    · refine ⟨b, hb, ?_, ?_⟩
      · intro s hs
        simpa only [hJ] using hs
      · simpa only [hJ] using ht
  obtain ⟨b, hb, hsub, htb⟩ := hwindow
  have hne : (Ico 0 b).Nontrivial := by
    obtain ⟨c, hc, hcb⟩ := exists_between hb
    exact ⟨0, ⟨le_rfl, hb⟩, c, ⟨hc.le, hcb⟩, hc.ne⟩
  let R := M51Ordinary.restrict F hsub ordConnected_Ico hne
  have hinit : HamiltonIveyPinchedAt (R.connection 0) 0 := initial_pinched I F h0
  have h := (hamiltonIveyPinching_from_M04 (a := 0) (b := b)
    le_rfl hb R hinit).persistence t htb
  exact ⟨h.1, fun x _ => h.2.1 x, fun x _ => h.2.2 x⟩

end PoincareConjecture.M51Initial
