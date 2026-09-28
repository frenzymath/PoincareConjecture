import PoincareConjecture.Proofs.M38.SumAssembly
import PoincareConjecture.Proofs.M38.MonodromyModel

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u v

namespace PoincareConjecture.M38

theorem exists_residualAssembly_finset {ι : Type v} [DecidableEq ι]
    (stage : Finset ι → GeneralizedSliceCarrier.{u}) (cuts : Finset ι)
    (next : ∀ s ⊆ cuts, s.Nonempty → ∃ i ∈ s,
      ∃ beta : Diffeomorph (𝓡 2) (𝓡 2) UnitTwoSphere UnitTwoSphere ∞,
        Nonempty (SmoothConnectedSumData (stage s) (monodromyCarrier.{u} beta)
          (stage (s.erase i))))
    {n : ℕ} {pieces : Fin n → GeneralizedSliceCarrier.{u}}
    (S : SmoothFiniteConnectedSumAssembly pieces (stage cuts)) :
    ∃ m : ℕ, ∃ beta : Fin m → Diffeomorph (𝓡 2) (𝓡 2) UnitTwoSphere UnitTwoSphere ∞,
      Nonempty (SmoothFiniteConnectedSumAssembly
        (Fin.append pieces (fun j => monodromyCarrier.{u} (beta j))) (stage ∅)) := by
  have aux : ∀ s : Finset ι, s ⊆ cuts →
      ∀ {k : ℕ} {p : Fin k → GeneralizedSliceCarrier.{u}},
      SmoothFiniteConnectedSumAssembly p (stage s) →
      ∃ m : ℕ, ∃ beta : Fin m → Diffeomorph (𝓡 2) (𝓡 2) UnitTwoSphere UnitTwoSphere ∞,
        Nonempty (SmoothFiniteConnectedSumAssembly
          (Fin.append p (fun j => monodromyCarrier.{u} (beta j))) (stage ∅)) := by
    intro s
    refine Finset.strongInductionOn s ?_
    intro t ih ht k p St
    rcases t.eq_empty_or_nonempty with rfl | hnonempty
    · refine ⟨0, Fin.elim0, ?_⟩
      have heq : Fin.append p (fun j : Fin 0 => monodromyCarrier.{u} (Fin.elim0 j)) = p := by
        rw [Fin.append_right_nil _ _ rfl]
        rfl
      exact heq.symm ▸ Nonempty.intro St
    · obtain ⟨i, hi, beta, ⟨K⟩⟩ := next t ht hnonempty
      let St' := appendConnectedSumAssembly St K
      obtain ⟨m, gamma, ⟨R⟩⟩ := ih (t.erase i) (Finset.erase_ssubset hi)
        ((Finset.erase_subset i t).trans ht) St'
      refine ⟨1 + m, Fin.append (fun _ : Fin 1 => beta) gamma, ?_⟩
      have hfamily : Fin.append (fun _ : Fin 1 => monodromyCarrier.{u} beta)
          (fun j => monodromyCarrier.{u} (gamma j)) =
          (fun j => monodromyCarrier.{u} (Fin.append (fun _ : Fin 1 => beta) gamma j)) := by
        funext j
        refine Fin.addCases ?_ ?_ j
        · intro i
          simp only [Fin.append_left]
        · intro i
          simp only [Fin.append_right]
      have R' := reassociateAssembly R
      rw [hfamily] at R'
      exact ⟨R'⟩
  exact aux cuts le_rfl S

theorem exists_residualAssembly {ι : Type v}
    (stage : Set ι → GeneralizedSliceCarrier.{u}) (cuts : Set ι) (hfinite : cuts.Finite)
    (next : ∀ s ⊆ cuts, s.Nonempty → ∃ i ∈ s,
      ∃ beta : Diffeomorph (𝓡 2) (𝓡 2) UnitTwoSphere UnitTwoSphere ∞,
        Nonempty (SmoothConnectedSumData (stage s) (monodromyCarrier.{u} beta)
          (stage (s \ {i}))))
    {n : ℕ} {pieces : Fin n → GeneralizedSliceCarrier.{u}}
    (S : SmoothFiniteConnectedSumAssembly pieces (stage cuts)) :
    ∃ m : ℕ, ∃ beta : Fin m → Diffeomorph (𝓡 2) (𝓡 2) UnitTwoSphere UnitTwoSphere ∞,
      Nonempty (SmoothFiniteConnectedSumAssembly
        (Fin.append pieces (fun j => monodromyCarrier.{u} (beta j))) (stage ∅)) := by
  classical
  have hnext : ∀ s ⊆ hfinite.toFinset, s.Nonempty → ∃ i ∈ s,
      ∃ beta : Diffeomorph (𝓡 2) (𝓡 2) UnitTwoSphere UnitTwoSphere ∞,
        Nonempty (SmoothConnectedSumData (stage (s : Set ι)) (monodromyCarrier.{u} beta)
          (stage ((s.erase i : Finset ι) : Set ι))) := by
    intro s hs hnonempty
    have hsub : (s : Set ι) ⊆ cuts := Set.Finite.subset_toFinset.mp hs
    obtain ⟨i, hi, beta, hK⟩ := next (s : Set ι) hsub hnonempty.to_set
    exact ⟨i, hi, beta, by simpa only [Finset.coe_erase] using hK⟩
  have S' : SmoothFiniteConnectedSumAssembly pieces (stage (hfinite.toFinset : Set ι)) := by
    simpa only [Set.Finite.coe_toFinset] using S
  have h := exists_residualAssembly_finset (fun s : Finset ι => stage (s : Set ι))
    hfinite.toFinset hnext S'
  simpa only [Finset.coe_empty] using h

end PoincareConjecture.M38
