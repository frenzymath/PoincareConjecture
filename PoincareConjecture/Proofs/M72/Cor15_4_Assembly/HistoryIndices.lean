import PoincareConjecture.Proofs.M72.Cor15_4_Assembly.Reindex
import PoincareConjecture.Proofs.M72.Cor15_4_Assembly.Successors










set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [T2Space M] [T3Space M]
  [SecondCountableTopology M]
  {N : NormalizedInitialMetric (M := M)}



def m72SummandPiece (I : M72ReconstructionInput N) (L : M72ReconstructionLedger I)
    (j : M72SummandIndex I L) : GeneralizedSliceCarrier.{u} :=
  (M72EventTopology I L j.1).conclusion.piece j.2.1



def M72TailSummandIndex (I : M72ReconstructionInput N) (L : M72ReconstructionLedger I)
    (e : M72EventIndex I L) :=
  {j : M72SummandIndex I L // e.1 ≤ j.1.1}



def m72TailSummandPiece (I : M72ReconstructionInput N) (L : M72ReconstructionLedger I)
    (e : M72EventIndex I L) (j : M72TailSummandIndex I L e) :
    GeneralizedSliceCarrier.{u} :=
  m72SummandPiece I L j.1



theorem m72SummandPieceNonempty (I : M72ReconstructionInput N)
    (L : M72ReconstructionLedger I) (j : M72SummandIndex I L) :
    Nonempty (m72SummandPiece I L j).carrier :=
  (M72EventTopology I L j.1).conclusion.piece_connected j.2.1 |>.nonempty.to_subtype
    |>.map Subtype.val



theorem m72TerminalNoSurvivor (I : M72ReconstructionInput N)
    (L : M72ReconstructionLedger I) (e : M72EventIndex I L)
    (heH : e.1 = I.extinction.extinction_time)
    (i : Fin (M72EventTopology I L e).conclusion.piece_count) :
    (M72EventTopology I L e).conclusion.kind i ≠ .survivor := by
  apply (M72EventTopology I L e).no_survivor_if_empty
  rw [heH]
  exact I.extinction.extinct



noncomputable def m72TerminalTailEquiv (I : M72ReconstructionInput N)
    (L : M72ReconstructionLedger I) (e : M72EventIndex I L)
    (heH : e.1 = I.extinction.extinction_time) :
    Fin (M72EventTopology I L e).conclusion.piece_count ≃ M72TailSummandIndex I L e := by
  let f : Fin (M72EventTopology I L e).conclusion.piece_count →
      M72TailSummandIndex I L e :=
    fun i => ⟨⟨e, ⟨i, m72TerminalNoSurvivor I L e heH i⟩⟩, le_rfl⟩
  apply Equiv.ofBijective f
  constructor
  · intro i j hij
    have h : (⟨e, ⟨i, m72TerminalNoSurvivor I L e heH i⟩⟩ : M72SummandIndex I L) =
        ⟨e, ⟨j, m72TerminalNoSurvivor I L e heH j⟩⟩ :=
      congrArg Subtype.val hij
    have h' : (⟨i, m72TerminalNoSurvivor I L e heH i⟩ : M72NonSurvivorIndex I L e) =
        ⟨j, m72TerminalNoSurvivor I L e heH j⟩ :=
      eq_of_heq (Sigma.mk.inj_iff.mp h).2
    exact congrArg Subtype.val h'
  · rintro ⟨⟨s, i⟩, hs⟩
    have hse : s = e := by
      apply Subtype.ext
      apply le_antisymm
      · rw [heH]
        exact M72EventBeforeExtinction I L s
      · exact hs
    subst s
    exact ⟨i.1, rfl⟩



theorem m72TerminalTailEquiv_piece (I : M72ReconstructionInput N)
    (L : M72ReconstructionLedger I) (e : M72EventIndex I L)
    (heH : e.1 = I.extinction.extinction_time)
    (i : Fin (M72EventTopology I L e).conclusion.piece_count) :
    m72TailSummandPiece I L e (m72TerminalTailEquiv I L e heH i) =
      (M72EventTopology I L e).conclusion.piece i := rfl



noncomputable def m72SuccessorTailEquiv (I : M72ReconstructionInput N)
    (L : M72ReconstructionLedger I) (e e' : M72EventIndex I L)
    (horder : e.1 < e'.1)
    (hminimal : ∀ s : ℝ, e.1 < s → s ∈ I.global.certificate.flow.surgery_times →
      e'.1 ≤ s) :
    (M72TailSummandIndex I L e' ⊕ M72NonSurvivorIndex I L e) ≃
      M72TailSummandIndex I L e := by
  let f : (M72TailSummandIndex I L e' ⊕ M72NonSurvivorIndex I L e) →
      M72TailSummandIndex I L e :=
    Sum.elim (fun j => ⟨j.1, horder.le.trans j.2⟩) (fun j => ⟨⟨e, j⟩, le_rfl⟩)
  apply Equiv.ofBijective f
  constructor
  · intro x y hxy
    cases x with
    | inl a =>
      cases y with
      | inl b =>
        apply congrArg Sum.inl
        apply Subtype.ext
        exact congrArg (fun t : M72TailSummandIndex I L e => t.1) hxy
      | inr b =>
        have h : a.1.1.1 = e.1 := congrArg (fun j => j.1.1.1) hxy
        exact (not_lt_of_ge (h ▸ a.2) horder).elim
    | inr a =>
      cases y with
      | inl b =>
        have h : e.1 = b.1.1.1 := congrArg (fun j => j.1.1.1) hxy
        exact (not_lt_of_ge (h.symm ▸ b.2) horder).elim
      | inr b =>
        apply congrArg Sum.inr
        have h : (⟨e, a⟩ : M72SummandIndex I L) = ⟨e, b⟩ :=
          congrArg Subtype.val hxy
        simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using h
  · rintro ⟨⟨s, i⟩, hs⟩
    by_cases hse : s = e
    · subst s
      exact ⟨Sum.inr i, rfl⟩
    · have hes : e.1 < s.1 := lt_of_le_of_ne hs (fun h => hse (Subtype.ext h.symm))
      have he's : e'.1 ≤ s.1 := hminimal s.1 hes (M72EventFlowMem I L s)
      exact ⟨Sum.inl ⟨⟨s, i⟩, he's⟩, rfl⟩



theorem m72SuccessorTailEquiv_piece (I : M72ReconstructionInput N)
    (L : M72ReconstructionLedger I) (e e' : M72EventIndex I L)
    (horder : e.1 < e'.1)
    (hminimal : ∀ s : ℝ, e.1 < s → s ∈ I.global.certificate.flow.surgery_times →
      e'.1 ≤ s)
    (j : M72TailSummandIndex I L e' ⊕ M72NonSurvivorIndex I L e) :
    m72TailSummandPiece I L e (m72SuccessorTailEquiv I L e e' horder hminimal j) =
      Sum.elim (m72TailSummandPiece I L e')
        (fun i : M72NonSurvivorIndex I L e =>
          (M72EventTopology I L e).conclusion.piece i.1) j := by
  cases j <;> rfl



def m72FirstTailEquiv (I : M72ReconstructionInput N)
    (L : M72ReconstructionLedger I) (e : M72EventIndex I L)
    (hfirst : ∀ e' : M72EventIndex I L, e.1 ≤ e'.1) :
    M72TailSummandIndex I L e ≃ M72SummandIndex I L :=
  Equiv.subtypeUnivEquiv fun j => hfirst j.1



theorem m72FirstTailEquiv_piece (I : M72ReconstructionInput N)
    (L : M72ReconstructionLedger I) (e : M72EventIndex I L)
    (hfirst : ∀ e' : M72EventIndex I L, e.1 ≤ e'.1)
    (j : M72TailSummandIndex I L e) :
    m72SummandPiece I L (m72FirstTailEquiv I L e hfirst j) =
      m72TailSummandPiece I L e j := rfl

end PoincareConjecture
