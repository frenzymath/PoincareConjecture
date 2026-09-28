import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Disks.SupportedMotion
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Support.ClosedExtension
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallTopology



set_option autoImplicit false
open Set Geometry Topology unitInterval

namespace Homeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {D : Set E}

theorem exists_closedExtension_joint_finitePL_track
    (hD : IsClosed D) (H : I → D ≃ₜ D)
    (hfix : ∀ t (x : D), (x : E) ∈ frontier D → H t x = x)
    (hc : Continuous (fun z : I × D => H z.1 z.2))
    (f : (ℝ × E) → E) (hf : FinitePiecewiseAffineOn f (Icc (0 : ℝ) 1 ×ˢ D))
    (hfv : ∀ t : I, ∀ x : D, f ((t : ℝ), x) = (H t x : E)) :
    ∃ g : (ℝ × E) → E,
      (∀ t : I, ∀ x : E, g ((t : ℝ), x) = (H t).closedExtension hD (hfix t) x) ∧
      ∀ (K : SimplicialComplex ℝ E), K.faces.Finite →
        FinitePiecewiseAffineOn g (Icc (0 : ℝ) 1 ×ˢ K.space) := by
  let G (t : I) := (H t).closedExtension hD (hfix t)
  let g (z : ℝ × E) := G (projIcc 0 1 zero_le_one z.1) z.2
  have hgv (t : I) (x : E) : g ((t : ℝ), x) = G t x := by
    simp only [g, projIcc_val]
  have hG : Continuous (fun z : I × E => G z.1 z.2) :=
    continuous_closedExtension_family H hD hc hfix
  have ht : Continuous (fun z : ℝ × E => projIcc (0 : ℝ) 1 zero_le_one z.1) :=
    continuous_projIcc.comp continuous_fst
  have hp : Continuous (fun z : ℝ × E => (projIcc (0 : ℝ) 1 zero_le_one z.1, z.2)) :=
    ht.prodMk continuous_snd
  have hgc : Continuous g := by
    change Continuous ((fun z : I × E => G z.1 z.2) ∘
      (fun z : ℝ × E => (projIcc (0 : ℝ) 1 zero_le_one z.1, z.2)))
    exact hG.comp hp
  refine ⟨g, hgv, ?_⟩
  intro K hK
  apply PoincareConjecture.M76.CollarIsotopy.finitePiecewiseAffineOn_supported_track K hK hD hf
    hgc.continuousOn
  · intro t ht x hx
    rw [hgv ⟨t, ht⟩ x, hfv ⟨t, ht⟩ ⟨x, hx.2⟩]
    exact (H ⟨t, ht⟩).closedExtension_apply_mem hD (hfix ⟨t, ht⟩) hx.2
  · intro t ht x hx
    rw [hgv ⟨t, ht⟩ x]
    exact (H ⟨t, ht⟩).closedExtension_apply_notMem hD (hfix ⟨t, ht⟩) hx.2

end Homeomorph

namespace Set

theorem IsFinitePLBallPair.exists_supported_joint_PL_isotopy
    {V E : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [Nontrivial V]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {D : Set E} (hD : IsFinitePLBallPair V D (frontier D))
    (e : D ≃ₜ D) (he : e.IsFinitePL)
    (hfix : ∀ x : D, (x : E) ∈ frontier D → e x = x) :
    ∃ (H : I → E ≃ₜ E) (F Fi : (ℝ × E) → E),
      H 0 = Homeomorph.refl E ∧ H 1 = e.closedExtension hD.isCompact.isClosed hfix ∧
      Continuous (fun z : I × E => H z.1 z.2) ∧
      Continuous (fun z : I × E => (H z.1).symm z.2) ∧
      (∀ t : I, ∀ x : E, x ∉ interior D → H t x = x) ∧
      (∀ t : I, ∀ x : E, F ((t : ℝ), x) = H t x) ∧
      (∀ t : I, ∀ x : E, Fi ((t : ℝ), x) = (H t).symm x) ∧
      ∀ (K : SimplicialComplex ℝ E), K.faces.Finite →
        FinitePiecewiseAffineOn F (Icc (0 : ℝ) 1 ×ˢ K.space) ∧
        FinitePiecewiseAffineOn Fi (Icc (0 : ℝ) 1 ×ˢ K.space) := by
  obtain ⟨J, f, fi, hzero, hone, hfixed, hc, hci, hf, hfi, hfv, hfiv⟩ :=
    hD.exists_joint_PL_isotopy e he hfix
  let hclosed := hD.isCompact.isClosed
  let H (t : I) := (J t).closedExtension hclosed (hfixed t)
  have hfixedInv (t : I) (x : D) (hx : (x : E) ∈ frontier D) : (J t).symm x = x := by
    apply (J t).injective
    rw [(J t).apply_symm_apply, hfixed t x hx]
  obtain ⟨F, hFv, hF⟩ := Homeomorph.exists_closedExtension_joint_finitePL_track
    hclosed J hfixed hc f hf hfv
  obtain ⟨Fi, hFiv, hFi⟩ := Homeomorph.exists_closedExtension_joint_finitePL_track
    hclosed (fun t => (J t).symm) hfixedInv hci fi hfi hfiv
  have hFiVal (t : I) (x : E) : Fi ((t : ℝ), x) = (H t).symm x := hFiv t x
  refine ⟨H, F, Fi, ?_, ?_,
    Homeomorph.continuous_closedExtension_family J hclosed hc hfixed,
    Homeomorph.continuous_closedExtension_family_symm J hclosed hci hfixed,
    ?_, hFv, hFiVal, fun K hK => ⟨hF K hK, hFi K hK⟩⟩
  · apply Homeomorph.ext
    intro x
    by_cases hx : x ∈ D
    · change (J 0).closedExtension hclosed (hfixed 0) x = x
      rw [(J 0).closedExtension_apply_mem hclosed (hfixed 0) hx, hzero]
      rfl
    · exact (J 0).closedExtension_apply_notMem hclosed (hfixed 0) hx
  · apply Homeomorph.ext
    intro x
    by_cases hx : x ∈ D
    · rw [e.closedExtension_apply_mem hclosed hfix hx]
      change (J 1).closedExtension hclosed (hfixed 1) x = (e ⟨x, hx⟩ : E)
      rw [(J 1).closedExtension_apply_mem hclosed (hfixed 1) hx, hone]
    · exact ((J 1).closedExtension_apply_notMem hclosed (hfixed 1) hx).trans
        (e.closedExtension_apply_notMem hclosed hfix hx).symm
  · intro t x hx
    by_cases hxD : x ∈ D
    · exact (J t).closedExtension_apply_frontier hclosed (hfixed t)
        ⟨subset_closure hxD, hx⟩
    · exact (J t).closedExtension_apply_notMem hclosed (hfixed t) hxD

end Set
