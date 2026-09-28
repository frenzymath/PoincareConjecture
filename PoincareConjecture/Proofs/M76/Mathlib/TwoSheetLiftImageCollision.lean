import PoincareConjecture.Proofs.M76.Mathlib.TwoSheetCoverInvolution
import PoincareConjecture.Proofs.M76.Mathlib.CoveringDeformationRetraction
import Mathlib.Topology.Separation.Hausdorff














set_option autoImplicit false

open Set

namespace IsCoveringMap






theorem exists_two_sheet_lift_image_collision
    {A E X : Type*} [TopologicalSpace A] [TopologicalSpace E] [TopologicalSpace X]
    [CompactSpace A] [Nonempty A] [T2Space E] [ConnectedSpace E]
    {p : E → X} (hp : IsCoveringMap p)
    (hcard : ∀ x : X, (p ⁻¹' {x}).ncard = 2)
    (f : C(A, X)) (g : C(A, E)) (hg : ∀ a, p (g a) = f a)
    {r : C(X, X)} (H : (ContinuousMap.id X).HomotopyRel r (range f))
    (hr : ∀ x, r x ∈ range f) :
    ∃ T : E ≃ₜ E, (∀ e, p (T e) = p e) ∧
      (∀ e, T (T e) = e) ∧ (∀ e, T e ≠ e) ∧
      p ⁻¹' range f = range g ∪ T '' range g ∧
      ∃ a b : A, g a = T (g b) ∧ g a ≠ g b ∧ f a = f b := by
  classical
  obtain ⟨T, hTp, hTT, hTne⟩ := hp.exists_two_sheet_involution hcard
  have hfiber (e : E) : p ⁻¹' {p e} = {e, T e} := by
    have hsub : ({e, T e} : Set E) ⊆ p ⁻¹' {p e} := by
      intro y hy
      rcases mem_insert_iff.mp hy with hye | hyT
      · exact congrArg p hye
      · exact (congrArg p (mem_singleton_iff.mp hyT)).trans (hTp e)
    have hfinite : (p ⁻¹' {p e}).Finite := finite_of_ncard_pos (by rw [hcard]; norm_num)
    have hle : (p ⁻¹' {p e}).ncard ≤ ({e, T e} : Set E).ncard := by
      rw [hcard, ncard_pair (hTne e).symm]
    exact (eq_of_subset_of_ncard_le hsub hle hfinite).symm
  have hfull : p ⁻¹' range f = range g ∪ T '' range g := by
    ext e
    constructor
    · rintro ⟨a, ha⟩
      have he : e ∈ p ⁻¹' {p (g a)} := ha.symm.trans (hg a).symm
      rw [hfiber] at he
      rcases mem_insert_iff.mp he with he | he
      · exact Or.inl ⟨a, he.symm⟩
      · exact Or.inr ⟨g a, mem_range_self a, (mem_singleton_iff.mp he).symm⟩
    · rintro (⟨a, rfl⟩ | ⟨y, ⟨a, rfl⟩, rfl⟩)
      · exact ⟨a, (hg a).symm⟩
      · exact ⟨a, ((hTp (g a)).trans (hg a)).symm⟩
  have hconn := hp.isConnected_preimage_of_deformation H hr
  have hclosed : IsClosed (range g) := (isCompact_range g.continuous).isClosed
  have hclosedT : IsClosed (T '' range g) :=
    ((isCompact_range g.continuous).image T.continuous).isClosed
  obtain ⟨a0⟩ := ‹Nonempty A›
  have hleft : (p ⁻¹' range f ∩ range g).Nonempty :=
    ⟨g a0, ⟨a0, (hg a0).symm⟩, mem_range_self a0⟩
  have hright : (p ⁻¹' range f ∩ T '' range g).Nonempty :=
    ⟨T (g a0), ⟨a0, ((hTp (g a0)).trans (hg a0)).symm⟩,
      ⟨g a0, mem_range_self a0, rfl⟩⟩
  obtain ⟨e, _, ⟨a, hae⟩, y, ⟨b, hby⟩, hye⟩ :=
    isPreconnected_closed_iff.mp hconn.isPreconnected (range g) (T '' range g)
      hclosed hclosedT hfull.subset hleft hright
  have hab : g a = T (g b) := hae.trans (hye.symm.trans (congrArg T hby).symm)
  have hne : g a ≠ g b := fun heq => hTne (g b) (hab.symm.trans heq)
  have hproj : f a = f b := (hg a).symm.trans
    ((congrArg p hab).trans ((hTp (g b)).trans (hg b)))
  exact ⟨T, hTp, hTT, hTne, hfull, a, b, hab, hne, hproj⟩

end IsCoveringMap
