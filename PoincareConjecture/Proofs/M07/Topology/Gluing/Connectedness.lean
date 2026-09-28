import PoincareConjecture.Proofs.M07.Topology.Gluing.Basic
import Mathlib.Topology.Connected.Basic

open Set Topology

namespace Poincare.Gluing

universe u v

noncomputable section

variable {I : Type u} {P : I → Type v}
  [∀ i, TopologicalSpace (P i)]

theorem OverlapSystem.quotient_preconnectedSpace
    (D : OverlapSystem P)
    [∀ i, Nonempty (P i)] [∀ i, PreconnectedSpace (P i)]
    (i0 : I)
    (hreach : ∀ i, Relation.ReflTransGen
      (fun i j : I => (D.transition i j).source.Nonempty) i0 i) :
    PreconnectedSpace (Quotient D.setoid) := by
  let s : I → Set (Quotient D.setoid) := fun i => Set.range (D.include i)
  have hs : ∀ i, IsPreconnected (s i) := by
    intro i
    rw [show s i = D.include i '' (Set.univ : Set (P i)) by
      ext q; simp [s]]
    exact isPreconnected_univ.image _
      (continuous_quotient_mk'.comp continuous_sigmaMk).continuousOn
  have hedge : ∀ i j, (D.transition i j).source.Nonempty →
      (s i ∩ s j).Nonempty := by
    intro i j hij
    rcases hij with ⟨x, hx⟩
    have heq : D.include i x = D.include j (D.transition i j x) :=
      (D.include_eq_iff i j x (D.transition i j x)).mpr ⟨hx, rfl⟩
    exact ⟨D.include i x, ⟨x, rfl⟩, ⟨D.transition i j x, heq.symm⟩⟩
  let R' : I → I → Prop :=
    fun i j => (s i ∩ s j).Nonempty ∧ i ∈ (Set.univ : Set I)
  have hconnect : ∀ i, Relation.ReflTransGen R' i0 i := by
    intro i
    apply Relation.ReflTransGen.mono
      (fun a b hab => ⟨hedge a b hab, Set.mem_univ _⟩)
    exact hreach i
  have hback : ∀ i, Relation.ReflTransGen R' i i0 := by
    intro i
    have hswap : Relation.ReflTransGen (Function.swap R') i i0 :=
      Relation.ReflTransGen.swap (r := R') i i0 (hconnect i)
    apply Relation.ReflTransGen.mono (r := Function.swap R') (p := R') (fun a b hab => by
      change R' b a at hab
      exact ⟨by simpa [inter_comm] using hab.1, Set.mem_univ _⟩)
    exact hswap
  have hu : (⋃ i, s i) = (Set.univ : Set (Quotient D.setoid)) := by
    simpa [s] using D.include_cover
  refine ⟨?_⟩
  rw [← hu]
  simpa using
    (IsPreconnected.biUnion_of_reflTransGen (t := (Set.univ : Set I))
      (fun i _ => hs i)
      (fun i _ j _ => (hback i).trans (hconnect j)))

theorem OverlapSystem.quotient_connectedSpace
    (D : OverlapSystem P) [∀ i, ConnectedSpace (P i)]
    (i0 : I)
    (hreach : ∀ i, Relation.ReflTransGen
      (fun i j : I => (D.transition i j).source.Nonempty) i0 i) :
    ConnectedSpace (Quotient D.setoid) := by
  let := D.quotient_preconnectedSpace i0 hreach
  exact ⟨⟨D.include i0 (Classical.choice inferInstance)⟩⟩

end

end Poincare.Gluing
