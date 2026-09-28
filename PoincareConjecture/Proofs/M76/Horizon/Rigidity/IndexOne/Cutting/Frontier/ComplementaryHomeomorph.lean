import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Cutting.Frontier.StripReversal
import PoincareConjecture.Proofs.M76.Mathlib.CompactHomeomorphGluing

set_option autoImplicit false
open Set Metric

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "R" => latticeHandleDomain (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "B" => latticeHandleBoundary (Fin 1) (Fin 2) L
local notation "p" => (4 * (128 : ℝ))
local notation "C" => AddCircle p

private instance : Fact (0 < p) := ⟨by norm_num⟩

theorem exists_complementary_frontier_homeomorph
    (phi : C(H, H)) (F : (ContinuousMap.id H).HomotopyRel phi B)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < p)
    (hfront : frontier (sourceSlab phi a b) =
      (sourceSlab phi a b ∩ frontier R) ∪
        (sourceSurface phi (a : C) ∪ sourceSurface phi (b : C)))
    (hfront' : frontier (sourceSlab phi b (a + p)) =
      (sourceSlab phi b (a + p) ∩ frontier R) ∪
        (sourceSurface phi (a : C) ∪ sourceSurface phi (b : C))) :
    ∃ G : ↥(frontier (sourceSlab phi a b)) ≃ₜ
        ↥(frontier (sourceSlab phi b (a + p))),
      (∀ x : frontier (sourceSlab phi a b),
        (x : X) ∈ sourceSurface phi (a : C) ∪ sourceSurface phi (b : C) →
          (G x : X) = x) ∧
      ∀ x : ↥(sourceSlab phi a b ∩ frontier R),
        (G ⟨x, hfront.symm ▸ Or.inl x.property⟩ : X) =
          complementaryOldStripReversal phi a b F hab (by linarith) x := by
  classical
  let : T2Space ((Fin 2 → ℝ) ⧸ (hamiltonLowerPeriodLattice (Fin 2)).toAddSubgroup) :=
    (hamiltonLowerLatticePiEquiv (Fin 2)).isEmbedding.t2Space
  let q : C(R, C) := (sourcePhase phi).comp
    ⟨latticeHandleDomainEquiv (Fin 1) (Fin 2) L,
      (latticeHandleDomainEquiv (Fin 1) (Fin 2) L).continuous⟩
  have hR := isCompact_latticeHandleDomain (Fin 1) (Fin 2) L
  let : CompactSpace R := isCompact_iff_compactSpace.mp hR
  let S := sourceSurface phi (a : C) ∪ sourceSurface phi (b : C)
  let A := sourceSlab phi a b ∩ frontier R
  let A' := sourceSlab phi b (a + p) ∩ frontier R
  have hSc (theta : C) : IsCompact (sourceSurface phi theta) :=
    ((isClosed_singleton.preimage q.continuous).isCompact).image continuous_subtype_val
  have hAc : IsCompact A :=
    (((AddCircle.isCompact_closedIntervalArc p a b).isClosed.preimage q.continuous).isCompact.image
      continuous_subtype_val).inter_right isClosed_frontier
  have hS : IsCompact S := (hSc (a : C)).union (hSc (b : C))
  have hSN : S ⊆ sourceSlab phi a b := by
    intro x hx
    have hxR : x ∈ R := hx.elim (fun h => sourceSurface_subset phi (a : C) h)
      (fun h => sourceSurface_subset phi (b : C) h)
    let x' : R := ⟨x, hxR⟩
    apply (mem_sourceSlab_iff phi a b x').mpr
    rcases hx with hx | hx
    · rw [(mem_sourceSurface_iff phi (a : C) x').mp hx]
      exact ⟨a, ⟨le_rfl, hab.le⟩, rfl⟩
    · rw [(mem_sourceSurface_iff phi (b : C) x').mp hx]
      exact ⟨b, ⟨hab.le, le_rfl⟩, rfl⟩
  let E : A ≃ₜ A' := complementaryOldStripReversal phi a b F hab (by linarith)
  have hfix (x : A) (hx : (x : X) ∈ S) : (E x : X) = x :=
    complementaryOldStripReversal_fixed phi a b F hab (by linarith) x hx
  have hoverlap (x : A) : (x : X) ∈ S ↔ (E x : X) ∈ S := by
    constructor
    · intro hx
      rwa [hfix x hx]
    · intro hx
      let y : A := ⟨E x, hSN hx, (E x).property.2⟩
      have hy : (E y : X) = E x := hfix y hx
      have hyx : y = x := E.injective (Subtype.ext hy)
      have heqx : (E x : X) = x := congrArg Subtype.val hyx
      rwa [heqx] at hx
  obtain ⟨G, hGA, hGS⟩ := Homeomorph.exists_union_of_compact hAc hS E (Homeomorph.refl S)
    hoverlap (fun x hA hS => hfix ⟨x, hA⟩ hS)
  let G' := (Homeomorph.setCongr hfront).trans
    (G.trans (Homeomorph.setCongr hfront'.symm))
  refine ⟨G', ?_, ?_⟩
  · intro x hx
    exact hGS ⟨x, hx⟩
  · intro x
    exact hGA x

end PoincareConjecture.M76.HamiltonIntervalTorus
