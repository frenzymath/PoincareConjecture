import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Surfaces.RimCircles
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.Cuts.RimSubcomplexes

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "R" => latticeHandleDomain (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "B" => latticeHandleBoundary (Fin 1) (Fin 2) L
local notation "C" => AddCircle (4 * (128 : ℝ))

theorem exists_sourceRim_circle_subcomplexes
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (phi : C(H, H)) (theta : C) (F : (ContinuousMap.id H).HomotopyRel phi B)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (G : ↥(sourceSurface phi theta ∩ frontier R) ≃ₜ K.space) :
    ∃ J : Bool → SimplicialComplex ℝ E,
      (∀ side, J side ≤ K) ∧
      Pairwise (fun a b => Disjoint (J a).space (J b).space) ∧
      (⋃ side, (J side).space) = K.space ∧
      (∀ s, s ∈ K.faces ↔ ∃ side, s ∈ (J side).faces) ∧
      ∃ gamma : ∀ side, C ≃ₜ (J side).space,
        ∀ side c, (gamma side c : E) =
          (G ((sourceRimCircleCoordinates phi theta F (originalIntervalEndpoint side)
            (originalIntervalEndpoint_norm side) c).val) : E) := by
  classical
  let : CompactSpace K.space := isCompact_iff_compactSpace.mp (K.isCompact_space_of_finite hK)
  let S : Bool → Set E := fun side => Subtype.val ''
    (G.symm ⁻¹' sourceRimCircle phi theta F (originalIntervalEndpoint side))
  have hSc (side : Bool) : IsClosed (S side) :=
    (((sourceRimCircle_isClopen phi theta F (originalIntervalEndpoint side)).isClosed.preimage
      G.symm.continuous).isCompact.image continuous_subtype_val).isClosed
  have hdis : Pairwise (fun a b => Disjoint (S a) (S b)) := by
    intro a b hab
    apply disjoint_left.mpr
    rintro x ⟨y, hy, rfl⟩ ⟨z, hz, heq⟩
    have hzy : z = y := Subtype.ext heq
    subst z
    exact disjoint_left.mp (sourceRimCircle_two_disjoint phi theta F hab) hy hz
  have hcover : (⋃ side, S side) = K.space := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨side, y, _, rfl⟩ := mem_iUnion.mp hx
      exact y.property
    · intro x hx
      have hz : G.symm ⟨x, hx⟩ ∈
          ⋃ side, sourceRimCircle phi theta F (originalIntervalEndpoint side) := by
        rw [sourceRimCircle_two_cover]
        trivial
      obtain ⟨side, hside⟩ := mem_iUnion.mp hz
      exact mem_iUnion.mpr ⟨side, ⟨⟨x, hx⟩, hside, rfl⟩⟩
  obtain ⟨J, hJK, hJS, hfaces⟩ :=
    Dehn.Annuli.exists_subcomplexes_of_disjoint_closed_cover K hK S hSc hdis hcover
  have hg (side : Bool) : ∃ gamma : C ≃ₜ (J side).space,
      ∀ c, (gamma c : E) =
        (G ((sourceRimCircleCoordinates phi theta F (originalIntervalEndpoint side)
          (originalIntervalEndpoint_norm side) c).val) : E) := by
    let A := sourceRimCircleCoordinates phi theta F (originalIntervalEndpoint side)
      (originalIntervalEndpoint_norm side)
    let f : C → (J side).space := fun c => ⟨G (A c).val, by
      rw [hJS side]
      exact ⟨G (A c).val, by simpa only [mem_preimage, Homeomorph.symm_apply_apply]
        using (A c).property, rfl⟩⟩
    have hc : Continuous f := by fun_prop
    have hi : Function.Injective f := by
      intro c d h
      apply A.injective
      apply Subtype.ext
      apply G.injective
      exact Subtype.ext (congrArg (fun z : (J side).space => (z : E)) h)
    have hs : Function.Surjective f := by
      intro x
      obtain ⟨y, hy, hyx⟩ := (hJS side).subset x.property
      obtain ⟨c, hc⟩ := A.surjective ⟨G.symm y, hy⟩
      refine ⟨c, Subtype.ext ?_⟩
      change (G (A c).val : E) = x.val
      rw [hc]
      simpa only [Homeomorph.apply_symm_apply] using hyx
    exact ⟨hc.isClosedEmbedding hi |>.isEmbedding.toHomeomorphOfSurjective hs, fun _ => rfl⟩
  choose gamma hgamma using hg
  refine ⟨J, hJK, ?_, ?_, hfaces, gamma, hgamma⟩
  · intro a b hab
    simpa only [hJS] using hdis hab
  · simpa only [hJS] using hcover

end PoincareConjecture.M76.HamiltonIntervalTorus
