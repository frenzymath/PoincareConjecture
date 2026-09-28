import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.Reflection.SurgeryStep
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.CapPreservation

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

open Poincare.Geometry.Euclidean Poincare.Geometry.Manifold

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

namespace SphereSurgeryStep

variable {f : S2 → E3} {v : E3} {c R : Real}

@[simp] theorem reflected_capMinusHeights (S : SphereSurgeryStep f v c R) :
    S.reflected.capMinusHeights = Neg.neg '' S.capPlusHeights := by
  rw [capMinusHeights, capPlusHeights, image_image]
  apply image_congr
  intro x _
  exact inner_heightReflection S.unit_v (S.gPlus x)

@[simp] theorem reflected_capPlusHeights (S : SphereSurgeryStep f v c R) :
    S.reflected.capPlusHeights = Neg.neg '' S.capMinusHeights := by
  rw [capPlusHeights, capMinusHeights, image_image]
  apply image_congr
  intro x _
  exact inner_heightReflection S.unit_v (S.gMinus x)

end SphereSurgeryStep

namespace SphereSurgeryTree

variable {v : E3} {A : Finset Real} {f : S2 → E3}

def reflected (hv : ‖v‖ = 1) (T : SphereSurgeryTree v A f) :
    SphereSurgeryTree v (A.image Neg.neg) (heightReflection hv ∘ f) := by
  classical
  induction T with
  | leaf hf hav =>
    refine .leaf (SphereSurgeryStep.sphere_embedding_postcompose (heightReflection hv) hf) ?_
    intro c hc q heq
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hc
    apply hav k hk q
    simpa only [comp_apply, inner_heightReflection, neg_inj] using heq
  | @branch f c R hc hsep S tm tp ihm ihp =>
    refine .branch (c := -c) (R := R) (Finset.mem_image.mpr ⟨c, hc, rfl⟩) ?_
      S.reflected ihp ihm
    intro k hk hkc
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
    have hjc : j ≠ c := fun heq => hkc (congrArg Neg.neg heq)
    simpa only [neg_sub_neg, abs_sub_comm] using hsep j hj hjc

theorem reflected_leaves (hv : ‖v‖ = 1) (T : SphereSurgeryTree v A f) :
    (T.reflected hv).leaves = T.leaves.reverse.map (fun g => heightReflection hv ∘ g) := by
  induction T with
  | leaf hf hav => simp [reflected, leaves]
  | branch hc hsep S tm tp ihm ihp =>
    change (tp.reflected hv).leaves ++ (tm.reflected hv).leaves =
      (tm.leaves ++ tp.leaves).reverse.map (fun g => heightReflection hv ∘ g)
    rw [ihm, ihp, List.reverse_append, List.map_append]

theorem mem_reflected_leaves_iff (hv : ‖v‖ = 1) (T : SphereSurgeryTree v A f)
    (g : S2 → E3) :
    g ∈ (T.reflected hv).leaves ↔ ∃ g₀ ∈ T.leaves, heightReflection hv ∘ g₀ = g := by
  rw [reflected_leaves]
  simp only [List.mem_map, List.mem_reverse]

theorem reflected_mem_leaves (hv : ‖v‖ = 1) (T : SphereSurgeryTree v A f)
    {g : S2 → E3} (hg : g ∈ T.leaves) :
    heightReflection hv ∘ g ∈ (T.reflected hv).leaves :=
  (T.mem_reflected_leaves_iff hv _).mpr ⟨g, hg, rfl⟩

theorem Protects.reflected (hv : ‖v‖ = 1) {T : SphereSurgeryTree v A f} {B : Set Real}
    (hT : T.Protects B) : (T.reflected hv).Protects (Neg.neg '' B) := by
  induction T with
  | leaf => trivial
  | branch hc hsep S tm tp ihm ihp =>
    refine ⟨?_, ihp hT.2.2, ihm hT.2.1⟩
    rintro k ⟨j, hj, rfl⟩
    simpa only [neg_sub_neg, abs_sub_comm] using hT.1 j hj

theorem PreservesCaps.reflected (hv : ‖v‖ = 1) {T : SphereSurgeryTree v A f}
    (hT : T.PreservesCaps) : (T.reflected hv).PreservesCaps := by
  induction T with
  | leaf => trivial
  | branch hc hsep S tm tp ihm ihp =>
    refine ⟨?_, ?_, ihp hT.2.2.2, ihm hT.2.2.1⟩
    · change (tp.reflected hv).Protects S.reflected.capMinusHeights
      rw [S.reflected_capMinusHeights]
      exact hT.2.1.reflected hv
    · change (tm.reflected hv).Protects S.reflected.capPlusHeights
      rw [S.reflected_capPlusHeights]
      exact hT.1.reflected hv

end SphereSurgeryTree

end Poincare.Manifold.Schoenflies
