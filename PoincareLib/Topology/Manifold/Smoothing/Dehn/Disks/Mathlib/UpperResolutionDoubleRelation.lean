import PoincareLib.Topology.Manifold.Smoothing.Dehn.Disks.Mathlib.UpperResolutionTargetFibers
import PoincareLib.Topology.Manifold.Smoothing.Dehn.Disks.Mathlib.RetainedDoubleRelation

/-!
# Exact retained double relation of the normalized upper candidate

The actual source-copy map on the two retained exterior disks transports
exactly the old distinct-point target relation and its projected double
locus. Every replacement-strip fiber is proved singleton from the original
full tube-preimage equation and prescribed source contacts.
-/

set_option autoImplicit false

open Set Metric

namespace PoincareMT.M76.Dehn.PolygonalCrossingResolution

local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "I01" => Icc (0 : ℝ) 1

/-- The complete actual upper double relation and double locus are images
of precisely the old relation restricted to the retained outer disks. -/
theorem upper_retained_double_relation
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S A C B0 B1 : Set E} {f : E → X} {τ : C3 → X} {g : V2 → X}
    {pA pC : I01 → E}
    (s : UpperResolutionSources A C source pA pC minusArmPoint plusArmPoint
      f (τ ∘ strip (1 / 4) true) f g)
    (hAC : Disjoint A C) (hτ : InjOn τ tube)
    (hfull : S ∩ f ⁻¹' (τ '' tube) = B0 ∪ B1) (hAS : A ⊆ S) (hCS : C ⊆ S)
    (hA0 : A ∩ B0 = range pA) (hA1 : A ∩ B1 = ∅)
    (hC0 : C ∩ B0 = ∅) (hC1 : C ∩ B1 = range pC)
    (hA : ∀ t : I01, f (pA t) = τ ((-1, 1), t))
    (hC : ∀ t : I01, f (pC t) = τ ((1, 1), t)) :
    let j := joinSourceCopies hAC s.jA s.jC
    Function.Injective j ∧ range j = range s.jA ∪ range s.jC ∧
      (∀ x : (A ∪ C : Set E), g (j x) = f x) ∧
      {v : V2 × V2 | v.1 ∈ D ∧ v.2 ∈ D ∧ g v.1 = g v.2 ∧ v.1 ≠ v.2} =
        (fun v : (A ∪ C : Set E) × (A ∪ C : Set E) ↦ (j v.1, j v.2)) ''
          {v | f v.1 = f v.2 ∧ (v.1 : E) ≠ v.2} ∧
      {z : V2 | z ∈ D ∧ ∃ w ∈ D, g z = g w ∧ z ≠ w} =
        j '' {x : (A ∪ C : Set E) | ∃ y : (A ∪ C : Set E), f x = f y ∧ (x : E) ≠ y} := by
  let j := joinSourceCopies hAC s.jA s.jC
  have harms : Disjoint (range minusArmPoint) (range plusArmPoint) := by
    apply disjoint_left.mpr
    rintro z ⟨u, rfl⟩ ⟨v, hv⟩
    have hbad := congrArg (fun x : source ↦ x.val.2) hv
    norm_num [minusArmPoint, plusArmPoint] at hbad
  have hj : Function.Injective j := joinSourceCopies_injective hAC
    s.embeddings.1.injective s.embeddings.2.2.injective (s.disjoint_outer harms)
  have hrange : range j = range s.jA ∪ range s.jC := joinSourceCopies_range hAC _ _
  have hkeep (x : (A ∪ C : Set E)) : g (j x) = f x :=
    joinSourceCopies_target hAC s.keepA s.keepC x
  have hcover : range j ∪ range s.jS = D := by
    rw [hrange, ← s.cover]
    ac_rfl
  have hsingle : ∀ z ∈ range s.jS, ∀ w ∈ D, g w = g z → w = z := by
    rintro z ⟨y, rfl⟩ w hw h
    exact (upper_strip_target_fiber s hτ hfull hAS hCS hA0 hA1 hC0 hC1 hA hC y hw).mp h
  exact ⟨hj, hrange, hkeep, retained_double_relation_eq j hj hcover hkeep hsingle,
    retained_double_locus_eq j hj hcover hkeep hsingle⟩

end PoincareMT.M76.Dehn.PolygonalCrossingResolution
