import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.AlternateResolutionTargetFibers
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.RetainedDoubleRelation

set_option autoImplicit false

open Set Metric

namespace PoincareConjecture.M76.Dehn.PolygonalCrossingResolution

local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "I01" => Icc (0 : ℝ) 1

theorem alternate_retained_double_relation
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S A M C B0 B1 : Set E} {f : E → X} {τ : C3 → X} {g : V2 → X}
    {pA pL pR pC : I01 → E}
    (s : AlternateResolutionSources A M C source pA pL pR pC minusArmPoint plusArmPoint
      f (τ ∘ alternate (1 / 4) false) f (τ ∘ alternate (1 / 4) true) f g)
    (hAM : Disjoint A M) (hAC : Disjoint A C) (hMC : Disjoint M C)
    (hτ : InjOn τ tube)
    (hfull : S ∩ f ⁻¹' (τ '' tube) = B0 ∪ B1)
    (hAS : A ⊆ S) (hMS : M ⊆ S) (hCS : C ⊆ S)
    (hA0 : A ∩ B0 = range pA) (hA1 : A ∩ B1 = ∅)
    (hM0 : M ∩ B0 = range pR) (hM1 : M ∩ B1 = range pL)
    (hC0 : C ∩ B0 = ∅) (hC1 : C ∩ B1 = range pC)
    (hA : ∀ t : I01, f (pA t) = τ ((-1, 1), t))
    (hL : ∀ t : I01, f (pL t) = τ ((-1, -1), t))
    (hR : ∀ t : I01, f (pR t) = τ ((1, -1), t))
    (hC : ∀ t : I01, f (pC t) = τ ((1, 1), t)) :
    let jAM := joinSourceCopies hAM s.jA s.jM
    let j := joinSourceCopies (disjoint_union_left.mpr ⟨hAC, hMC⟩) jAM s.jC
    Function.Injective j ∧ range j = (range s.jA ∪ range s.jM) ∪ range s.jC ∧
      (∀ x : ((A ∪ M) ∪ C : Set E), g (j x) = f x) ∧
      {v : V2 × V2 | v.1 ∈ D ∧ v.2 ∈ D ∧ g v.1 = g v.2 ∧ v.1 ≠ v.2} =
        (fun v : ((A ∪ M) ∪ C : Set E) × ((A ∪ M) ∪ C : Set E) ↦ (j v.1, j v.2)) ''
          {v | f v.1 = f v.2 ∧ (v.1 : E) ≠ v.2} ∧
      {z : V2 | z ∈ D ∧ ∃ w ∈ D, g z = g w ∧ z ≠ w} =
        j '' {x : ((A ∪ M) ∪ C : Set E) |
          ∃ y : ((A ∪ M) ∪ C : Set E), f x = f y ∧ (x : E) ≠ y} := by
  let jAM := joinSourceCopies hAM s.jA s.jM
  have hAMC : Disjoint (A ∪ M) C := disjoint_union_left.mpr ⟨hAC, hMC⟩
  let j := joinSourceCopies hAMC jAM s.jC
  have harms : Disjoint (range minusArmPoint) (range plusArmPoint) := by
    apply disjoint_left.mpr
    rintro z ⟨u, rfl⟩ ⟨v, hv⟩
    have hbad := congrArg (fun x : source ↦ x.val.2) hv
    norm_num [minusArmPoint, plusArmPoint] at hbad
  have hjAM : Function.Injective jAM := joinSourceCopies_injective hAM
    s.embeddings.1.injective s.embeddings.2.2.1.injective (s.disjoint_A_middle harms)
  have hAMimage : range jAM = range s.jA ∪ range s.jM := joinSourceCopies_range hAM _ _
  have himages : Disjoint (range jAM) (range s.jC) := by
    rw [hAMimage]
    exact disjoint_union_left.mpr ⟨s.disjoint_A_C harms, s.disjoint_middle_C harms⟩
  have hj : Function.Injective j := joinSourceCopies_injective hAMC
    hjAM s.embeddings.2.2.2.2.injective himages
  have hrange : range j = (range s.jA ∪ range s.jM) ∪ range s.jC := by
    rw [joinSourceCopies_range, hAMimage]
  have hkeepAM (x : (A ∪ M : Set E)) : g (jAM x) = f x :=
    joinSourceCopies_target hAM s.keepA s.keepM x
  have hkeep (x : ((A ∪ M) ∪ C : Set E)) : g (j x) = f x :=
    joinSourceCopies_target hAMC hkeepAM s.keepC x
  have hcover : range j ∪ (range s.jL ∪ range s.jR) = D := by
    rw [hrange, ← s.cover]
    ac_rfl
  have hsingle : ∀ z ∈ range s.jL ∪ range s.jR, ∀ w ∈ D, g w = g z → w = z := by
    rintro z (⟨y, rfl⟩ | ⟨y, rfl⟩) w hw h
    · exact (alternate_strip_target_fibers s hτ hfull hAS hMS hCS hA0 hA1 hM0 hM1
        hC0 hC1 hA hL hR hC y hw).1.mp h
    · exact (alternate_strip_target_fibers s hτ hfull hAS hMS hCS hA0 hA1 hM0 hM1
        hC0 hC1 hA hL hR hC y hw).2.mp h
  exact ⟨hj, hrange, hkeep, retained_double_relation_eq j hj hcover hkeep hsingle,
    retained_double_locus_eq j hj hcover hkeep hsingle⟩

end PoincareConjecture.M76.Dehn.PolygonalCrossingResolution
