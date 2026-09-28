import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Collars.CollaredNullLoopFilling
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Disks.CollarEnlargedFilling
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Disks.FrontierAvoidingReplacement

set_option autoImplicit false

open Set Metric unitInterval

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1

theorem exists_collared_null_circle_deletion
    {X : Type*} [TopologicalSpace X] {Y U F : Set X}
    (hUY : U ⊆ Y) (G : (F × Ioo (-1 : ℝ) 1) ≃ₜ U)
    (hGbase : ∀ y : F, (G (y, ⟨0, by norm_num⟩) : X) = y)
    (hGzero : ∀ z, (G z : X) ∈ F ↔ (z.2 : ℝ) = 0)
    {g : V2 → X} (hg : ContinuousOn g D) (hgY : MapsTo g D Y)
    {B : Set V2} (a : D ≃ₜ B) (c : C(Q × I, V2)) (hc : Function.Injective c)
    (hcbase : ∀ u : Q, c (u, 0) = (a ⟨u, sphere_subset_closedBall u.property⟩ : V2))
    (hcout : ∀ (u : Q) (t : I), 0 < (t : ℝ) → c (u, t) ∉ B)
    (hE : IsClosed (B ∪ range c)) (hED : B ∪ range c ⊆ interior D)
    (hfront : frontier (B ∪ range c) ⊆ range (fun u : Q => c (u, 1)))
    (hcU : ∀ z : Q × I, g (c z) ∈ U)
    {S : Set (Set V2)} (hS : S.Finite) (hdisj : S.PairwiseDisjoint id)
    {s : Set V2} (hs : s ∈ S) (hsB : s ⊆ B)
    (hinter : (B ∪ range c) ∩ (⋃ t ∈ S, t) = s)
    (hcover : D ∩ g ⁻¹' F = ⋃ t ∈ S, t)
    (gamma : C(Q, F))
    (hgamma : ∀ u : Q, (gamma u : X) = g (a ⟨u, sphere_subset_closedBall u.property⟩))
    (hnull : gamma.Nullhomotopic) :
    ∃ g' : V2 → X, ContinuousOn g' D ∧ MapsTo g' D Y ∧
      EqOn g' g (B ∪ range c)ᶜ ∧ EqOn g' g (frontier D) ∧
      (∀ x ∈ B ∪ range c, g' x ∉ F) ∧
      D ∩ g' ⁻¹' F = ⋃ t ∈ S \ {s}, t ∧
      (S \ {s}).Finite ∧ (S \ {s}).PairwiseDisjoint id ∧
      (S \ {s}).ncard = S.ncard - 1 ∧ (S \ {s}).ncard < S.ncard := by
  have hcD : MapsTo c univ D := fun z _ =>
    interior_subset (hED (Or.inr (mem_range_self z)))
  have hgc : Continuous (fun z : Q × I => g (c z)) :=
    hg.comp_continuous c.continuous (fun z => hcD (mem_univ z))
  let A : C(I × Q, U) :=
    ⟨fun z => ⟨g (c (z.2, z.1)), hcU (z.2, z.1)⟩,
      (hgc.comp continuous_swap).subtype_mk _⟩
  have hA0 (u : Q) : A (0, u) = G (gamma u, ⟨0, by norm_num⟩) := by
    apply Subtype.ext
    change g (c (u, 0)) = (G (gamma u, ⟨0, by norm_num⟩) : X)
    rw [hcbase, hGbase, hgamma]
  have hA1 (u : Q) : (A (1, u) : X) ∉ F := by
    intro hu
    have hcE : c (u, 1) ∈ B ∪ range c := Or.inr (mem_range_self (u, 1))
    have hcs : c (u, 1) ∈ s := hinter.subset
      ⟨hcE, hcover.subset ⟨interior_subset (hED hcE), hu⟩⟩
    exact hcout u 1 (by norm_num) (hsB hcs)
  obtain ⟨f, hfouter, hfavoid⟩ :=
    PLDomain.exists_collared_null_loop_filling G hGzero gamma A hA0 hA1 hnull
  obtain ⟨fillU, _, _, hfillouter, hfillavoid⟩ :=
    exists_collar_enlarged_filling a c hc hcbase hcout f
      (F := (Subtype.val : U → X) ⁻¹' F) hfavoid
  let fill : C(↥(B ∪ range c), Y) := (ContinuousMap.inclusion hUY).comp fillU
  have hfillrim (x : ↥(B ∪ range c)) (hx : (x : V2) ∈ frontier (B ∪ range c)) :
      (fill x : X) = g x := by
    obtain ⟨u, hu⟩ := hfront hx
    have hx' : x = (⟨c (u, 1), Or.inr (mem_range_self (u, 1))⟩ : ↥(B ∪ range c)) :=
      Subtype.ext hu.symm
    rw [hx']
    change (fillU ⟨c (u, 1), Or.inr (mem_range_self (u, 1))⟩ : X) = g (c (u, 1))
    exact congrArg (Subtype.val : U → X) ((hfillouter u).trans (hfouter u))
  have hfillF (x : ↥(B ∪ range c)) : (fill x : X) ∉ F := hfillavoid x
  obtain ⟨g', hg', hg'Y, hfill, hout, hboundary, hpreimage, hfinite, hpair,
    hcount, hdecrease⟩ := exists_frontier_avoiding_family_deletion hE hED hg hgY
      fill hfillrim hfillF hS hdisj hs hinter hcover
  refine ⟨g', hg', hg'Y, hout, hboundary, ?_, hpreimage, hfinite, hpair,
    hcount, hdecrease⟩
  intro x hx
  rw [hfill ⟨x, hx⟩]
  exact hfillF ⟨x, hx⟩

end PoincareConjecture.M76
