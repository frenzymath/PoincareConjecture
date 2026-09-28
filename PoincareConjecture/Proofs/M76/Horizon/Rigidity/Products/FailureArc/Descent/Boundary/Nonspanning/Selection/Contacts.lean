import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Nonspanning.Selection.Exteriors
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Nonspanning.Chain.Maps.PuncturedCopies
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.Mathlib.TubeArmOrientation
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.ResolutionTubeFibers



set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn.NonspanningStripExteriors

open PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)
local notation "I01" => Icc (0 : ℝ) 1

variable {c : Bool → P2 → P2} {D T : Set P2} (E : NonspanningStripExteriors c D T)

def firstArm (t : I01) : P2 := c false ((t : ℝ), farArmParameter (!E.s0))
def leftArm (t : I01) : P2 := c true ((t : ℝ), farArmParameter E.s1)
def rightArm (t : I01) : P2 := c false ((t : ℝ), farArmParameter E.s0)
def lastArm (t : I01) : P2 := c true ((t : ℝ), farArmParameter (!E.s1))

theorem retained_ball (i : NonspanningRetainedPiece) :
    IsFinitePLBallPair P2 (E.chain.retainedSet i) (frontier (E.chain.retainedSet i)) := by
  cases i
  · exact (E.first_ball.frontier_eq_of_finrank_eq rfl).symm ▸ E.first_ball
  · exact (E.middle_ball.frontier_eq_of_finrank_eq rfl).symm ▸ E.middle_ball
  · exact (E.last_ball.frontier_eq_of_finrank_eq rfl).symm ▸ E.last_ball

theorem retained_subset (i : NonspanningRetainedPiece) : E.chain.retainedSet i ⊆ T := by
  intro x hx
  apply E.cover.subset
  cases i
  · exact Or.inl (Or.inl (Or.inl hx))
  · exact Or.inl (Or.inl (Or.inr hx))
  · exact Or.inl (Or.inr hx)

theorem retained_PL
    {X ι : Type*} [TopologicalSpace X] {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)}
    {f : P2 → X} (hD : IsFinitePLBallPair P2 D (frontier D))
    (hf : PolyhedralPLInCharts e f (T \ interior D)) (i : NonspanningRetainedPiece) :
    PolyhedralPLInCharts e f (E.chain.retainedSet i \ interior D) := by
  obtain ⟨K, hK, hKs⟩ := E.hole.source_complex E.retained_ball hD (.inl i)
  have hsub : K.space ⊆ T \ interior D := by
    intro x hx
    have hh := hKs.subset hx
    exact ⟨E.retained_subset i hh.1, hh.2⟩
  simpa only [hKs, NonspanningChainHole.sourceSet] using hf.restrict_finite K hK hsub

theorem arm_range (j b : Bool) :
    c j '' arm (farArmParameter b) = range (fun t : I01 ↦ c j ((t : ℝ), farArmParameter b)) := by
  ext x
  constructor
  · rintro ⟨⟨t, u⟩, ⟨ht, hu⟩, rfl⟩
    have he : u = farArmParameter b := hu
    subst u
    exact ⟨⟨t, ht⟩, rfl⟩
  · rintro ⟨t, rfl⟩
    exact ⟨((t : ℝ), farArmParameter b), ⟨t.property, rfl⟩, rfl⟩

theorem oriented_corner_equations {X : Type*} {f : P2 → X} {τ : C3 → X}
    (h0 : ∀ p ∈ source, f (c false p) = τ ((p.2, p.2), p.1))
    (h1 : ∀ p ∈ source, f (c true p) = τ ((p.2, -p.2), p.1)) (t : I01) :
    f (E.firstArm t) = (τ ∘ tubeArmOrientation E.s0 E.s1) ((-1, 1), t) ∧
    f (E.leftArm t) = (τ ∘ tubeArmOrientation E.s0 E.s1) ((-1, -1), t) ∧
    f (E.rightArm t) = (τ ∘ tubeArmOrientation E.s0 E.s1) ((1, -1), t) ∧
    f (E.lastArm t) = (τ ∘ tubeArmOrientation E.s0 E.s1) ((1, 1), t) :=
  reoriented_tube_old_arm_equations f (c false) (c true) τ h0 h1 E.s0 E.s1 t

theorem oriented_tube_preimages {X : Type*} {f : P2 → X} {τ : C3 → X}
    (hfull : (T \ interior D) ∩ f ⁻¹' (τ '' tube) = c false '' source ∪ c true '' source) :
    (E.first \ interior D) ∩ f ⁻¹' ((τ ∘ tubeArmOrientation E.s0 E.s1) '' tube) = range E.firstArm ∧
    (E.middle \ interior D) ∩ f ⁻¹' ((τ ∘ tubeArmOrientation E.s0 E.s1) '' tube) =
      range E.leftArm ∪ range E.rightArm ∧
    (E.last \ interior D) ∩ f ⁻¹' ((τ ∘ tubeArmOrientation E.s0 E.s1) '' tube) = range E.lastArm := by
  have hrestrict (V W : Set P2) (j : Bool) (hcontact : c j '' source ∩ V = W) :
      (V \ interior D) ∩ (c j '' source) = W := by
    ext x
    constructor
    · intro hx
      exact hcontact.subset ⟨hx.2, hx.1.1⟩
    · intro hx
      have hh := hcontact.symm.subset hx
      have hs : x ∈ c false '' source ∪ c true '' source := by
        cases j
        · exact Or.inl hh.1
        · exact Or.inr hh.1
      exact ⟨⟨hh.2, (hfull.symm.subset hs).1.2⟩, hh.1⟩
  have hA0 := hrestrict E.first _ false E.strip_first
  have hM0 := hrestrict E.middle _ false E.strip_middle0
  have hM1 := hrestrict E.middle _ true E.strip_middle1
  have hC1 := hrestrict E.last _ true E.strip_last
  have hA1 : (E.first \ interior D) ∩ (c true '' source) = ∅ :=
    (E.opposite_first.mono_left sdiff_subset).eq_bot
  have hC0 : (E.last \ interior D) ∩ (c false '' source) = ∅ :=
    (E.opposite_last.mono_left sdiff_subset).eq_bot
  have hsub (i : NonspanningRetainedPiece) :
      E.chain.retainedSet i \ interior D ⊆ T \ interior D :=
    fun x hx ↦ ⟨E.retained_subset i hx.1, hx.2⟩
  have hA := retained_tube_preimage hfull (hsub .first) hA0 hA1
  have hM := retained_tube_preimage hfull (hsub .middle) hM0 hM1
  have hC := retained_tube_preimage hfull (hsub .last) hC0 hC1
  rw [reoriented_tube_image]
  refine ⟨?_, ?_, ?_⟩
  · change _ = range (fun t : I01 ↦ c false ((t : ℝ), farArmParameter (!E.s0)))
    simpa only [union_empty, arm_range, NonspanningChainGeometry.retainedSet] using hA
  · change _ = range (fun t : I01 ↦ c true ((t : ℝ), farArmParameter E.s1)) ∪
      range (fun t : I01 ↦ c false ((t : ℝ), farArmParameter E.s0))
    simpa only [arm_range, union_comm, NonspanningChainGeometry.retainedSet] using hM
  · change _ = range (fun t : I01 ↦ c true ((t : ℝ), farArmParameter (!E.s1)))
    simpa only [empty_union, arm_range, NonspanningChainGeometry.retainedSet] using hC

end PoincareConjecture.M76.Dehn.NonspanningStripExteriors
