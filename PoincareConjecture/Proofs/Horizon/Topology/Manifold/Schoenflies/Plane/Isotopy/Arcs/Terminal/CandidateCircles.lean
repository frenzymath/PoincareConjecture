import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.ModelCandidates
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.ReflectedModelNesting
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.ModelNesting
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.ActualMarkedCircles
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.NestingSelection



noncomputable section
set_option autoImplicit false
open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.PlaneArcs.Terminal
open SaddleLevel Plane.Isotopy.ArcPairs
private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1

variable {f : S2 → E3} {M : SphereMorseReduction f} {g : S2 → E3}
  {P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g}
  {p : S2} {e : OpenPartialHomeomorph E2 S2}



theorem exists_matching_terminal_candidate_circles
    (hg : g ∈ M.tree.leaves) (ds : Fin 3 → TerminalSaddleGeometry M P p e)
    (hzero : (ds 0).model = Saddle.shear)
    (hone : (ds 1).model = Saddle.Nested.shear (3 / 10))
    (htwo : (ds 2).model = Saddle.Nested.shear (3 / 10))
    (hscale : (ds 2).scale = (ds 1).scale)
    (hchart : (ds 2).modelChart = negativeBranchReflectedChart (ds 1).modelChart)
    (hD : ∀ i, (ds i).D = (ds 0).D)
    (hframe : ∀ i, (ds i).frame = (ds 0).frame)
    (hP : P.Protects ((fun q => inner Real (M.v : E3) (M.D (f q))) ''
      {q | mfderiv (𝓡 2) 𝓘(Real, Real)
        (fun y => inner Real (M.v : E3) (M.D (f y))) q = 0}))
    (hcaps : P.PreservesCaps) (hp : p ∈ P.core)
    (hc : mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => inner Real (M.v : E3) (g q)) p = 0)
    (hunique : ∀ q ∈ P.core,
      mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => inner Real (M.v : E3) (g q)) q = 0 → q = p)
    (he0 : 0 ∈ e.source) (hep : e 0 = p)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    (hform : ∀ x ∈ e.source, inner Real (M.v : E3) (g (e x)) =
      inner Real (M.v : E3) (g p) - x 0 ^ 2 + x 1 ^ 2)
    (hcount : Nat.card (ds 0).ends.LowerCutIndex = 2) :
    ∃ ε : Real, 0 < ε ∧ ∀ t ∈ Ioc (0 : Real) ε,
      ∃ k : Fin 3, ∃ C D : Fin 2 → S1 → E2,
        (∀ i, _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ (C i)) ∧
        (∀ i, _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ (D i)) ∧
        Injective (fun x : Fin 2 × S1 => C x.1 x.2) ∧
        Injective (fun x : Fin 2 × S1 => D x.1 x.2) ∧
        (⋃ i, range (C i)) = (ds k).A (inner Real (M.v : E3) (g p) - t) ∧
        (⋃ i, range (D i)) = (ds k).B (inner Real (M.v : E3) (g p) - t) ∧
        (∀ i, Saddle.toE2 ((ds k).flatten (g (e (negativeLevelArc t i 0)))) ∈ range (C i)) ∧
        (∀ i, Saddle.toE2 ((ds k).flatten (g (e (negativeLevelArc t i 0)))) ∈ range (D i)) ∧
        ∀ i j : Fin 2, i ≠ j → (NestedPair (C i) (C j) ↔ NestedPair (D i) (D j)) := by
  classical
  obtain ⟨rA, δA, _, _, hδA, _, hδAr, hactual⟩ :=
    exists_actual_negative_branch_circle_pairs hg (ds 0) hP hcaps hp hc hunique
      he0 hep he hei hform hcount
  obtain ⟨r0, δ0, _, _, hδ0, _, hδ0r, hstandard⟩ :=
    exists_standard_model_negative_branch_circle_pairs_unnested (ds 0) hzero hform
  obtain ⟨δN, hδN, hnested⟩ := exists_oppositely_nested_model_circle_pairs
    (ds 1) (ds 2) hone htwo hscale hchart hform
  refine ⟨min δA (min δ0 δN), lt_min hδA (lt_min hδ0 hδN), ?_⟩
  intro t ht
  have htA : t ∈ Ioc (0 : Real) δA := ⟨ht.1, ht.2.trans (min_le_left _ _)⟩
  have ht0 : t ∈ Ioc (0 : Real) δ0 :=
    ⟨ht.1, ht.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
  have htN : t ∈ Ioc (0 : Real) δN :=
    ⟨ht.1, ht.2.trans ((min_le_right _ _).trans (min_le_right _ _))⟩
  obtain ⟨C, hC, hiC, hcoverC, hbranchC⟩ := hactual t htA
  obtain ⟨D0, h0, hi0, hcover0, hbranch0, hn0, hn0'⟩ := hstandard t ht0
  obtain ⟨D1, D2, h1, h2, hi1, hi2, hcover1, hcover2, hctr1, hctr2,
    _, _, hnest⟩ := hnested t htN
  let D : Fin 3 → Fin 2 → S1 → E2 := ![D0, D1, D2]
  have hsm (k : Fin 3) (i) :
      _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ (D k i) := by
    fin_cases k
    · exact h0 i
    · exact h1 i
    · exact h2 i
  have hnest1 : NestedPair (D 1 0) (D 1 1) ∨ NestedPair (D 1 1) (D 1 0) := by
    rcases hnest with h | h
    · exact Or.inl h.1
    · exact Or.inr h.1
  have hflip : (NestedPair (D 2 0) (D 2 1) ↔ NestedPair (D 1 1) (D 1 0)) ∧
      (NestedPair (D 2 1) (D 2 0) ↔ NestedPair (D 1 0) (D 1 1)) := by
    have ha := nestedPair_asymm_of_smooth (D1 0) (D1 1) (h1 0) (h1 1)
    have hb := nestedPair_asymm_of_smooth (D1 1) (D1 0) (h1 1) (h1 0)
    have hc' := nestedPair_asymm_of_smooth (D2 0) (D2 1) (h2 0) (h2 1)
    have hd := nestedPair_asymm_of_smooth (D2 1) (D2 0) (h2 1) (h2 0)
    change (NestedPair (D2 0) (D2 1) ↔ NestedPair (D1 1) (D1 0)) ∧
      (NestedPair (D2 1) (D2 0) ↔ NestedPair (D1 0) (D1 1))
    rcases hnest with h | h
    · exact ⟨⟨fun h' => (hd h.2 h').elim, fun h' => (ha h.1 h').elim⟩,
        ⟨fun _ => h.1, fun _ => h.2⟩⟩
    · exact ⟨⟨fun _ => h.1, fun _ => h.2⟩,
        ⟨fun h' => (hc' h.2 h').elim, fun h' => (hb h.1 h').elim⟩⟩
  obtain ⟨k, hk⟩ := exists_circle_candidate_with_matching_nesting C D hC hsm
    hn0 hn0' hnest1 hflip
  have hflat (k) : (ds k).flatten = (ds 0).flatten := by
    simp only [TerminalSaddleGeometry.flatten, hD k, hframe k]
  have hA (k) : (ds k).A = (ds 0).A := by
    funext z
    change {x | Saddle.toE3 x z ∈ (ds k).flatten '' range g} =
      {x | Saddle.toE3 x z ∈ (ds 0).flatten '' range g}
    rw [hflat k]
  refine ⟨k, C, D k, hC, hsm k, hiC, ?_, ?_, ?_, ?_, ?_, hk⟩
  · fin_cases k
    · exact hi0
    · exact hi1
    · exact hi2
  · rw [hA]
    exact hcoverC
  · fin_cases k
    · exact hcover0
    · exact hcover1
    · exact hcover2
  · intro i
    rw [hflat]
    exact hbranchC i 0 ⟨by linarith [hyperbolaRadius_pos (htA.2.trans_lt hδAr)],
      (hyperbolaRadius_pos (htA.2.trans_lt hδAr)).le⟩
  · fin_cases k
    · intro i
      exact hbranch0 i 0 ⟨by linarith [hyperbolaRadius_pos (ht0.2.trans_lt hδ0r)],
        (hyperbolaRadius_pos (ht0.2.trans_lt hδ0r)).le⟩
    · exact hctr1
    · exact hctr2

end Poincare.Manifold.Schoenflies.PlaneArcs.Terminal
