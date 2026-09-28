import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.ChartCircleMatching
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.BranchContinuation
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.TerminalData







open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.Poincare.Manifold.Schoenflies.PlaneArcs
open _root_.Poincare.Manifold.Schoenflies.PlaneArcs.Terminal
open _root_.PoincareConjecture

namespace M38Schoenflies



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.PlaneArcs.Terminal

open SaddleLevel Plane.Isotopy.ArcPairs

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1

private theorem pair_disjoint_of_jointly_injective
    (C : Fin 2 → S1 → E2) (hi : Injective (fun x : Fin 2 × S1 => C x.1 x.2)) :
    Disjoint (range (C 0)) (range (C 1)) := by
  apply disjoint_left.mpr
  rintro x ⟨q, hq⟩ ⟨u, hu⟩
  have he : (0 : Fin 2) = 1 :=
    congrArg Prod.fst (@hi (0, q) (1, u) (hq.trans hu.symm))
  exact (by decide : (0 : Fin 2) ≠ 1) he

private theorem ribbon_eq_reversed_arc (t s : Real) (i : Fin 2) :
    negativeLevelRibbon t (WithLp.toLp 2 ![s, (i : Real)]) =
      negativeLevelArc t (Fin.rev i) s := by
  fin_cases i <;> ext j <;> fin_cases j <;>
    norm_num [Fin.rev, negativeLevelRibbon, positiveLevelRibbon, negativeLevelArc,
      positiveLevelArc, saddleCoordinateSwap]

variable {f : S2 → E3} {M : SphereMorseReduction f} {g : S2 → E3}
  {P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g}
  {p : S2} {e : OpenPartialHomeomorph E2 S2}




theorem exists_terminal_protected_negative_circle_anchor
    (d : TerminalSaddleGeometry M P p e)
    (R : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    {a t : Real} (hmargin : 8 * d.r < a) (ht : 0 < t) (htr : t < d.r ^ 2)
    (hlevel : ∀ x ∈ closedSquare a,
      (R x ∈ d.A (inner Real (M.v : E3) (g p) - t) ↔ -(x 0) ^ 2 + (x 1) ^ 2 = -t) ∧
      (R x ∈ d.B (inner Real (M.v : E3) (g p) - t) ↔ -(x 0) ^ 2 + (x 1) ^ 2 = -t))
    (C D : Fin 2 → S1 → E2)
    (hC : ∀ i, _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ (C i))
    (hD : ∀ i, _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ (D i))
    (hCi : Injective (fun x : Fin 2 × S1 => C x.1 x.2))
    (hDi : Injective (fun x : Fin 2 × S1 => D x.1 x.2))
    (hCA : (⋃ i, range (C i)) = d.A (inner Real (M.v : E3) (g p) - t))
    (hDB : (⋃ i, range (D i)) = d.B (inner Real (M.v : E3) (g p) - t))
    (hnest : ∀ i j, i ≠ j → (NestedPair (C i) (C j) ↔ NestedPair (D i) (D j)))
    (hcenter : ∀ i, R (negativeLevelArc t i 0) ∈ range (C i) ∩ range (D i))
    (N : Set E2) (hN : closure N ⊆ R '' openSquare (4 * d.r)) :
    ∃ K : Set E2, IsCompact K ∧ Disjoint K (closure N) ∧
      ∃ Φ : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
        (∀ x, Φ 0 x = x) ∧
        ContDiff Real ∞ (fun z : Real × E2 => Φ z.1 z.2) ∧
        ContDiff Real ∞ (fun z : Real × E2 => (Φ z.1).symm z.2) ∧
        (∀ u x, x ∉ K → Φ u x = x) ∧
        (∀ i, Φ 1 '' range (C i) = range (D i)) ∧
        Φ 1 '' d.A (inner Real (M.v : E3) (g p) - t) =
          d.B (inner Real (M.v : E3) (g p) - t) ∧
        ∃ U : Set E2, IsOpen U ∧ closure N ⊆ U ∧ ∀ u, EqOn (Φ u) id U := by
  have ha : 0 < a := by linarith [d.r_pos]
  have hra : d.r < a := by linarith [d.r_pos]
  have hta : t < a ^ 2 := by nlinarith [d.r_pos]
  have hrad : 6 * d.r ≤ hyperbolaRadius a t := by
    have hsq := hyperbolaRadius_sq hta.le
    have hpos := (hyperbolaRadius_pos hta).le
    have hmarginSq : (8 * d.r) ^ 2 < a ^ 2 := by nlinarith [d.r_pos]
    nlinarith [sq_nonneg d.r]
  have hCdis := pair_disjoint_of_jointly_injective C hCi
  have hDdis := pair_disjoint_of_jointly_injective D hDi
  have hCbranch := negative_morse_branch_mem_circle_of_center_mem C
    (fun i => (hC i).contMDiff.continuous) hCdis _ hCA R ha ht hta
    (fun x hx => (hlevel x hx).1) (fun i => (hcenter i).1)
  have hDbranch := negative_morse_branch_mem_circle_of_center_mem D
    (fun i => (hD i).contMDiff.continuous) hDdis _ hDB R ha ht hta
    (fun x hx => (hlevel x hx).2) (fun i => (hcenter i).2)
  let C' : Fin 2 → S1 → E2 := fun i => C (Fin.rev i)
  let D' : Fin 2 → S1 → E2 := fun i => D (Fin.rev i)
  have hC'dis : Disjoint (range (C' 0)) (range (C' 1)) := hCdis.symm
  have hD'dis : Disjoint (range (D' 0)) (range (D' 1)) := hDdis.symm
  have hn (i j : Fin 2) (hij : i ≠ j) :
      NestedPair (C' i) (C' j) ↔ NestedPair (D' i) (D' j) :=
    hnest (Fin.rev i) (Fin.rev j) (fun he => hij (Fin.rev_injective he))
  have hedge (i : Fin 2) (s : Real) (hs : s ∈ Ioo (-(6 * d.r)) (6 * d.r)) :
      R (negativeLevelRibbon t (WithLp.toLp 2 ![s, (i : Real)])) ∈
        range (C' i) ∩ range (D' i) := by
    rw [ribbon_eq_reversed_arc]
    have hs' : s ∈ Icc (-hyperbolaRadius a t) (hyperbolaRadius a t) :=
      ⟨by linarith [hs.1], by linarith [hs.2]⟩
    exact ⟨hCbranch (Fin.rev i) s hs', hDbranch (Fin.rev i) s hs'⟩
  have hCl (x : E2) (hx : x ∈ openSquare a)
      (hm : R x ∈ range (C' 0) ∪ range (C' 1)) : -(x 0)^2 + (x 1)^2 = -t := by
    apply (hlevel x (openSquare_subset_closedSquare a hx)).1.mp
    apply hCA.subset
    rcases hm with h | h
    · exact mem_iUnion_of_mem 1 h
    · exact mem_iUnion_of_mem 0 h
  have hDl (x : E2) (hx : x ∈ openSquare a)
      (hm : R x ∈ range (D' 0) ∪ range (D' 1)) : -(x 0)^2 + (x 1)^2 = -t := by
    apply (hlevel x (openSquare_subset_closedSquare a hx)).2.mp
    apply hDB.subset
    rcases hm with h | h
    · exact mem_iUnion_of_mem 1 h
    · exact mem_iUnion_of_mem 0 h
  obtain ⟨_, K, hK, hKsq, Φ, h0, hΦ, hΦi, hfix, hmatch, U, hU, hsqU, hUfix⟩ :=
    exists_chart_marked_circle_pair_isotopy_fixing_morse_square R C' D'
      (fun i => hC (Fin.rev i)) (fun i => hD (Fin.rev i)) hC'dis hD'dis hn
      ha ht hta (show 0 < 4 * d.r by linarith [d.r_pos])
      (show 4 * d.r < 5 * d.r by linarith [d.r_pos])
      (show 5 * d.r < 6 * d.r by linarith [d.r_pos]) hrad hedge hCl hDl
  have hNsq : closure N ⊆ R '' closedSquare (4 * d.r) :=
    hN.trans (image_mono (openSquare_subset_closedSquare _))
  have hm (i : Fin 2) : Φ 1 '' range (C i) = range (D i) := by
    have hh := hmatch (Fin.rev i)
    simpa only [C', D', Fin.rev_rev] using hh
  refine ⟨K, hK, hKsq.mono_right hNsq, Φ, h0, hΦ, hΦi, hfix, hm, ?_,
    U, hU, hNsq.trans hsqU, hUfix⟩
  rw [← hCA, ← hDB, image_iUnion]
  exact iUnion_congr hm

end Poincare.Manifold.Schoenflies.PlaneArcs.Terminal

end

end M38Schoenflies
