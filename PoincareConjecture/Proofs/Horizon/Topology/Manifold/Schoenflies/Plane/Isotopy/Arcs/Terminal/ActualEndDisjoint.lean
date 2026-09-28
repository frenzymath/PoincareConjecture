import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.TerminalData

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.PlaneArcs.Terminal
open SaddleLevel SphereSurgeryCoreCap
private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

theorem terminalEndCap_pairwise_disjoint
    {v : E3} {g : S2 → E3} {B : Set Real} {C : Set S2}
    (A : AnnularEndFamily v g B C) :
    Pairwise (fun i j : A.EndIndex => Disjoint (terminalEndCap A i) (terminalEndCap A j)) := by
  let cap : A.EndIndex → SphereSurgeryCoreCap v g B := fun i =>
    match i with
    | .inl j => j.1.1
    | .inr j => j.1.1
  have hcapmem (i : A.EndIndex) : cap i ∈ A.caps := by
    rcases i with i | i <;> exact i.1.2
  have hcapinj : Injective cap := by
    rintro (i | i) (j | j) hij
    · congr 1
      exact Subtype.ext (Subtype.ext hij)
    · have heq : i.1.1.center = j.1.1.center := congrArg SphereSurgeryCoreCap.center hij
      exact False.elim (by linarith [i.2, j.2, A.cuts_lt])
    · have heq : i.1.1.center = j.1.1.center := congrArg SphereSurgeryCoreCap.center hij
      exact False.elim (by linarith [i.2, j.2, A.cuts_lt])
    · congr 1
      exact Subtype.ext (Subtype.ext hij)
  have hcapEnd (i : A.EndIndex) : C ∩ ((cap i).chart '' closedBall (0 : E2) 1) ⊆
      A.endRegion i := by
    intro q hq
    have hb := (core_inter_closed_disk A.caps A.caps_disjoint A.core_complement
      (cap i) (hcapmem i)).subset hq
    rcases i with i | i
    · change q ∈ i.1.1.chart '' sphere (0 : E2) 1 at hb
      rw [← (A.lower i.1.1 i.1.2 i.2).boundary] at hb
      obtain ⟨u, rfl⟩ := hb
      exact mem_image_of_mem _ ⟨mem_univ _, le_rfl, i.2.le⟩
    · change q ∈ i.1.1.chart '' sphere (0 : E2) 1 at hb
      rw [← (A.upper i.1.1 i.1.2 i.2).boundary] at hb
      obtain ⟨u, rfl⟩ := hb
      change (A.upper i.1.1 i.1.2 i.2).chart (u, i.1.1.center) ∈
        (A.upper i.1.1 i.1.2 i.2).region
      rw [(A.upper i.1.1 i.1.2 i.2).region_eq_image]
      exact mem_image_of_mem _ ⟨mem_univ _, i.2.le, le_rfl⟩
  have hcapEq (i : A.EndIndex) : terminalEndCap A i =
      A.endRegion i ∪ (cap i).chart '' closedBall (0 : E2) 1 := by
    rcases i with i | i <;> rfl
  let : Std.Symm (fun D E : SphereSurgeryCoreCap v g B =>
      Disjoint (D.chart '' closedBall 0 1) (E.chart '' closedBall 0 1)) :=
    ⟨fun _ _ h => h.symm⟩
  intro i j hij
  have hends := A.pairwise_disjoint hij
  have hcaps := A.caps_disjoint.forall (hcapmem i) (hcapmem j)
    (fun hh => hij (hcapinj hh))
  rw [hcapEq i, hcapEq j]
  apply disjoint_left.mpr
  intro q hq hq'
  rcases hq with hq | hq <;> rcases hq' with hq' | hq'
  · exact disjoint_left.mp hends hq hq'
  · exact disjoint_left.mp hends hq
      (hcapEnd j ⟨A.endRegion_subset_core i hq, hq'⟩)
  · exact disjoint_left.mp hends
      (hcapEnd i ⟨A.endRegion_subset_core j hq', hq⟩) hq'
  · exact disjoint_left.mp hcaps hq hq'

private theorem path_target_injective {v : E3} {f g : S2 → E3}
    (P : SphereSurgeryPath v f g) : Injective f → Injective g := by
  induction P with
  | refl => exact id
  | minus S next ih => exact fun _ => ih S.fMinus_embedding.isEmbedding.injective
  | plus S next ih => exact fun _ => ih S.fPlus_embedding.isEmbedding.injective

theorem terminal_actual_caps_pairwise_disjoint
    {f : S2 → E3} {M : SphereMorseReduction f} {g : S2 → E3}
    {P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g}
    {p : S2} {e : OpenPartialHomeomorph E2 S2}
    (d : TerminalSaddleGeometry M P p e) :
    Pairwise (fun i j : Fin 3 => Disjoint (d.C i) (d.C j)) := by
  have hg : Injective g := path_target_injective P M.embedding.isEmbedding.injective
  intro i j hij
  have hsource := terminalEndCap_pairwise_disjoint d.ends
    (show d.labels i ≠ d.labels j from fun hh => hij (d.labels.injective hh))
  apply disjoint_left.mpr
  rintro _ ⟨q, hq, rfl⟩ ⟨q', hq', heq⟩
  have hqq : q' = q := hg (d.flatten.injective heq)
  subst q'
  exact disjoint_left.mp hsource hq hq'

end Poincare.Manifold.Schoenflies.PlaneArcs.Terminal
