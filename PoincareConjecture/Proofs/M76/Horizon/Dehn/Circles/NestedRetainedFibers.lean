import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.NestedResolvedAnnulus
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.Components.RetainedModels

set_option autoImplicit false

open Set Metric Geometry PLAnnularStrip
open PoincareConjecture.M76.Dehn PoincareConjecture.M76.Dehn.PolygonalCrossingResolution

namespace Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "R" => sphere (0 : V2) 1

theorem exists_nested_retained_fibers
    {X : Type*} {m n k : ℕ}
    (P : Polygon V2 (m + 3)) (I : Polygon V2 (n + 3)) (Q : Polygon V2 (k + 3))
    (hP : P.HasSimplicialEdges) (hinjP : Function.Injective P)
    (hI : I.HasSimplicialEdges) (hinjI : Function.Injective I)
    (hQ : Q.HasSimplicialEdges) (hinjQ : Function.Injective Q)
    (hPsq : P.boundary ℝ ⊆ ball 0 1) (hQsq : Q.boundary ℝ ⊆ ball 0 1)
    (hIP : closure I.inside ⊆ P.inside) (hQI : closure Q.inside ⊆ I.inside)
    (H : closure Q.inside ≃ₜ closure I.inside) (hH : H.IsFinitePL)
    {L d : ℝ} (c : squareAnnulus L d ≃ₜ ↥(closure P.inside \ I.inside))
    (f g : V2 → X) (a : P2 → X)
    (ha : Function.Injective (fun p : squareAnnulus L d => a p))
    (hkeep : ∀ x : closure Q.inside, g (H x) = f x)
    (hout : EqOn g f (D \ P.inside))
    (hcollar : ∀ p : squareAnnulus L d, g (c p) = a p)
    (hcross : ∀ x ∈ closure P.inside \ I.inside,
      ∀ y ∈ closure I.inside ∪ (D \ P.inside), g x = g y ↔ x = y) :
    ∃ j : (closure Q.inside ∪ (D \ P.inside) : Set V2) → V2,
      RetainedSquareMapFacts f g _ j ∧
      (∀ x : closure Q.inside, j ⟨x, Or.inl x.property⟩ = (H x : V2)) ∧
      (∀ x : ↥(D \ P.inside), j ⟨x, Or.inr x.property⟩ = x) ∧
      (∃ J : V2 → V2, FinitePiecewiseAffineOn J (closure Q.inside ∪ (D \ P.inside)) ∧
        ∀ x : (closure Q.inside ∪ (D \ P.inside) : Set V2), J x = j x) := by
  classical
  obtain ⟨hcover, _, _, hIO, _, hclosedO, _⟩ :=
    nested_annulus_source_partition P I hP hinjP hI hinjI hPsq hIP
  obtain ⟨_, _, _, hQball⟩ := polygon_source_region Q
    (ContinuousLinearEquiv.finTwoArrow ℝ ℝ) hQ hinjQ (convex_ball _ _) hQsq
  obtain ⟨_, _, _, hPball⟩ := polygon_source_region P
    (ContinuousLinearEquiv.finTwoArrow ℝ ℝ) hP hinjP (convex_ball _ _) hPsq
  have hQO : Disjoint (closure Q.inside) (D \ P.inside) :=
    hIO.mono_left (hQI.trans subset_closure)
  let jA : closure Q.inside → V2 := fun x => H x
  let jB : ↥(D \ P.inside) → V2 := Subtype.val
  let j := joinSourceCopies hQO jA jB
  have hrA : range jA = closure I.inside := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact (H y).property
    · intro hx
      exact ⟨H.symm ⟨x, hx⟩, congrArg Subtype.val (H.apply_symm_apply _)⟩
  have hrB : range jB = D \ P.inside := Subtype.range_val
  have hr : range j = closure I.inside ∪ (D \ P.inside) := by
    rw [joinSourceCopies_range, hrA, hrB]
  have hji : Function.Injective j := joinSourceCopies_injective hQO
    (Subtype.val_injective.comp H.injective) Subtype.val_injective
    (by rwa [hrA, hrB])
  have hjc : Continuous j := joinSourceCopies_continuous hQO isClosed_closure hclosedO
    (continuous_subtype_val.comp H.continuous) continuous_subtype_val
  have hcov : range j ∪ (closure P.inside \ I.inside) = D := by
    rw [hr]
    simpa only [union_assoc, union_left_comm, union_comm] using hcover
  have hkeep' (x : (closure Q.inside ∪ (D \ P.inside) : Set V2)) : g (j x) = f x :=
    joinSourceCopies_target hQO hkeep (fun y => hout y.property) x
  have hsingle : ∀ z ∈ closure P.inside \ I.inside, ∀ w ∈ D,
      g w = g z → w = z := by
    intro z hz w hw heq
    rcases hcov.symm.subset hw with hwj | hwc
    · exact ((hcross z hz w (hr.subset hwj)).mp heq.symm).symm
    · let p := c.symm ⟨z, hz⟩
      let q := c.symm ⟨w, hwc⟩
      have hp : (c p : V2) = z := congrArg Subtype.val (c.apply_symm_apply _)
      have hq : (c q : V2) = w := congrArg Subtype.val (c.apply_symm_apply _)
      have he : a q = a p := by rw [← hcollar, ← hcollar, hp, hq]; exact heq
      exact hq.symm.trans ((congrArg (fun v => (c v : V2)) (ha he)).trans hp)
  have hmap (x : (closure Q.inside ∪ (D \ P.inside) : Set V2)) : j x ∈ D :=
    hcov.subset (Or.inl (mem_range_self x))
  have hbd (x : (closure Q.inside ∪ (D \ P.inside) : Set V2)) :
      j x ∈ R ↔ (x : V2) ∈ R := by
    rcases x.property with hx | hx
    · rw [show j x = jA ⟨x, hx⟩ from joinSourceCopies_left hQO jA jB x hx]
      have hleft : jA ⟨x, hx⟩ ∈ ball 0 1 :=
        hPball (subset_closure (hIP (H ⟨x, hx⟩).property))
      have hright : (x : V2) ∈ ball 0 1 := hQball hx
      exact iff_of_false (fun h => (ne_of_lt hleft) h) (fun h => (ne_of_lt hright) h)
    · rw [show j x = jB ⟨x, hx⟩ from joinSourceCopies_right hQO jA jB x hx]
  refine ⟨j, ⟨union_subset (hQball.trans ball_subset_closedBall) sdiff_subset,
    hji, hjc, hmap, hkeep', hbd,
    retained_double_relation_eq j hji hcov hkeep' hsingle,
    retained_double_locus_eq j hji hcov hkeep' hsingle⟩,
    (fun x => joinSourceCopies_left hQO jA jB _ x.property),
    (fun x => joinSourceCopies_right hQO jA jB _ x.property), ?_⟩
  obtain ⟨J, hJ, hJval⟩ := hH
  obtain ⟨_, K, hK, hKs⟩ := exists_polygon_source_complement P hP hinjP hPsq
  have hid : FinitePiecewiseAffineOn (id : V2 → V2) (D \ P.inside) :=
    ⟨K, hK, hKs, fun _ _ => ⟨ContinuousAffineMap.id ℝ V2, fun _ _ => rfl⟩⟩
  exact joinSourceCopies_exists_finitePL_extension hQO jA jB
    ⟨J, hJ, fun x => (hJval x).symm⟩ ⟨id, hid, fun _ => rfl⟩

end Dehn
