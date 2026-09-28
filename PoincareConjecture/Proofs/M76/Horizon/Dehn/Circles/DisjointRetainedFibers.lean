import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.DisjointResolvedAnnuli
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.Components.RetainedModels

set_option autoImplicit false

open Set Metric Geometry PLAnnularStrip
open PoincareConjecture.M76.Dehn PoincareConjecture.M76.Dehn.PolygonalCrossingResolution

namespace Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "R" => sphere (0 : V2) 1

theorem exists_disjoint_retained_fibers
    {X : Type*} {m n : Bool → ℕ}
    (P : (i : Bool) → Polygon V2 (m i + 3)) (I : (i : Bool) → Polygon V2 (n i + 3))
    (hP : ∀ i, (P i).HasSimplicialEdges) (hinjP : ∀ i, Function.Injective (P i))
    (hI : ∀ i, (I i).HasSimplicialEdges) (hinjI : ∀ i, Function.Injective (I i))
    (hPsq : ∀ i, (P i).boundary ℝ ⊆ ball 0 1)
    (hIP : ∀ i, closure (I i).inside ⊆ (P i).inside)
    (hdisP : Disjoint (closure (P false).inside) (closure (P true).inside))
    (H : closure (I false).inside ≃ₜ closure (I true).inside) (hH : H.IsFinitePL)
    {L d : ℝ}
    (c : (i : Bool) → squareAnnulus L d ≃ₜ ↥(closure (P i).inside \ (I i).inside))
    (f g : V2 → X) (a : Bool → P2 → X)
    (ha : ∀ i, Function.Injective (fun p : squareAnnulus L d => a i p))
    (hadis : Disjoint (a false '' squareAnnulus L d) (a true '' squareAnnulus L d))
    (hkeep0 : ∀ x : closure (I false).inside, g (H x) = f x)
    (hkeep1 : ∀ x : closure (I true).inside, g (H.symm x) = f x)
    (hout : EqOn g f (D \ ((P false).inside ∪ (P true).inside)))
    (hcollar : ∀ i (p : squareAnnulus L d), g (c i p) = a i p)
    (hcross : ∀ x ∈ (closure (P false).inside \ (I false).inside) ∪
        (closure (P true).inside \ (I true).inside),
      ∀ y ∈ (closure (I false).inside ∪ closure (I true).inside) ∪
        (D \ ((P false).inside ∪ (P true).inside)), g x = g y ↔ x = y) :
    let K := (closure (I false).inside ∪ closure (I true).inside) ∪
      (D \ ((P false).inside ∪ (P true).inside))
    ∃ j : K → V2, RetainedSquareMapFacts f g K j ∧ range j = K ∧
      (∀ x : closure (I false).inside, j ⟨x, Or.inl (Or.inl x.property)⟩ = (H x : V2)) ∧
      (∀ x : closure (I true).inside, j ⟨x, Or.inl (Or.inr x.property)⟩ = (H.symm x : V2)) ∧
      (∀ x : ↥(D \ ((P false).inside ∪ (P true).inside)),
        j ⟨x, Or.inr x.property⟩ = x) ∧
      (∃ J : V2 → V2, FinitePiecewiseAffineOn J K ∧ ∀ x : K, J x = j x) := by
  classical
  dsimp only
  let S := fun i => closure (I i).inside
  let C := fun i => closure (P i).inside \ (I i).inside
  let O := D \ ((P false).inside ∪ (P true).inside)
  let K := (S false ∪ S true) ∪ O
  obtain ⟨hcover, _, _, hdisI, hdisIO, _, _, _, hclosedO, hSball, _, _⟩ :=
    disjoint_annulus_source_partition P I hP hinjP hI hinjI hPsq hIP hdisP
  let j0 : S false → V2 := fun x => H x
  let j1 : S true → V2 := fun x => H.symm x
  let jA := joinSourceCopies hdisI j0 j1
  let jB : O → V2 := Subtype.val
  let j := joinSourceCopies hdisIO jA jB
  have hr0 : range j0 = S true := by
    ext x
    exact ⟨fun ⟨y, hy⟩ => hy ▸ (H y).property,
      fun hx => ⟨H.symm ⟨x, hx⟩, congrArg Subtype.val (H.apply_symm_apply _)⟩⟩
  have hr1 : range j1 = S false := by
    ext x
    exact ⟨fun ⟨y, hy⟩ => hy ▸ (H.symm y).property,
      fun hx => ⟨H ⟨x, hx⟩, congrArg Subtype.val (H.symm_apply_apply _)⟩⟩
  have hrA : range jA = S false ∪ S true := by
    rw [joinSourceCopies_range, hr0, hr1, union_comm]
  have hrB : range jB = O := Subtype.range_val
  have hr : range j = K := by rw [joinSourceCopies_range, hrA, hrB]
  have hAi : Function.Injective jA := joinSourceCopies_injective hdisI
    (Subtype.val_injective.comp H.injective) (Subtype.val_injective.comp H.symm.injective)
    (by rw [hr0, hr1]; exact hdisI.symm)
  have hji : Function.Injective j := joinSourceCopies_injective hdisIO hAi
    Subtype.val_injective (by rwa [hrA, hrB])
  have hAc : Continuous jA := joinSourceCopies_continuous hdisI isClosed_closure
    isClosed_closure (continuous_subtype_val.comp H.continuous)
    (continuous_subtype_val.comp H.symm.continuous)
  have hjc : Continuous j := joinSourceCopies_continuous hdisIO
    (isClosed_closure.union isClosed_closure) hclosedO hAc continuous_subtype_val
  have hkeepA (x : (S false ∪ S true : Set V2)) : g (jA x) = f x :=
    joinSourceCopies_target hdisI hkeep0 hkeep1 x
  have hkeep (x : K) : g (j x) = f x :=
    joinSourceCopies_target hdisIO hkeepA (fun y => hout y.property) x
  have hcov : range j ∪ (C false ∪ C true) = D := by rw [hr]; exact hcover
  have hcval (i : Bool) (x : C i) : (c i ((c i).symm x) : V2) = x :=
    congrArg Subtype.val ((c i).apply_symm_apply x)
  have hsingle : ∀ z ∈ C false ∪ C true, ∀ w ∈ D, g w = g z → w = z := by
    intro z hz w hw heq
    rcases hcov.symm.subset hw with hwj | hwc
    · exact ((hcross z hz w (hr.subset hwj)).mp heq.symm).symm
    · obtain ⟨i, hi⟩ : ∃ i : Bool, z ∈ C i := hz.elim
        (fun h => ⟨false, h⟩) (fun h => ⟨true, h⟩)
      obtain ⟨l, hl⟩ : ∃ l : Bool, w ∈ C l := hwc.elim
        (fun h => ⟨false, h⟩) (fun h => ⟨true, h⟩)
      let p := (c i).symm ⟨z, hi⟩
      let q := (c l).symm ⟨w, hl⟩
      have hp : (c i p : V2) = z := hcval i _
      have hq : (c l q : V2) = w := hcval l _
      have he : a l q = a i p := by rw [← hcollar, ← hcollar, hp, hq]; exact heq
      by_cases hli : l = i
      · subst l
        exact hq.symm.trans ((congrArg (fun v => (c i v : V2)) (ha i he)).trans hp)
      · have hnot : Disjoint (a l '' squareAnnulus L d) (a i '' squareAnnulus L d) := by
          cases l <;> cases i
          · exact False.elim (hli rfl)
          · exact hadis
          · exact hadis.symm
          · exact False.elim (hli rfl)
        exact False.elim (disjoint_left.mp hnot ⟨q, q.property, rfl⟩ ⟨p, p.property, he.symm⟩)
  have hKsub : K ⊆ D := union_subset
    (union_subset ((hSball false).trans ball_subset_closedBall)
      ((hSball true).trans ball_subset_closedBall)) sdiff_subset
  have hbdA (x : (S false ∪ S true : Set V2)) : jA x ∈ R ↔ (x : V2) ∈ R := by
    have hleft : jA x ∈ ball 0 1 := union_subset (hSball false) (hSball true)
      (hrA.subset (mem_range_self x))
    have hright : (x : V2) ∈ ball 0 1 := union_subset (hSball false) (hSball true) x.property
    exact iff_of_false (fun h => (ne_of_lt hleft) h) (fun h => (ne_of_lt hright) h)
  have hbd (x : K) : j x ∈ R ↔ (x : V2) ∈ R := by
    rcases x.property with hx | hx
    · rw [show j x = jA ⟨x, hx⟩ from joinSourceCopies_left hdisIO jA jB x hx]
      exact hbdA ⟨x, hx⟩
    · rw [show j x = jB ⟨x, hx⟩ from joinSourceCopies_right hdisIO jA jB x hx]
  refine ⟨j, ⟨hKsub, hji, hjc, fun x => hKsub (hr.subset (mem_range_self x)),
    hkeep, hbd, retained_double_relation_eq j hji hcov hkeep hsingle,
    retained_double_locus_eq j hji hcov hkeep hsingle⟩, hr, ?_, ?_, ?_, ?_⟩
  · intro x
    exact (joinSourceCopies_left hdisIO jA jB _ (Or.inl x.property)).trans
      (joinSourceCopies_left hdisI j0 j1 _ x.property)
  · intro x
    exact (joinSourceCopies_left hdisIO jA jB _ (Or.inr x.property)).trans
      (joinSourceCopies_right hdisI j0 j1 _ x.property)
  · intro x
    exact joinSourceCopies_right hdisIO jA jB _ x.property
  · have hHsymm := hH.symm
    obtain ⟨J0, hJ0, hJ0val⟩ := hH
    obtain ⟨J1, hJ1, hJ1val⟩ := hHsymm
    obtain ⟨_, K0, hK0, hK0s⟩ := exists_polygon_source_complement (P false)
      (hP false) (hinjP false) (hPsq false)
    obtain ⟨_, K1, hK1, hK1s⟩ := exists_polygon_source_complement (P true)
      (hP true) (hinjP true) (hPsq true)
    obtain ⟨KO, hKO, hKOs⟩ := K0.exists_finite_triangulation_inter K1 hK0 hK1
    have hKOspace : KO.space = O := by
      rw [hKOs, hK0s, hK1s]
      ext x
      simp only [O, mem_inter_iff, mem_sdiff, mem_union, not_or]
      tauto
    have hid : FinitePiecewiseAffineOn (id : V2 → V2) O :=
      ⟨KO, hKO, hKOspace, fun _ _ => ⟨ContinuousAffineMap.id ℝ V2, fun _ _ => rfl⟩⟩
    exact joinSourceCopies_exists_finitePL_extension hdisIO jA jB
      (joinSourceCopies_exists_finitePL_extension hdisI j0 j1
        ⟨J0, hJ0, fun x => (hJ0val x).symm⟩ ⟨J1, hJ1, fun x => (hJ1val x).symm⟩)
      ⟨id, hid, fun _ => rfl⟩

end Dehn
