import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Compression.Complement.TransverseCorners
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Arcs.Mathlib.ShiftedCircleClosedArc











set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "V3" => (Fin 3 → ℝ)



theorem plDomain_relative_preimage_of_eq_off_closed
    {X Y ι : Type*} [TopologicalSpace X] [T2Space X] [TopologicalSpace Y]
    {e : ι → OpenPartialHomeomorph X V3} {R D : Set X}
    (hR : IsCompact R) (q qnew : C(R, Y)) {A : Set Y} (hA : IsClosed A)
    (he : PLDomain e (Subtype.val '' (q ⁻¹' A)))
    (hfront : frontier (Subtype.val '' (q ⁻¹' A)) =
      (Subtype.val '' (q ⁻¹' A) ∩ frontier R) ∪ Subtype.val '' (q ⁻¹' frontier A))
    (hD : IsClosed D) (hDR : D ⊆ interior R)
    (heq : ∀ x : R, (x : X) ∉ D → qnew x = q x)
    (havoid : ∀ x : R, (x : X) ∈ D → qnew x ∉ frontier A) :
    PLDomain e (Subtype.val '' (qnew ⁻¹' A)) ∧
      frontier (Subtype.val '' (qnew ⁻¹' A)) =
        (Subtype.val '' (qnew ⁻¹' A) ∩ frontier R) ∪
          Subtype.val '' (qnew ⁻¹' frontier A) := by
  let N : Set X := Subtype.val '' (q ⁻¹' A)
  let Nnew : Set X := Subtype.val '' (qnew ⁻¹' A)
  let M : Set X := (Nnew ∩ frontier R) ∪ Subtype.val '' (qnew ⁻¹' frontier A)
  have hmark : M ⊆ Dᶜ := by
    rintro x (hx | ⟨y, hy, rfl⟩) hxD
    · exact disjoint_left.mp disjoint_interior_frontier (hDR hxD) hx.2
    · exact havoid y hxD hy
  have hagree : ∀ x ∈ Dᶜ, x ∈ Nnew ↔ x ∈ N := by
    intro x hx
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, by simpa only [mem_preimage, heq y hx] using hy, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, by simpa only [mem_preimage, heq y hx] using hy, rfl⟩
  have hsubset : frontier Nnew ⊆ M := relative_preimage_frontier_subset hR qnew hA
  have hnewfront : frontier Nnew = M := by
    apply Subset.antisymm hsubset
    intro x hx
    have hxD := hmark hx
    apply (mem_frontier_iff_of_open_agreement hD.isOpen_compl hagree hxD).mpr
    rw [hfront]
    rcases hx with hx | ⟨y, hy, rfl⟩
    · exact Or.inl ⟨(hagree x hxD).mp hx.1, hx.2⟩
    · exact Or.inr ⟨y, by simpa only [mem_preimage, heq y hxD] using hy, rfl⟩
  have hclosed : IsClosed Nnew := by
    let : CompactSpace R := isCompact_iff_compactSpace.mp hR
    exact ((hA.preimage qnew.continuous).isCompact.image continuous_subtype_val).isClosed
  refine ⟨⟨he.cover, he.compatible, hclosed, ?_⟩, hnewfront⟩
  intro x hx
  exact halfspace_of_open_agreement he hD.isOpen_compl hagree (hmark (hsubset hx)) hx

local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "R" => latticeHandleDomain (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "p" => (4 * (128 : ℝ))
local notation "C" => AddCircle p

private instance : Fact (0 < p) := ⟨by norm_num⟩



theorem plDomain_sourceSlab_of_supported_phase_avoidance
    {ι : Type*} {e : ι → OpenPartialHomeomorph X V3}
    (phi psi : C(H, H)) {c a b : ℝ} (ha : c < a) (hab : a ≤ b) (hb : b < c + p)
    (he : PLDomain e (sourceSlab phi a b))
    (hfront : frontier (sourceSlab phi a b) = (sourceSlab phi a b ∩ frontier R) ∪
      (sourceSurface phi (a : C) ∪ sourceSurface phi (b : C)))
    {D : Set X} (hD : IsClosed D) (hDR : D ⊆ interior R)
    (hfixed : ∀ x : H,
      ((latticeHandleDomainEquiv (Fin 1) (Fin 2) L).symm x : X) ∉ D → psi x = phi x)
    (havoid : ∀ x : R, (x : X) ∈ D →
      sourcePhase psi (latticeHandleDomainEquiv (Fin 1) (Fin 2) L x) ≠ (a : C) ∧
      sourcePhase psi (latticeHandleDomainEquiv (Fin 1) (Fin 2) L x) ≠ (b : C)) :
    PLDomain e (sourceSlab psi a b) ∧
      frontier (sourceSlab psi a b) = (sourceSlab psi a b ∩ frontier R) ∪
        (sourceSurface psi (a : C) ∪ sourceSurface psi (b : C)) := by
  let : T2Space ((Fin 2 → ℝ) ⧸ (L).toAddSubgroup) :=
    (hamiltonLowerLatticePiEquiv (Fin 2)).isEmbedding.t2Space
  let q (f : C(H, H)) : C(R, C) := (sourcePhase f).comp
    ⟨latticeHandleDomainEquiv (Fin 1) (Fin 2) L,
      (latticeHandleDomainEquiv (Fin 1) (Fin 2) L).continuous⟩
  have hphases (f : C(H, H)) :
      Subtype.val '' ((q f) ⁻¹' frontier (AddCircle.closedIntervalArc p a b)) =
        sourceSurface f (a : C) ∪ sourceSurface f (b : C) := by
    rw [AddCircle.frontier_closedIntervalArc_shifted p ha hab hb]
    rw [show ({(a : C), (b : C)} : Set C) = {(a : C)} ∪ {(b : C)} by
      ext; simp [or_comm], preimage_union, image_union]
    rfl
  have hfront' : frontier (Subtype.val '' ((q phi) ⁻¹' AddCircle.closedIntervalArc p a b)) =
      (Subtype.val '' ((q phi) ⁻¹' AddCircle.closedIntervalArc p a b) ∩ frontier R) ∪
        Subtype.val '' ((q phi) ⁻¹' frontier (AddCircle.closedIntervalArc p a b)) := by
    rw [hphases]
    exact hfront
  obtain ⟨hPL, hf⟩ := plDomain_relative_preimage_of_eq_off_closed
    (isCompact_latticeHandleDomain (Fin 1) (Fin 2) L) (q phi) (q psi)
    (AddCircle.isCompact_closedIntervalArc p a b).isClosed he hfront' hD hDR
    (by
      intro x hx
      have h := hfixed (latticeHandleDomainEquiv (Fin 1) (Fin 2) L x)
        (by simpa only [Homeomorph.symm_apply_apply] using hx)
      exact congrArg (fun y : H => (hamiltonOneHierarchyCoordinates y).2) h)
    (by
      intro x hx
      rw [AddCircle.frontier_closedIntervalArc_shifted p ha hab hb]
      exact fun h => h.elim (havoid x hx).1 (havoid x hx).2)
  rw [hphases] at hf
  exact ⟨hPL, hf⟩



theorem plDomains_complementary_sourceSlabs_of_supported_phase_avoidance
    {ι : Type*} {e : ι → OpenPartialHomeomorph X V3}
    (phi psi : C(H, H)) {c a b : ℝ} (ha : c < a) (hab : a < b) (hb : b < c + p)
    (he : PLDomain e (sourceSlab phi a b))
    (he' : PLDomain e (sourceSlab phi b (a + p)))
    (hfront : frontier (sourceSlab phi a b) = (sourceSlab phi a b ∩ frontier R) ∪
      (sourceSurface phi (a : C) ∪ sourceSurface phi (b : C)))
    (hfront' : frontier (sourceSlab phi b (a + p)) =
      (sourceSlab phi b (a + p) ∩ frontier R) ∪
        (sourceSurface phi (a : C) ∪ sourceSurface phi (b : C)))
    {D : Set X} (hD : IsClosed D) (hDR : D ⊆ interior R)
    (hfixed : ∀ x : H,
      ((latticeHandleDomainEquiv (Fin 1) (Fin 2) L).symm x : X) ∉ D → psi x = phi x)
    (havoid : ∀ x : R, (x : X) ∈ D →
      sourcePhase psi (latticeHandleDomainEquiv (Fin 1) (Fin 2) L x) ≠ (a : C) ∧
      sourcePhase psi (latticeHandleDomainEquiv (Fin 1) (Fin 2) L x) ≠ (b : C)) :
    PLDomain e (sourceSlab psi a b) ∧
      frontier (sourceSlab psi a b) = (sourceSlab psi a b ∩ frontier R) ∪
        (sourceSurface psi (a : C) ∪ sourceSurface psi (b : C)) ∧
    PLDomain e (sourceSlab psi b (a + p)) ∧
      frontier (sourceSlab psi b (a + p)) =
        (sourceSlab psi b (a + p) ∩ frontier R) ∪
          (sourceSurface psi (a : C) ∪ sourceSurface psi (b : C)) := by
  obtain ⟨hPL, hf⟩ := plDomain_sourceSlab_of_supported_phase_avoidance
    phi psi ha hab.le hb he hfront hD hDR hfixed havoid
  have hf' : frontier (sourceSlab phi b (a + p)) =
      (sourceSlab phi b (a + p) ∩ frontier R) ∪
        (sourceSurface phi (b : C) ∪ sourceSurface phi ((a + p : ℝ) : C)) := by
    rw [AddCircle.coe_add_period, union_comm (sourceSurface phi (b : C))]
    exact hfront'
  obtain ⟨hPL', hnewfront'⟩ := plDomain_sourceSlab_of_supported_phase_avoidance
    phi psi (c := (a + b) / 2) (by linarith : (a + b) / 2 < b)
    (by linarith : b ≤ a + p) (by linarith : a + p < (a + b) / 2 + p)
    he' hf' hD hDR hfixed (by
      intro x hx
      rw [AddCircle.coe_add_period]
      exact ⟨(havoid x hx).2, (havoid x hx).1⟩)
  rw [AddCircle.coe_add_period, union_comm (sourceSurface psi (b : C))] at hnewfront'
  exact ⟨hPL, hf, hPL', hnewfront'⟩



theorem sourceSurface_eq_sdiff_of_supported_avoidance
    (phi psi : C(H, H)) {D : Set X} (theta : C)
    (hfixed : ∀ x : H,
      ((latticeHandleDomainEquiv (Fin 1) (Fin 2) L).symm x : X) ∉ interior D → psi x = phi x)
    (havoid : ∀ x : R, (x : X) ∈ D →
      sourcePhase psi (latticeHandleDomainEquiv (Fin 1) (Fin 2) L x) ≠ theta) :
    sourceSurface psi theta = sourceSurface phi theta \ interior D := by
  have hnot (x : X) (hx : x ∈ sourceSurface psi theta) : x ∉ D := by
    let xR : R := ⟨x, sourceSurface_subset psi theta hx⟩
    exact fun hxD => havoid xR hxD ((mem_sourceSurface_iff psi theta xR).mp hx)
  ext x
  constructor
  · intro hx
    have hxI : x ∉ interior D := fun h => hnot x hx (interior_subset h)
    exact ⟨(sourceSurface_agrees_off_support phi psi hfixed theta x hxI).mp hx, hxI⟩
  · rintro ⟨hx, hxI⟩
    exact (sourceSurface_agrees_off_support phi psi hfixed theta x hxI).mpr hx



theorem sourceSlab_eq_sdiff_of_supported_avoidance
    (phi psi : C(H, H)) {D : Set X} (a b : ℝ)
    (hfixed : ∀ x : H,
      ((latticeHandleDomainEquiv (Fin 1) (Fin 2) L).symm x : X) ∉ interior D → psi x = phi x)
    (havoid : Disjoint (sourceSlab psi a b) D) :
    sourceSlab psi a b = sourceSlab phi a b \ interior D := by
  ext x
  constructor
  · intro hx
    have hxI : x ∉ interior D := fun h => disjoint_left.mp havoid hx (interior_subset h)
    exact ⟨(sourceSlab_agrees_off_support phi psi hfixed a b x hxI).mp hx, hxI⟩
  · rintro ⟨hx, hxI⟩
    exact (sourceSlab_agrees_off_support phi psi hfixed a b x hxI).mpr hx



theorem sourceSlab_eq_union_of_supported_containment
    (phi psi : C(H, H)) {D : Set X} (a b : ℝ)
    (hfixed : ∀ x : H,
      ((latticeHandleDomainEquiv (Fin 1) (Fin 2) L).symm x : X) ∉ interior D → psi x = phi x)
    (hcontains : D ⊆ sourceSlab psi a b) :
    sourceSlab psi a b = sourceSlab phi a b ∪ D := by
  ext x
  by_cases hxD : x ∈ D
  · exact iff_of_true (hcontains hxD) (Or.inr hxD)
  · have hxI : x ∉ interior D := fun h => hxD (interior_subset h)
    simpa only [mem_union, hxD, or_false] using
      sourceSlab_agrees_off_support phi psi hfixed a b x hxI



theorem frontier_sourceSlab_eq_sdiff_of_supported_avoidance
    (phi psi : C(H, H)) {D : Set X} (a b : ℝ) (hDR : D ⊆ interior R)
    (hfront : frontier (sourceSlab phi a b) = (sourceSlab phi a b ∩ frontier R) ∪
      (sourceSurface phi (a : C) ∪ sourceSurface phi (b : C)))
    (hfrontNew : frontier (sourceSlab psi a b) = (sourceSlab psi a b ∩ frontier R) ∪
      (sourceSurface psi (a : C) ∪ sourceSurface psi (b : C)))
    (hfixed : ∀ x : H,
      ((latticeHandleDomainEquiv (Fin 1) (Fin 2) L).symm x : X) ∉ interior D → psi x = phi x)
    (havoid : ∀ x : R, (x : X) ∈ D →
      sourcePhase psi (latticeHandleDomainEquiv (Fin 1) (Fin 2) L x) ≠ (a : C) ∧
      sourcePhase psi (latticeHandleDomainEquiv (Fin 1) (Fin 2) L x) ≠ (b : C)) :
    frontier (sourceSlab psi a b) = frontier (sourceSlab phi a b) \ interior D := by
  have hold : sourceSlab psi a b ∩ frontier R =
      (sourceSlab phi a b ∩ frontier R) \ interior D := by
    ext x
    constructor
    · rintro ⟨hx, hxR⟩
      have hxI : x ∉ interior D := fun h =>
        disjoint_left.mp disjoint_interior_frontier (hDR (interior_subset h)) hxR
      exact ⟨⟨(sourceSlab_agrees_off_support phi psi hfixed a b x hxI).mp hx, hxR⟩, hxI⟩
    · rintro ⟨⟨hx, hxR⟩, hxI⟩
      exact ⟨(sourceSlab_agrees_off_support phi psi hfixed a b x hxI).mpr hx, hxR⟩
  rw [hfrontNew, hfront, hold,
    sourceSurface_eq_sdiff_of_supported_avoidance phi psi (a : C) hfixed
      (fun x hx => (havoid x hx).1),
    sourceSurface_eq_sdiff_of_supported_avoidance phi psi (b : C) hfixed
      (fun x hx => (havoid x hx).2), union_sdiff_distrib, union_sdiff_distrib]



theorem frontier_sourceSlab_disjoint_frontier_support
    (phi psi : C(H, H)) {D : Set X} (a b : ℝ)
    (hD : IsClosed D) (hDR : D ⊆ interior R)
    (hfront : frontier (sourceSlab phi a b) = (sourceSlab phi a b ∩ frontier R) ∪
      (sourceSurface phi (a : C) ∪ sourceSurface phi (b : C)))
    (hfixed : ∀ x : H,
      ((latticeHandleDomainEquiv (Fin 1) (Fin 2) L).symm x : X) ∉ interior D → psi x = phi x)
    (havoid : ∀ x : R, (x : X) ∈ D →
      sourcePhase psi (latticeHandleDomainEquiv (Fin 1) (Fin 2) L x) ≠ (a : C) ∧
      sourcePhase psi (latticeHandleDomainEquiv (Fin 1) (Fin 2) L x) ≠ (b : C)) :
    Disjoint (frontier (sourceSlab phi a b)) (frontier D) := by
  apply disjoint_left.mpr
  intro x hx hxD
  have hxDin : x ∈ D := hD.frontier_subset hxD
  have hxI : x ∉ interior D := hxD.2
  have hphase (theta : C) (hxS : x ∈ sourceSurface phi theta)
      (hneq : ∀ y : R, (y : X) ∈ D →
        sourcePhase psi (latticeHandleDomainEquiv (Fin 1) (Fin 2) L y) ≠ theta) : False := by
    have hxNew := (sourceSurface_agrees_off_support phi psi hfixed theta x hxI).mpr hxS
    let xR : R := ⟨x, sourceSurface_subset psi theta hxNew⟩
    exact hneq xR hxDin ((mem_sourceSurface_iff psi theta xR).mp hxNew)
  rw [hfront] at hx
  rcases hx with hx | hx | hx
  · exact disjoint_left.mp disjoint_interior_frontier (hDR hxDin) hx.2
  · exact hphase (a : C) hx (fun y hy => (havoid y hy).1)
  · exact hphase (b : C) hx (fun y hy => (havoid y hy).2)

end PoincareConjecture.M76.HamiltonIntervalTorus
