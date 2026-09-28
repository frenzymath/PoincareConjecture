import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Disks.Maps.SourceBoundaryAlternative

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

theorem exists_product_end_homotopyRel
    {X E : Type*} [TopologicalSpace X] [TopologicalSpace E]
    (H : X ≃ₜ E × unitInterval) (k : C(unitInterval, X)) (d : unitInterval)
    (hzero : (H (k 0)).2 = d) (hone : (H (k 1)).2 = d) :
    let b : C(unitInterval, X) :=
      ⟨fun t => H.symm ((H (k t)).1, d), by fun_prop⟩
    Nonempty (b.HomotopyRel k ({0, 1} : Set unitInterval)) := by
  intro b
  let height : unitInterval × unitInterval → unitInterval := fun z =>
    ⟨(1 - (z.1 : ℝ)) * d + (z.1 : ℝ) * (H (k z.2)).2,
      by simpa only [smul_eq_mul] using
        (convex_Icc (0 : ℝ) 1) d.property (H (k z.2)).2.property
          (sub_nonneg.mpr z.1.property.2) z.1.property.1
          (show 1 - (z.1 : ℝ) + (z.1 : ℝ) = 1 by ring)⟩
  have hheight : Continuous height := by
    apply Continuous.subtype_mk
    fun_prop
  refine ⟨{
    toFun := fun z => H.symm ((H (k z.2)).1, height z)
    continuous_toFun := H.symm.continuous.comp
      ((H.continuous.comp (k.continuous.comp continuous_snd)).fst.prodMk hheight)
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ }⟩
  · intro t
    change H.symm ((H (k t)).1, height (0, t)) = H.symm ((H (k t)).1, d)
    congr 1
    refine Prod.ext rfl ?_
    apply Subtype.ext
    simp [height]
  · intro t
    have ht : height (1, t) = (H (k t)).2 := by
      apply Subtype.ext
      simp [height]
    change H.symm ((H (k t)).1, height (1, t)) = k t
    rw [ht, Prod.mk.eta, H.symm_apply_apply]
  · intro s t ht
    have htd : (H (k t)).2 = d := by
      rcases ht with rfl | rfl
      · exact hzero
      · exact hone
    have hs : height (s, t) = d := by
      apply Subtype.ext
      change (1 - (s : ℝ)) * d + (s : ℝ) * (H (k t)).2 = (d : ℝ)
      rw [htd]
      ring
    change H.symm ((H (k t)).1, height (s, t)) = H.symm ((H (k t)).1, d)
    rw [hs]

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "C0" => AddCircle (4 * (16 : ℝ))
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

theorem not_hamiltonZero_boundary_failure_of_marked_product
    {E ι : Type*} [TopologicalSpace E]
    {e : ι → OpenPartialHomeomorph X0 V3} {R : Set X0}
    (phi : C(H0, H0))
    (g : C(frontier R, C0 × C0)) (hg : IsCoveringMap g)
    (hgval : ∀ z : frontier R, g z = (Q0 (hamiltonZeroAmbientMap phi z)).1)
    (H : R ≃ₜ E × unitInterval)
    (hmark : ∀ z : R, (z : X0) ∈ frontier R ↔ (H z).2 = 0 ∨ (H z).2 = 1)
    (a b : C0) (hab : a ≠ b)
    (hlabel0 : ∀ z : R, (H z).2 = 0 → hamiltonZeroCircleMap phi z = a)
    (hlabel1 : ∀ z : R, (H z).2 = 1 → hamiltonZeroCircleMap phi z = b) :
    ¬ HamiltonZeroBoundaryFailureArc e R phi := by
  rintro ⟨param, k, _, _, hk, hkR, hkfront, _, ⟨F⟩⟩
  let kR : C(unitInterval, R) :=
    ⟨fun t => ⟨k t, hkR ⟨t, rfl⟩⟩, k.continuous.subtype_mk _⟩
  have h0 : (H (kR 0)).2 = 0 ∨ (H (kR 0)).2 = 1 :=
    (hmark _).mp ((hkfront 0).mpr (Or.inl rfl))
  have h1 : (H (kR 1)).2 = 0 ∨ (H (kR 1)).2 = 1 :=
    (hmark _).mp ((hkfront 1).mpr (Or.inr rfl))
  have hends : hamiltonZeroCircleMap phi (kR 1) = hamiltonZeroCircleMap phi (kR 0) :=
    congrArg (fun y => (Q0 y).2)
      (F.fst_eq_snd (show (1 : unitInterval) ∈ ({0, 1} : Set unitInterval) from Or.inr rfl))
  have hsame : (H (kR 0)).2 = (H (kR 1)).2 := by
    rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1
    · exact h0.trans h1.symm
    · exact False.elim (hab (((hlabel0 _ h0).symm.trans hends.symm).trans (hlabel1 _ h1)))
    · exact False.elim (hab (((hlabel0 _ h1).symm.trans hends).trans (hlabel1 _ h0)))
    · exact h0.trans h1.symm
  let d := (H (kR 0)).2
  let bR : C(unitInterval, R) := ⟨fun t => H.symm ((H (kR t)).1, d), by fun_prop⟩
  obtain ⟨G⟩ := exists_product_end_homotopyRel H kR d rfl hsame.symm
  have hbR (t : unitInterval) : (bR t : X0) ∈ frontier R := by
    apply (hmark _).mpr
    change (H (H.symm ((H (kR t)).1, d))).2 = 0 ∨
      (H (H.symm ((H (kR t)).1, d))).2 = 1
    rw [H.apply_symm_apply]
    exact h0
  let bF : C(unitInterval, frontier R) :=
    ⟨fun t => ⟨bR t, hbR t⟩, (continuous_subtype_val.comp bR.continuous).subtype_mk _⟩
  have hne : k 0 ≠ k 1 := fun h => zero_ne_one (hk.injective h)
  apply hamiltonZero_failure_arc_not_boundary_homotopic phi g hg hgval k hne
    (hamiltonZeroAmbientMap phi (k 0)) F
  exact ⟨bF, ⟨G.compContinuousMap (⟨Subtype.val, continuous_subtype_val⟩ : C(R, X0))⟩⟩

theorem not_hamiltonZero_boundary_failure_of_product_with_original_marks
    {ι : Type*} {e : ι → OpenPartialHomeomorph X0 V3} {R : Set X0}
    (phi : C(H0, H0))
    (g : C(frontier R, C0 × C0)) (hg : IsCoveringMap g)
    (hgval : ∀ z : frontier R, g z = (Q0 (hamiltonZeroAmbientMap phi z)).1)
    (ends : Bool → Set X0)
    (H : (ends false × unitInterval) ≃ₜ R)
    (hzero : ∀ x, (H (x, 0) : X0) = x)
    (hone : range (fun x => (H (x, 1) : X0)) = ends true)
    (hfront : ∀ x t, (H (x, t) : X0) ∈ frontier R ↔
      (t : ℝ) = 0 ∨ (t : ℝ) = 1)
    (a b : C0) (hab : a ≠ b)
    (hlabel0 : ∀ x ∈ ends false, hamiltonZeroCircleMap phi x = a)
    (hlabel1 : ∀ x ∈ ends true, hamiltonZeroCircleMap phi x = b) :
    ¬ HamiltonZeroBoundaryFailureArc e R phi := by
  apply not_hamiltonZero_boundary_failure_of_marked_product phi g hg hgval H.symm
    (a := a) (b := b) (hab := hab)
  · intro z
    obtain ⟨⟨x, t⟩, rfl⟩ := H.surjective z
    rw [H.symm_apply_apply]
    refine (hfront x t).trans ?_
    constructor
    · rintro (ht | ht)
      · exact Or.inl (Subtype.ext ht)
      · exact Or.inr (Subtype.ext ht)
    · rintro (rfl | rfl) <;> simp
  · intro z hz
    have heq : z = H ((H.symm z).1, 0) := by
      exact (H.apply_symm_apply z).symm.trans (congrArg H (Prod.ext rfl hz))
    rw [heq]
    exact (hzero _).symm ▸ hlabel0 _ (H.symm z).1.property
  · intro z hz
    apply hlabel1
    rw [← hone]
    refine ⟨(H.symm z).1, ?_⟩
    have heq : H ((H.symm z).1, 1) = z := by
      rw [← hz, Prod.mk.eta, H.apply_symm_apply]
    exact congrArg Subtype.val heq

theorem not_hamiltonZero_boundary_failure_of_component_products
    {ι : Type*} {e : ι → OpenPartialHomeomorph X0 V3} {R : Set X0}
    (phi : C(H0, H0))
    (g : C(frontier R, C0 × C0)) (hg : IsCoveringMap g)
    (hgval : ∀ z : frontier R, g z = (Q0 (hamiltonZeroAmbientMap phi z)).1)
    (a b : C0) (hab : a ≠ b)
    (products : ∀ x ∈ R, ∃ B : Set X0,
      ∃ H : connectedComponentIn R x ≃ₜ B × unitInterval,
        (∀ z : connectedComponentIn R x, (z : X0) ∈ frontier R ↔
          (H z).2 = 0 ∨ (H z).2 = 1) ∧
        (∀ z : connectedComponentIn R x, (H z).2 = 0 →
          hamiltonZeroCircleMap phi z = a) ∧
        (∀ z : connectedComponentIn R x, (H z).2 = 1 →
          hamiltonZeroCircleMap phi z = b)) :
    ¬ HamiltonZeroBoundaryFailureArc e R phi := by
  rintro ⟨param, k, _, _, hk, hkR, hkfront, _, ⟨F⟩⟩
  let P := connectedComponentIn R (k 0)
  have hkP : range k ⊆ P :=
    (isPreconnected_range k.continuous).subset_connectedComponentIn (mem_range_self 0) hkR
  obtain ⟨B, H, hmark, hlabel0, hlabel1⟩ := products (k 0) (hkR (mem_range_self 0))
  let kP : C(unitInterval, P) :=
    ⟨fun t => ⟨k t, hkP ⟨t, rfl⟩⟩, k.continuous.subtype_mk _⟩
  have h0 : (H (kP 0)).2 = 0 ∨ (H (kP 0)).2 = 1 :=
    (hmark _).mp ((hkfront 0).mpr (Or.inl rfl))
  have h1 : (H (kP 1)).2 = 0 ∨ (H (kP 1)).2 = 1 :=
    (hmark _).mp ((hkfront 1).mpr (Or.inr rfl))
  have hends : hamiltonZeroCircleMap phi (kP 1) = hamiltonZeroCircleMap phi (kP 0) :=
    congrArg (fun y => (Q0 y).2)
      (F.fst_eq_snd (show (1 : unitInterval) ∈ ({0, 1} : Set unitInterval) from Or.inr rfl))
  have hsame : (H (kP 0)).2 = (H (kP 1)).2 := by
    rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1
    · exact h0.trans h1.symm
    · exact False.elim (hab (((hlabel0 _ h0).symm.trans hends.symm).trans (hlabel1 _ h1)))
    · exact False.elim (hab (((hlabel0 _ h1).symm.trans hends).trans (hlabel1 _ h0)))
    · exact h0.trans h1.symm
  let d := (H (kP 0)).2
  let bP : C(unitInterval, P) := ⟨fun t => H.symm ((H (kP t)).1, d), by fun_prop⟩
  obtain ⟨G⟩ := exists_product_end_homotopyRel H kP d rfl hsame.symm
  have hbP (t : unitInterval) : (bP t : X0) ∈ frontier R := by
    apply (hmark _).mpr
    change (H (H.symm ((H (kP t)).1, d))).2 = 0 ∨
      (H (H.symm ((H (kP t)).1, d))).2 = 1
    rw [H.apply_symm_apply]
    exact h0
  let bF : C(unitInterval, frontier R) :=
    ⟨fun t => ⟨bP t, hbP t⟩, (continuous_subtype_val.comp bP.continuous).subtype_mk _⟩
  have hne : k 0 ≠ k 1 := fun h => zero_ne_one (hk.injective h)
  apply hamiltonZero_failure_arc_not_boundary_homotopic phi g hg hgval k hne
    (hamiltonZeroAmbientMap phi (k 0)) F
  exact ⟨bF, ⟨G.compContinuousMap (⟨Subtype.val, continuous_subtype_val⟩ : C(P, X0))⟩⟩

end PoincareConjecture.M76
