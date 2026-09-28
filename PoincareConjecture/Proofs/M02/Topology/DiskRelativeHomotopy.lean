import PoincareConjecture.Proofs.M02.Topology.SphereDiskExtension

set_option autoImplicit false

open Set Metric
open scoped Topology unitInterval

universe u

namespace PoincareConjecture.Proofs.M02.Topology

noncomputable section

theorem exists_characteristic_prism_coordinates (m : Nat) :
    ∃ e : (unitInterval × closedBall (0 : Fin m → ℝ) 1) ≃ₜ
        closedBall (0 : Fin (m + 1) → ℝ) 1,
      ∀ p, ‖(e p).val‖ = 1 ↔ p.1 = 0 ∨ p.1 = 1 ∨ ‖p.2.val‖ = 1 := by
  obtain ⟨b, hb⟩ := exists_cube_ball_coordinates m
  obtain ⟨c, hc⟩ := exists_cube_ball_coordinates (m + 1)
  let split : (Fin (m + 1) → unitInterval) ≃ₜ unitInterval × (Fin m → unitInterval) :=
    { toFun := fun z => (z 0, fun i => z i.succ)
      invFun := fun p => Fin.cons p.1 p.2
      left_inv := by intro z; funext i; exact Fin.cases rfl (fun _ => rfl) i
      right_inv := by intro p; exact Prod.ext rfl rfl
      continuous_toFun := (continuous_apply 0).prodMk (continuous_pi fun i =>
        continuous_apply i.succ)
      continuous_invFun := by
        apply continuous_pi
        intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact continuous_fst
        · exact (continuous_apply j).comp continuous_snd }
  let e : (unitInterval × closedBall (0 : Fin m → ℝ) 1) ≃ₜ
      closedBall (0 : Fin (m + 1) → ℝ) 1 :=
    ((Homeomorph.refl unitInterval).prodCongr b.symm).trans (split.symm.trans c)
  refine ⟨e, fun p => ?_⟩
  change ‖(c (Fin.cons p.1 (b.symm p.2))).val‖ = 1 ↔ _
  rw [← hc]
  have htail : b.symm p.2 ∈ Cube.boundary (Fin m) ↔ ‖p.2.val‖ = 1 := by
    simpa only [b.apply_symm_apply] using hb (b.symm p.2)
  rw [← htail]
  constructor
  · rintro ⟨i, hi⟩
    induction i using Fin.cases with
    | zero => exact hi.elim Or.inl (fun h => Or.inr (Or.inl h))
    | succ i => exact Or.inr (Or.inr ⟨i, hi⟩)
  · rintro (h | h | ⟨i, hi⟩)
    · exact ⟨0, Or.inl h⟩
    · exact ⟨0, Or.inr h⟩
    · exact ⟨i.succ, hi⟩

theorem exists_disk_relative_homotopy_of_pi_trivial
    {Y : Type u} [TopologicalSpace Y] (n : Nat)
    (hpi : ∀ y : Y, Subsingleton (HomotopyGroup.Pi (n + 1) Y y))
    (f g : C(closedBall (0 : Fin (n + 1) → ℝ) 1, Y))
    (H : C(unitInterval × sphere (0 : Fin (n + 1) → ℝ) 1, Y))
    (h0 : ∀ z : sphere (0 : Fin (n + 1) → ℝ) 1,
      H (0, z) = f ⟨z.val, sphere_subset_closedBall z.property⟩)
    (h1 : ∀ z : sphere (0 : Fin (n + 1) → ℝ) 1,
      H (1, z) = g ⟨z.val, sphere_subset_closedBall z.property⟩) :
    ∃ F : C(unitInterval × closedBall (0 : Fin (n + 1) → ℝ) 1, Y),
      (∀ z, F (0, z) = f z) ∧ (∀ z, F (1, z) = g z) ∧
      (∀ (t : unitInterval) (z : sphere (0 : Fin (n + 1) → ℝ) 1),
        F (t, ⟨z.val, sphere_subset_closedBall z.property⟩) = H (t, z)) := by
  let D := closedBall (0 : Fin (n + 1) → ℝ) 1
  let S := sphere (0 : Fin (n + 1) → ℝ) 1
  let A : Set (unitInterval × D) := {p | p.1 = 0 ∨ p.1 = 1 ∨ ‖p.2.val‖ = 1}
  let Q : C((D ⊕ D) ⊕ (unitInterval × S), A) :=
    ⟨Sum.elim
      (Sum.elim (fun z => ⟨(0, z), Or.inl rfl⟩) (fun z => ⟨(1, z), Or.inr (Or.inl rfl)⟩))
      (fun p => ⟨(p.1, ⟨p.2.val, sphere_subset_closedBall p.2.property⟩),
        Or.inr (Or.inr (mem_sphere_zero_iff_norm.mp p.2.property))⟩), by
          apply continuous_sum_dom.mpr
          constructor
          · apply continuous_sum_dom.mpr
            constructor <;> fun_prop
          · fun_prop⟩
  have hsurj : Function.Surjective Q := by
    rintro ⟨p, hp | hp | hp⟩
    · exact ⟨Sum.inl (Sum.inl p.2), Subtype.ext (Prod.ext hp.symm rfl)⟩
    · exact ⟨Sum.inl (Sum.inr p.2), Subtype.ext (Prod.ext hp.symm rfl)⟩
    · exact ⟨Sum.inr (p.1, ⟨p.2.val, mem_sphere_zero_iff_norm.mpr hp⟩), rfl⟩
  let l : C((D ⊕ D) ⊕ (unitInterval × S), Y) :=
    ⟨Sum.elim (Sum.elim f g) H,
      continuous_sum_dom.mpr ⟨continuous_sum_dom.mpr ⟨f.continuous, g.continuous⟩, H.continuous⟩⟩
  have hfactor : Function.FactorsThrough l Q := by
    intro a b hab
    cases a with
    | inl a =>
      cases b with
      | inl b =>
        cases a with
        | inl x =>
          cases b with
          | inl y => exact congrArg f (congrArg (fun p : A => p.val.2) hab)
          | inr y => exact (zero_ne_one (congrArg (fun p : A => p.val.1) hab)).elim
        | inr x =>
          cases b with
          | inl y => exact (one_ne_zero (congrArg (fun p : A => p.val.1) hab)).elim
          | inr y => exact congrArg g (congrArg (fun p : A => p.val.2) hab)
      | inr p =>
        cases a with
        | inl x =>
          have ht : (0 : unitInterval) = p.1 := congrArg (fun p : A => p.val.1) hab
          have hx : x = ⟨p.2.val, sphere_subset_closedBall p.2.property⟩ :=
            congrArg (fun p : A => p.val.2) hab
          change f x = H p
          exact (congrArg f hx).trans
            ((h0 p.2).symm.trans (congrArg H (show (0, p.2) = p from Prod.ext ht rfl)))
        | inr x =>
          have ht : (1 : unitInterval) = p.1 := congrArg (fun p : A => p.val.1) hab
          have hx : x = ⟨p.2.val, sphere_subset_closedBall p.2.property⟩ :=
            congrArg (fun p : A => p.val.2) hab
          change g x = H p
          exact (congrArg g hx).trans
            ((h1 p.2).symm.trans (congrArg H (show (1, p.2) = p from Prod.ext ht rfl)))
    | inr p =>
      cases b with
      | inl b =>
        cases b with
        | inl x =>
          have ht : p.1 = (0 : unitInterval) := congrArg (fun p : A => p.val.1) hab
          have hx : (⟨p.2.val, sphere_subset_closedBall p.2.property⟩ : D) = x :=
            congrArg (fun p : A => p.val.2) hab
          change H p = f x
          exact (congrArg H (show p = (0, p.2) from Prod.ext ht rfl)).trans
            ((h0 p.2).trans (congrArg f hx))
        | inr x =>
          have ht : p.1 = (1 : unitInterval) := congrArg (fun p : A => p.val.1) hab
          have hx : (⟨p.2.val, sphere_subset_closedBall p.2.property⟩ : D) = x :=
            congrArg (fun p : A => p.val.2) hab
          change H p = g x
          exact (congrArg H (show p = (1, p.2) from Prod.ext ht rfl)).trans
            ((h1 p.2).trans (congrArg g hx))
      | inr q =>
        have ht : p.1 = q.1 := congrArg (fun p : A => p.val.1) hab
        have hx : p.2.val = q.2.val := congrArg (fun p : A => p.val.2.val) hab
        exact congrArg H (Prod.ext ht (Subtype.ext hx))
  have hQ : _root_.Topology.IsQuotientMap Q :=
    .of_surjective_continuous hsurj Q.continuous
  let L := hQ.lift l hfactor
  have hL (z : (D ⊕ D) ⊕ (unitInterval × S)) : L (Q z) = l z :=
    DFunLike.congr_fun (hQ.lift_comp l hfactor) z
  obtain ⟨e, he⟩ := exists_characteristic_prism_coordinates (n + 1)
  let incl : C(sphere (0 : Fin (n + 2) → ℝ) 1, closedBall (0 : Fin (n + 2) → ℝ) 1) :=
    ⟨fun z => ⟨z.val, sphere_subset_closedBall z.property⟩, continuous_subtype_val.subtype_mk _⟩
  have heinv (z : sphere (0 : Fin (n + 2) → ℝ) 1) : e.symm (incl z) ∈ A := by
    apply (he (e.symm (incl z))).mp
    rw [e.apply_symm_apply]
    exact mem_sphere_zero_iff_norm.mp z.property
  let a : C(sphere (0 : Fin (n + 2) → ℝ) 1, A) :=
    ⟨fun z => ⟨e.symm (incl z), heinv z⟩, (e.symm.continuous.comp incl.continuous).subtype_mk _⟩
  obtain ⟨T, hT⟩ := exists_characteristic_disk_extension n hpi (L.comp a)
  let F : C(unitInterval × D, Y) := T.comp (e : C(_, _))
  have hboundary (p : A) : F p.val = L p := by
    let z : sphere (0 : Fin (n + 2) → ℝ) 1 :=
      ⟨(e p.val).val, mem_sphere_zero_iff_norm.mpr ((he p.val).mpr p.property)⟩
    have hz : a z = p := Subtype.ext (e.symm_apply_apply p.val)
    have h := hT z
    change T (e p.val) = L (a z) at h
    rw [hz] at h
    exact h
  refine ⟨F, ?_, ?_, ?_⟩
  · intro z
    exact (hboundary (Q (Sum.inl (Sum.inl z)))).trans (hL (Sum.inl (Sum.inl z)))
  · intro z
    exact (hboundary (Q (Sum.inl (Sum.inr z)))).trans (hL (Sum.inl (Sum.inr z)))
  · intro t z
    exact (hboundary (Q (Sum.inr (t, z)))).trans (hL (Sum.inr (t, z)))

end

end PoincareConjecture.Proofs.M02.Topology
