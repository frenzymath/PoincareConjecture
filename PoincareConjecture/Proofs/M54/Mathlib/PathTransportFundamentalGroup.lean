import PoincareConjecture.Proofs.M54.Mathlib.PathTransportExtension

set_option autoImplicit false

open Set
open scoped unitInterval

namespace LocalPathTransport

variable {X ι G : Type*} [TopologicalSpace X] {U : ι → Set X} [Monoid G]

noncomputable def global (L : LocalPathTransport U G)
    (hU : ∀ i, IsOpen (U i)) (hcover : univ ⊆ ⋃ i, U i) :
    LocalPathTransport (fun _ : Unit => (univ : Set X)) G where
  value := L.extend hU hcover
  map_const := L.extend_const hU hcover
  square H _ _ := L.extend_square hU hcover H

variable (L : LocalPathTransport (fun _ : Unit => (univ : Set X)) G)

theorem value_homotopic {x y : X} {p q : Path x y} (hpq : p.Homotopic q) :
    L.value p.toContinuousMap = L.value q.toContinuousMap := by
  obtain ⟨H⟩ := hpq
  let S : C(unitInterval × unitInterval, X) :=
    ⟨fun z => H (z.2, z.1), H.continuous.comp continuous_swap⟩
  have hb : S.horizontalPath 0 = p.toContinuousMap := by ext t; simp [S]
  have ht : S.horizontalPath 1 = q.toContinuousMap := by ext t; simp [S]
  have hl : S.verticalPath 0 = .const _ x := by ext t; simp [S]
  have hr : S.verticalPath 1 = .const _ y := by ext t; simp [S]
  have h := L.square S () (fun _ => mem_univ _)
  simpa only [hb, ht, hl, hr, L.map_const, mul_one, one_mul] using h

theorem value_trans {x y z : X} (p : Path x y) (q : Path y z) :
    L.value (p.trans q).toContinuousMap =
      L.value p.toContinuousMap * L.value q.toContinuousMap := by
  let half : unitInterval := ⟨1 / 2, by constructor <;> norm_num⟩
  have hleft : (p.trans q).toContinuousMap.intervalSubpath 0 half = p.toContinuousMap := by
    ext t
    change (p.trans q) (Icc.convexComb 0 half t) = p t
    calc
      _ = (p.trans q).extend (Icc.convexComb 0 half t) :=
        ((p.trans q).extend_extends' _).symm
      _ = p.extend (2 * (Icc.convexComb 0 half t : ℝ)) :=
        p.extend_trans_of_le_half q (by
          change (1 - (t : ℝ)) * 0 + (t : ℝ) * (1 / 2) ≤ 1 / 2
          linarith [t.2.2])
      _ = p.extend t := by congr 1; simp [Icc.coe_convexComb, half]; ring
      _ = p t := p.extend_extends' t
  have hright : (p.trans q).toContinuousMap.intervalSubpath half 1 = q.toContinuousMap := by
    ext t
    change (p.trans q) (Icc.convexComb half 1 t) = q t
    calc
      _ = (p.trans q).extend (Icc.convexComb half 1 t) :=
        ((p.trans q).extend_extends' _).symm
      _ = q.extend (2 * (Icc.convexComb half 1 t : ℝ) - 1) :=
        p.extend_trans_of_half_le q (by
          change 1 / 2 ≤ (1 - (t : ℝ)) * (1 / 2) + (t : ℝ) * 1
          linarith [t.2.1])
      _ = q.extend t := by congr 1; simp [Icc.coe_convexComb, half]; ring
      _ = q t := q.extend_extends' t
  have h := L.interval_mul (p.trans q).toContinuousMap
    (a := 0) (b := half) (c := 1)
    (by change (0 : ℝ) ≤ 1 / 2; norm_num)
    (by change (1 / 2 : ℝ) ≤ 1; norm_num) () (fun _ _ => mem_univ _)
  simpa only [hleft, hright, ContinuousMap.intervalSubpath_zero_one] using h.symm

noncomputable def toMonoidHom
    (L : LocalPathTransport (fun _ : Unit => (univ : Set X)) Gᵐᵒᵖ) (x : X) :
    FundamentalGroup X x →* G where
  toFun := Quotient.lift (fun p : Path x x => MulOpposite.unop (L.value p.toContinuousMap))
    (fun _ _ h => congrArg MulOpposite.unop (L.value_homotopic h))
  map_one' := by
    change MulOpposite.unop (L.value (.const _ x)) = 1
    rw [L.map_const]
    rfl
  map_mul' := by
    intro p q
    induction p using Path.Homotopic.Quotient.ind with
    | mk p =>
      induction q using Path.Homotopic.Quotient.ind with
      | mk q =>
        change MulOpposite.unop (L.value (q.trans p).toContinuousMap) =
          MulOpposite.unop (L.value p.toContinuousMap) *
            MulOpposite.unop (L.value q.toContinuousMap)
        rw [L.value_trans]
        rfl

@[simp] theorem toMonoidHom_mk
    (L : LocalPathTransport (fun _ : Unit => (univ : Set X)) Gᵐᵒᵖ) (x : X)
    (p : Path x x) :
    L.toMonoidHom x (Path.Homotopic.Quotient.mk p) =
      MulOpposite.unop (L.value p.toContinuousMap) := rfl

end LocalPathTransport
