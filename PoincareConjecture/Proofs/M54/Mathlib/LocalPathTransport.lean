import PoincareConjecture.Proofs.M54.Mathlib.PathSubdivision










set_option autoImplicit false

open Set
open scoped unitInterval

namespace ContinuousMap

variable {X : Type*} [TopologicalSpace X]



def intervalSubpath (p : C(unitInterval, X)) (a b : unitInterval) : C(unitInterval, X) :=
  p.comp (Path.parameterSegment a b).toContinuousMap



@[simp] theorem intervalSubpath_apply (p : C(unitInterval, X)) (a b t : unitInterval) :
    p.intervalSubpath a b t = p (Icc.convexComb a b t) := rfl



@[simp] theorem intervalSubpath_zero_one (p : C(unitInterval, X)) :
    p.intervalSubpath 0 1 = p := by
  ext t
  simp



@[simp] theorem intervalSubpath_self (p : C(unitInterval, X)) (a : unitInterval) :
    p.intervalSubpath a a = .const _ (p a) := by
  ext t
  simp



def horizontalPath (H : C(unitInterval × unitInterval, X)) (t : unitInterval) :
    C(unitInterval, X) := H.comp ⟨fun s => (s, t), by fun_prop⟩



def verticalPath (H : C(unitInterval × unitInterval, X)) (s : unitInterval) :
    C(unitInterval, X) := H.comp ⟨fun t => (s, t), by fun_prop⟩



@[simp] theorem horizontalPath_apply (H : C(unitInterval × unitInterval, X))
    (s t : unitInterval) : H.horizontalPath t s = H (s, t) := rfl



@[simp] theorem verticalPath_apply (H : C(unitInterval × unitInterval, X))
    (s t : unitInterval) : H.verticalPath s t = H (s, t) := rfl



def rectangleRestrict (H : C(unitInterval × unitInterval, X))
    (a b c d : unitInterval) : C(unitInterval × unitInterval, X) :=
  H.comp ⟨fun z => (Icc.convexComb a b z.1, Icc.convexComb c d z.2),
    ((Icc.continuous_convexComb a b).comp continuous_fst).prodMk
      ((Icc.continuous_convexComb c d).comp continuous_snd)⟩



@[simp] theorem rectangleRestrict_apply (H : C(unitInterval × unitInterval, X))
    (a b c d : unitInterval) (z : unitInterval × unitInterval) :
    H.rectangleRestrict a b c d z =
      H (Icc.convexComb a b z.1, Icc.convexComb c d z.2) := rfl



@[simp] theorem rectangleRestrict_bottom (H : C(unitInterval × unitInterval, X))
    (a b c d : unitInterval) :
    (H.rectangleRestrict a b c d).horizontalPath 0 =
      (H.horizontalPath c).intervalSubpath a b := by
  ext t
  simp



@[simp] theorem rectangleRestrict_top (H : C(unitInterval × unitInterval, X))
    (a b c d : unitInterval) :
    (H.rectangleRestrict a b c d).horizontalPath 1 =
      (H.horizontalPath d).intervalSubpath a b := by
  ext t
  simp



@[simp] theorem rectangleRestrict_left (H : C(unitInterval × unitInterval, X))
    (a b c d : unitInterval) :
    (H.rectangleRestrict a b c d).verticalPath 0 =
      (H.verticalPath a).intervalSubpath c d := by
  ext t
  simp



@[simp] theorem rectangleRestrict_right (H : C(unitInterval × unitInterval, X))
    (a b c d : unitInterval) :
    (H.rectangleRestrict a b c d).verticalPath 1 =
      (H.verticalPath b).intervalSubpath c d := by
  ext t
  simp

end ContinuousMap




structure LocalPathTransport {X ι : Type*} [TopologicalSpace X]
    (U : ι → Set X) (G : Type*) [Monoid G] where


  value : C(unitInterval, X) → G


  map_const : ∀ x, value (.const _ x) = 1


  square : ∀ (H : C(unitInterval × unitInterval, X)) (i : ι),
    (∀ z, H z ∈ U i) →
      value (H.horizontalPath 0) * value (H.verticalPath 1) =
        value (H.verticalPath 0) * value (H.horizontalPath 1)

namespace LocalPathTransport

variable {X ι G : Type*} [TopologicalSpace X] {U : ι → Set X} [Monoid G]

private theorem convexComb_mem {a b x y : unitInterval}
    (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) (t : unitInterval) :
    Icc.convexComb x y t ∈ Icc a b := by
  rcases le_total x y with h | h
  · exact ⟨hx.1.trans (Icc.le_convexComb h t), (Icc.convexComb_le h t).trans hy.2⟩
  · rw [← Icc.convexComb_symm y x]
    exact ⟨hy.1.trans (Icc.le_convexComb h _), (Icc.convexComb_le h _).trans hx.2⟩



theorem interval_mul (L : LocalPathTransport U G) (p : C(unitInterval, X))
    {a b c : unitInterval} (hab : a ≤ b) (hbc : b ≤ c) (i : ι)
    (hp : MapsTo p (Icc a c) (U i)) :
    L.value (p.intervalSubpath a b) * L.value (p.intervalSubpath b c) =
      L.value (p.intervalSubpath a c) := by
  let H : C(unitInterval × unitInterval, X) :=
    p.comp ⟨fun z => Icc.convexComb (Icc.convexComb a b z.1)
      (Icc.convexComb a c z.1) z.2,
      Icc.continuous_convexComb_prod.comp
        (((Icc.continuous_convexComb a b).comp continuous_fst).prodMk
          (((Icc.continuous_convexComb a c).comp continuous_fst).prodMk continuous_snd))⟩
  have h := L.square H i (fun z => hp (convexComb_mem
    ⟨Icc.le_convexComb hab z.1, (Icc.convexComb_le hab z.1).trans hbc⟩
    ⟨Icc.le_convexComb (hab.trans hbc) z.1, Icc.convexComb_le (hab.trans hbc) z.1⟩ z.2))
  have hbottom : H.horizontalPath 0 = p.intervalSubpath a b := by ext t; simp [H]
  have hright : H.verticalPath 1 = p.intervalSubpath b c := by ext t; simp [H]
  have hleft : H.verticalPath 0 = .const _ (p a) := by ext t; simp [H]
  have htop : H.horizontalPath 1 = p.intervalSubpath a c := by ext t; simp [H]
  simpa only [hbottom, hright, hleft, htop, L.map_const, one_mul] using h

end LocalPathTransport
