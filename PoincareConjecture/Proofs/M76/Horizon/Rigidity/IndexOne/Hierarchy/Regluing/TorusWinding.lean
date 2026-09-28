import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Hierarchy.Annuli.Winding

set_option autoImplicit false
open Set

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "I" => unitInterval
local notation "p" => (4 * (128 : ℝ))
local notation "C" => AddCircle p
local notation "T" => (Fin 2 → C)

private instance : Fact (0 < p) := ⟨by norm_num⟩

noncomputable def torusIntegerTwist (n : Fin 2 → ℤ) : (I × T) ≃ₜ (I × T) where
  toFun x := (x.1, fun i => x.2 i + ((p * (n i : ℝ) * (x.1 : ℝ) : ℝ) : C))
  invFun x := (x.1, fun i => x.2 i - ((p * (n i : ℝ) * (x.1 : ℝ) : ℝ) : C))
  left_inv x := by simp
  right_inv x := by simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem torusIntegerTwist_boundary (n : Fin 2 → ℤ) (x : I × T)
    (hx : x.1 = 0 ∨ x.1 = 1) : torusIntegerTwist n x = x := by
  apply Prod.ext
  · rfl
  · funext i
    have hn : ((p * (n i : ℝ) : ℝ) : C) = 0 :=
      (AddCircle.coe_eq_zero_iff p).mpr ⟨n i, by simp [zsmul_eq_mul]; ring⟩
    rcases hx with hx | hx <;> simp [torusIntegerTwist, hx, hn]

theorem exists_torus_winding_correction (f : C(I × T, I × T))
    (hzero : ∀ z, f (0, z) = (0, z)) (hone : ∀ z, f (1, z) = (1, z)) :
    ∃ n : Fin 2 → ℤ, Nonempty ((f.comp
      ⟨torusIntegerTwist n, (torusIntegerTwist n).continuous⟩).HomotopyRel
        (ContinuousMap.id (I × T)) {x | x.1 = 0 ∨ x.1 = 1}) := by
  classical
  let error (i : Fin 2) : C(I × T, C) := ⟨fun x => (f x).2 i - x.2 i, by fun_prop⟩
  let zeroLift : C(T, ℝ) := ContinuousMap.const T 0
  have he0 (i : Fin 2) (z : T) : error i (0, z) = (zeroLift z : C) := by
    change (f (0, z)).2 i - z i = (0 : C)
    rw [hzero]
    simp
  let cov := AddCircle.isCoveringMap_coe p
  let lift (i : Fin 2) := cov.liftHomotopy (error i) zeroLift (he0 i)
  have hlift (i : Fin 2) (x : I × T) : (lift i x : C) = (f x).2 i - x.2 i :=
    congrFun (cov.liftHomotopy_lifts (error i) zeroLift (he0 i)) x
  have hlift0 (i : Fin 2) (z : T) : lift i (0, z) = 0 :=
    cov.liftHomotopy_zero (error i) zeroLift (he0 i) z
  have hlift1 (i : Fin 2) (z : T) : lift i (1, z) = lift i (1, 0) := by
    apply cov.const_of_comp (g := fun z : T => lift i (1, z)) (by fun_prop) _ z 0
    intro z w
    rw [hlift, hlift, hone, hone]
    simp
  have htop (i : Fin 2) : (lift i (1, 0) : C) = 0 := by rw [hlift, hone]; simp
  have hn : ∀ i : Fin 2, ∃ n : ℤ, p * (n : ℝ) = lift i (1, 0) := by
    intro i
    obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff p).mp (htop i)
    exact ⟨n, by rw [← hn]; simp [zsmul_eq_mul]; ring⟩
  choose n hn using hn
  have hn' (i : Fin 2) (z : T) : lift i (1, z) = p * (n i : ℝ) :=
    (hlift1 i z).trans (hn i).symm
  let shift : C(I × T, I × T) :=
    ⟨torusIntegerTwist (-n), (torusIntegerTwist (-n)).continuous⟩
  let g := f.comp shift
  let remaining (i : Fin 2) : C(I × T, ℝ) :=
    ⟨fun x => lift i (shift x) + p * ((-n i : ℤ) : ℝ) * (x.1 : ℝ), by fun_prop⟩
  have hremaining (i : Fin 2) (x : I × T) :
      (remaining i x : C) = (g x).2 i - x.2 i := by
    change ((lift i (shift x) + p * ((-n i : ℤ) : ℝ) * (x.1 : ℝ) : ℝ) : C) = _
    rw [AddCircle.coe_add, hlift]
    change (f (shift x)).2 i -
      (x.2 i + ((p * ((-n i : ℤ) : ℝ) * (x.1 : ℝ) : ℝ) : C)) +
      ((p * ((-n i : ℤ) : ℝ) * (x.1 : ℝ) : ℝ) : C) = (f (shift x)).2 i - x.2 i
    abel
  have hremBoundary (i : Fin 2) (x : I × T) (hx : x.1 = 0 ∨ x.1 = 1) :
      remaining i x = 0 := by
    change lift i (shift x) + p * ((-n i : ℤ) : ℝ) * (x.1 : ℝ) = 0
    rw [show shift x = x from torusIntegerTwist_boundary (-n) x hx]
    rcases x with ⟨t, z⟩
    rcases hx with hx | hx
    · change t = 0 at hx
      subst t
      simp [hlift0]
    · change t = 1 at hx
      subst t
      rw [hn']
      simp
  have hgBoundary (x : I × T) (hx : x.1 = 0 ∨ x.1 = 1) : g x = x := by
    change f (shift x) = x
    rw [show shift x = x from torusIntegerTwist_boundary (-n) x hx]
    rcases x with ⟨t, z⟩
    rcases hx with hx | hx
    · change t = 0 at hx
      subst t
      exact hzero z
    · change t = 1 at hx
      subst t
      exact hone z
  refine ⟨-n, ⟨{
    toFun := fun z => (Icc.convexComb (g z.2).1 z.2.1 z.1,
      fun i => z.2.2 i + (((1 - (z.1 : ℝ)) * remaining i z.2 : ℝ) : C))
    continuous_toFun := by fun_prop
    map_zero_left := by
      intro x
      apply Prod.ext
      · change Icc.convexComb (g x).1 x.1 0 = (g x).1
        simp
      · funext i
        change x.2 i + (((1 - (0 : ℝ)) * remaining i x : ℝ) : C) = (g x).2 i
        simp only [sub_zero, one_mul, hremaining]
        abel
    map_one_left := by intro x; simp
    prop' := by
      intro t x hx
      change (Icc.convexComb (g x).1 x.1 t,
        fun i => x.2 i + (((1 - (t : ℝ)) * remaining i x : ℝ) : C)) = g x
      rw [hgBoundary x hx]
      apply Prod.ext
      · simp
      · funext i
        change x.2 i + (((1 - (t : ℝ)) * remaining i x : ℝ) : C) = x.2 i
        rw [hremBoundary i x hx]
        simp }⟩⟩

end PoincareConjecture.M76.HamiltonIntervalTorus
