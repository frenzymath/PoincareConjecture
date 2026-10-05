import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.Homotopy.Basic

/-!

# The same mass deformation on the actual open superlevel

An exact affine scalar evolution keeps the strict superlevel
invariant. Restricting the original compact-superlevel homotopy
therefore gives a strong deformation on the open ambient stage,
with its entire endpoint range and every original time value
retained. See Hatcher, Theorem 3.1, pp. 45--46 and the open
ambient stage refinement in M76 derivation 270.
-/

set_option autoImplicit false

open Set unitInterval

namespace ContinuousMap

/-- The actual affine-mass homotopy restricts to the strict
superlevel as a strong deformation with exact endpoint range.
Its pointwise formula retains any additional cut invariants
of the same original homotopy. See Hatcher Theorem 3.1,
pp. 45--46 and M76 derivation 270. -/
theorem exists_homotopyRel_open_superlevel
    {M : Type*} [TopologicalSpace M] {z : M → ℝ} (hz : Continuous z)
    {c : ℝ} (hc : c < 1) {A : Set M} (hzA : ∀ x ∈ A, z x = 1)
    (T : C(I × {x : M | c ≤ z x}, M))
    (hT0 : ∀ x : {x : M | c ≤ z x}, T (0, x) = (x : M))
    (hT1 : ∀ x : {x : M | c ≤ z x}, T (1, x) ∈ A)
    (hfix : ∀ (t : I) (x : {x : M | c ≤ z x}),
      (x : M) ∈ A → T (t, x) = (x : M))
    (hmass : ∀ (t : I) (x : {x : M | c ≤ z x}),
      z (T (t, x)) = (1 - (t : ℝ)) * z x + (t : ℝ)) :
    let O : Set M := {x | c < z x}
    IsOpen O ∧ A ⊆ O ∧
      ∃ (r : C(O, O)) (H : (ContinuousMap.id O).HomotopyRel r {x | (x : M) ∈ A}),
        (∀ (t : I) (x : O), (H (t, x) : M) =
          T (t, ⟨x, (show c < z x from x.property).le⟩)) ∧
        range r = {x | (x : M) ∈ A} := by
  let P : Set M := {x | c ≤ z x}
  let O : Set M := {x | c < z x}
  let j : O → P := fun x => ⟨x, (show c < z x from x.property).le⟩
  have hj : Continuous j := continuous_subtype_val.subtype_mk _
  have hTO (t : I) (x : O) : T (t, j x) ∈ O := by
    change c < z (T (t, j x))
    rw [hmass]
    have hstrict := (convex_Ioi (𝕜 := ℝ) c) x.property hc
      (sub_nonneg.mpr t.property.2) t.property.1 (by ring)
    simpa only [smul_eq_mul, mul_one, mem_Ioi, j] using hstrict
  let L : I × O → O := fun p => ⟨T (p.1, j p.2), hTO p.1 p.2⟩
  have hL : Continuous L := (T.continuous.comp
    (continuous_fst.prodMk (hj.comp continuous_snd))).subtype_mk _
  let r : C(O, O) :=
    ⟨fun x => L (1, x), hL.comp (continuous_const.prodMk continuous_id)⟩
  let H : (ContinuousMap.id O).HomotopyRel r {x | (x : M) ∈ A} :=
    { toContinuousMap := ⟨L, hL⟩
      map_zero_left := fun x => Subtype.ext (hT0 (j x))
      map_one_left := fun _ => rfl
      prop' := fun t x hx => Subtype.ext (hfix t (j x) hx) }
  refine ⟨isOpen_lt continuous_const hz, ?_, r, H, fun _ _ => rfl, ?_⟩
  · intro x hx
    change c < z x
    rw [hzA x hx]
    exact hc
  · change Subtype.val '' range r = A
    ext x
    constructor
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
      exact hT1 (j y)
    · intro hx
      have hxO : x ∈ O := by
        change c < z x
        rw [hzA x hx]
        exact hc
      exact ⟨⟨x, hxO⟩, ⟨⟨x, hxO⟩, H.eq_fst 1 hx⟩, rfl⟩

end ContinuousMap
