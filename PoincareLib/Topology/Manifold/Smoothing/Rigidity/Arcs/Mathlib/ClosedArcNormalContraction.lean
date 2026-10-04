import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Arcs.Mathlib.CircleClosedArc
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.Homotopy.Basic

/-!
# The actual relative normal contraction in a complete quotient arc

The inverse of the original open quotient chart constructs the real
normal representative of every point in the closed arc. Linear
interpolation fixes the entire selected phase, preserves tangent
coordinates and stays in the whole closed slab. See Waldhausen1968,
p.60, and rigidity057, section3.
-/

set_option autoImplicit false

open Set

namespace AddCircle

variable {W Z : Type*} [TopologicalSpace W] [TopologicalSpace Z]

/-- A map into a complete product slab has an actual continuous
normal contraction relative to the entire selected phase. The real
representative is constructed from the quotient chart, not supplied;
no assertion of PL dependence on time is made. See rigidity057, section3. -/
theorem exists_closedArc_normal_contraction
    (p : ℝ) [Fact (0 < p)] {a b theta : ℝ}
    (ha : 0 < a) (hb : b < p) (htheta : theta ∈ Icc a b)
    (f : C(W, Z × AddCircle p))
    (hf : ∀ x, (f x).2 ∈ closedIntervalArc p a b) :
    ∃ H : f.HomotopyRel
        ⟨fun x => ((f x).1, (theta : AddCircle p)),
          f.continuous.fst.prodMk continuous_const⟩
        {x | (f x).2 = (theta : AddCircle p)},
      ∀ (t : unitInterval) (x : W),
        (H (t, x)).1 = (f x).1 ∧
        (H (t, x)).2 ∈ closedIntervalArc p a b ∧
        (H (t, x)).2 =
          (((1 - (t : ℝ)) * (openPartialHomeomorphCoe p 0).symm (f x).2 +
            (t : ℝ) * theta : ℝ) : AddCircle p) := by
  let J := openPartialHomeomorphCoe p 0
  have hsource (u : ℝ) (hu : u ∈ Icc a b) : u ∈ J.source := by
    change u ∈ Ioo (0 : ℝ) (0 + p)
    exact ⟨ha.trans_le hu.1, by simpa only [zero_add] using hu.2.trans_lt hb⟩
  have htarget (x : W) : (f x).2 ∈ J.target := by
    obtain ⟨u, hu, huf⟩ := hf x
    have hJu : J u = (f x).2 := huf
    rw [← hJu]
    exact J.map_source (hsource u hu)
  let l : C(W, ℝ) := ⟨fun x => J.symm (f x).2,
    J.continuousOn_symm.comp_continuous f.continuous.snd htarget⟩
  have hl (x : W) : l x ∈ Icc a b ∧ (l x : AddCircle p) = (f x).2 := by
    obtain ⟨u, hu, huf⟩ := hf x
    have hJu : J u = (f x).2 := huf
    have hlu : l x = u := by
      change J.symm (f x).2 = u
      rw [← hJu, J.left_inv (hsource u hu)]
    rw [hlu]
    exact ⟨hu, huf⟩
  have hltheta (x : W) (hx : (f x).2 = (theta : AddCircle p)) : l x = theta := by
    change J.symm (f x).2 = theta
    rw [hx]
    exact J.left_inv (hsource theta htheta)
  let r : C(W, Z × AddCircle p) :=
    ⟨fun x => ((f x).1, (theta : AddCircle p)),
      f.continuous.fst.prodMk continuous_const⟩
  let H : f.HomotopyRel r {x | (f x).2 = (theta : AddCircle p)} := {
    toFun := fun z => ((f z.2).1,
      (((1 - (z.1 : ℝ)) * l z.2 + (z.1 : ℝ) * theta : ℝ) : AddCircle p))
    continuous_toFun := (f.continuous.fst.comp continuous_snd).prodMk
      ((AddCircle.continuous_mk' p).comp
        (((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
          (l.continuous.comp continuous_snd)).add
            ((continuous_subtype_val.comp continuous_fst).mul continuous_const)))
    map_zero_left := by
      intro x
      apply Prod.ext
      · rfl
      · change (((1 - (0 : ℝ)) * l x + (0 : ℝ) * theta : ℝ) : AddCircle p) = (f x).2
        simpa only [sub_zero, one_mul, zero_mul, add_zero] using (hl x).2
    map_one_left := by
      intro x
      apply Prod.ext
      · rfl
      · change (((1 - (1 : ℝ)) * l x + (1 : ℝ) * theta : ℝ) : AddCircle p) =
          (theta : AddCircle p)
        simp only [sub_self, zero_mul, one_mul, zero_add]
    prop' := by
      intro t x hx
      change ((f x).1,
        (((1 - (t : ℝ)) * l x + (t : ℝ) * theta : ℝ) : AddCircle p)) = f x
      have hvalue : (1 - (t : ℝ)) * l x + (t : ℝ) * theta = theta := by
        rw [hltheta x hx]
        ring
      apply Prod.ext
      · rfl
      · rw [hvalue]
        exact hx.symm
  }
  refine ⟨H, ?_⟩
  intro t x
  refine ⟨rfl, ?_, rfl⟩
  have hconvex : (1 - (t : ℝ)) * l x + (t : ℝ) * theta ∈ Icc a b := by
    simpa only [smul_eq_mul] using
      (convex_Icc a b) (hl x).1 htheta (sub_nonneg.mpr t.property.2) t.property.1
        (show 1 - (t : ℝ) + (t : ℝ) = 1 by ring)
  exact ⟨_, hconvex, rfl⟩

end AddCircle
