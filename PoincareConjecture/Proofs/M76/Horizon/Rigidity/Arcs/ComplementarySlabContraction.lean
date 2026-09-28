import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.CircleClosedArc
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open Set

namespace AddCircle

theorem compl_interior_closedIntervalArc (p : ℝ) [Fact (0 < p)]
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < p) :
    (interior (closedIntervalArc p a b))ᶜ = closedIntervalArc p b (a + p) := by
  rw [interior_closedIntervalArc p ha hb]
  ext z
  constructor
  · intro hz
    obtain ⟨t, ht, htz⟩ := eq_coe_Ico z
    by_cases hbt : b ≤ t
    · exact ⟨t, ⟨hbt, by linarith [ht.2]⟩, htz⟩
    · have hta : t ≤ a := by
        by_contra! hat
        exact hz ⟨t, ⟨hat, lt_of_not_ge hbt⟩, htz⟩
      exact ⟨t + p, ⟨by linarith [ht.1], by linarith⟩,
        (coe_add_period p t).trans htz⟩
  · rintro ⟨t, ht, rfl⟩ ⟨u, hu, hut⟩
    have htI : t ∈ Ioc a (a + p) := ⟨hab.trans_le ht.1, ht.2⟩
    have huI : u ∈ Ioc a (a + p) := ⟨hu.1, by linarith [hu.2]⟩
    have hEq : u = t := (coe_eq_coe_iff_of_mem_Ioc huI htI).mp hut
    linarith [hu.2, ht.1]

variable {W Z : Type*} [TopologicalSpace W] [TopologicalSpace Z]

theorem exists_shifted_closedArc_normal_contraction
    (p : ℝ) [Fact (0 < p)] {c a b theta : ℝ}
    (ha : c < a) (hb : b < c + p) (htheta : theta ∈ Icc a b)
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
          (((1 - (t : ℝ)) * (openPartialHomeomorphCoe p c).symm (f x).2 +
            (t : ℝ) * theta : ℝ) : AddCircle p) := by
  let J := openPartialHomeomorphCoe p c
  have hsource (u : ℝ) (hu : u ∈ Icc a b) : u ∈ J.source :=
    ⟨ha.trans_le hu.1, hu.2.trans_lt hb⟩
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

theorem exists_complementarySlab_normal_contraction
    (p : ℝ) [Fact (0 < p)] {a b theta : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b < p) (htheta : theta ∈ Icc b (a + p))
    (f : C(W, Z × AddCircle p))
    (hf : ∀ x, (f x).2 ∈ (interior (closedIntervalArc p a b))ᶜ) :
    ∃ H : f.HomotopyRel
        ⟨fun x => ((f x).1, (theta : AddCircle p)),
          f.continuous.fst.prodMk continuous_const⟩
        {x | (f x).2 = (theta : AddCircle p)},
      ∀ (t : unitInterval) (x : W),
        (H (t, x)).1 = (f x).1 ∧
        (H (t, x)).2 ∈ (interior (closedIntervalArc p a b))ᶜ ∧
        (H (t, x)).2 =
          (((1 - (t : ℝ)) * (openPartialHomeomorphCoe p ((a + b) / 2)).symm
              (f x).2 + (t : ℝ) * theta : ℝ) : AddCircle p) := by
  rw [compl_interior_closedIntervalArc p ha hab hb] at hf ⊢
  exact exists_shifted_closedArc_normal_contraction p
    (by linarith : (a + b) / 2 < b) (by linarith : a + p < (a + b) / 2 + p)
    htheta f hf

end AddCircle
