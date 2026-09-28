import PoincareConjecture.Proofs.M76.Mathlib.RadialBallQuotient
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.Order.OrderClosed

set_option autoImplicit false

open Set Metric unitInterval NormedSpace

namespace PoincareConjecture.M76

noncomputable def rimCollarThreshold (t : I) : ℝ := 1 - (t : ℝ) / 2

lemma rimCollarThreshold_pos (t : I) : 0 < rimCollarThreshold t := by
  have := t.property.2
  dsimp [rimCollarThreshold]
  linarith

noncomputable def rimCollarInnerRadius (t r : I) : I :=
  ⟨min 1 ((r : ℝ) / rimCollarThreshold t),
    le_min zero_le_one (div_nonneg r.property.1 (rimCollarThreshold_pos t).le),
    min_le_left _ _⟩

noncomputable def rimCollarDepth (t r : I) : I :=
  ⟨max 0 (min ((r : ℝ) - rimCollarThreshold t) (1 - (r : ℝ))),
    le_max_left _ _, max_le zero_le_one ((min_le_right _ _).trans (by linarith [r.property.1]))⟩

lemma continuous_rimCollarInnerRadius :
    Continuous (fun z : I × I => rimCollarInnerRadius z.1 z.2) := by
  apply Continuous.subtype_mk
  exact continuous_const.min
    ((continuous_subtype_val.comp continuous_snd).div
      (by unfold rimCollarThreshold; fun_prop)
      (fun z => ne_of_gt (rimCollarThreshold_pos z.1)))

lemma continuous_rimCollarDepth :
    Continuous (fun z : I × I => rimCollarDepth z.1 z.2) := by
  apply Continuous.subtype_mk
  unfold rimCollarThreshold
  fun_prop

theorem exists_radial_rim_insertion
    {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ProperSpace E] [Nontrivial E] [TopologicalSpace Y]
    (f : C(closedBall (0 : E) 1, Y))
    (c : C(sphere (0 : E) 1 × I, Y))
    (hc : ∀ u : sphere (0 : E) 1,
      c (u, 0) = f ⟨u, sphere_subset_closedBall u.property⟩) :
    ∃ H : C(I × closedBall (0 : E) 1, Y),
      (∀ x, H (0, x) = f x) ∧
      (∀ (t : I) (u : sphere (0 : E) 1),
        H (t, ⟨u, sphere_subset_closedBall u.property⟩) =
          f ⟨u, sphere_subset_closedBall u.property⟩) ∧
      ∀ (r : I) (u : sphere (0 : E) 1), (1 / 2 : ℝ) ≤ r →
        H (1, unitSphereRadialMap E (r, u)) = c (u, rimCollarDepth 1 r) := by
  classical
  let inner : C(I × (I × sphere (0 : E) 1), Y) :=
    ⟨fun z => f (unitSphereRadialMap E (rimCollarInnerRadius z.1 z.2.1, z.2.2)),
      f.continuous.comp ((unitSphereRadialMap E).continuous.comp
        ((continuous_rimCollarInnerRadius.comp
          (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).prodMk
            (continuous_snd.comp continuous_snd)))⟩
  let outer : C(I × (I × sphere (0 : E) 1), Y) :=
    ⟨fun z => c (z.2.2, rimCollarDepth z.1 z.2.1),
      c.continuous.comp ((continuous_snd.comp continuous_snd).prodMk
        (continuous_rimCollarDepth.comp
          (continuous_fst.prodMk (continuous_fst.comp continuous_snd))))⟩
  have hseam (z : I × (I × sphere (0 : E) 1))
      (hz : (z.2.1 : ℝ) = rimCollarThreshold z.1) : inner z = outer z := by
    have hi : rimCollarInnerRadius z.1 z.2.1 = 1 := by
      apply Subtype.ext
      simp [rimCollarInnerRadius, hz, ne_of_gt (rimCollarThreshold_pos z.1)]
    have ho : rimCollarDepth z.1 z.2.1 = 0 := by
      apply Subtype.ext
      simp [rimCollarDepth, hz]
    change f (unitSphereRadialMap E (rimCollarInnerRadius z.1 z.2.1, z.2.2)) =
      c (z.2.2, rimCollarDepth z.1 z.2.1)
    rw [hi, ho, hc]
    congr 1
    exact Subtype.ext (one_smul ℝ _)
  let T : C(I × (I × sphere (0 : E) 1), Y) :=
    ⟨fun z => if (z.2.1 : ℝ) ≤ rimCollarThreshold z.1 then inner z else outer z,
      continuous_if_le (by fun_prop) (by unfold rimCollarThreshold; fun_prop)
        inner.continuous.continuousOn outer.continuous.continuousOn hseam⟩
  let p : C(I × (I × sphere (0 : E) 1), I × closedBall (0 : E) 1) :=
    ⟨fun z => (z.1, unitSphereRadialMap E z.2),
      continuous_fst.prodMk ((unitSphereRadialMap E).continuous.comp continuous_snd)⟩
  have hp : Function.Surjective p := by
    rintro ⟨t, x⟩
    obtain ⟨z, hz⟩ := surjective_unitSphereRadialMap E x
    exact ⟨(t, z), Prod.ext rfl hz⟩
  have hpq : Topology.IsQuotientMap p :=
    Topology.IsQuotientMap.of_surjective_continuous hp p.continuous
  have hfactor : Function.FactorsThrough T p := by
    intro z w hzw
    have ht : z.1 = w.1 := congrArg (fun v : I × closedBall (0 : E) 1 => v.1) hzw
    have hr := (unitSphereRadialMap_eq_iff E z.2 w.2).mp (congrArg Prod.snd hzw)
    rcases hr with ⟨hr, hz | hu⟩
    · have hw : w.2.1 = 0 := hr.symm.trans hz
      have hzi : (z.2.1 : ℝ) ≤ rimCollarThreshold z.1 := by
        rw [hz]; exact (rimCollarThreshold_pos z.1).le
      have hwi : (w.2.1 : ℝ) ≤ rimCollarThreshold w.1 := by
        rw [hw]; exact (rimCollarThreshold_pos w.1).le
      change (if _ then inner z else outer z) = (if _ then inner w else outer w)
      rw [if_pos hzi, if_pos hwi]
      change f (unitSphereRadialMap E (rimCollarInnerRadius z.1 z.2.1, z.2.2)) =
        f (unitSphereRadialMap E (rimCollarInnerRadius w.1 w.2.1, w.2.2))
      congr 1
      apply Subtype.ext
      simp [unitSphereRadialMap, rimCollarInnerRadius, hz, hw]
    · exact congrArg T (Prod.ext ht (Prod.ext hr hu))
  let H := hpq.lift T hfactor
  have hH (t : I) (r : I) (u : sphere (0 : E) 1) :
      H (t, unitSphereRadialMap E (r, u)) = T (t, r, u) :=
    congrArg (fun k : C(I × (I × sphere (0 : E) 1), Y) => k (t, r, u))
      (hpq.lift_comp T hfactor)
  refine ⟨H, ?_, ?_, ?_⟩
  · intro x
    obtain ⟨⟨r, u⟩, rfl⟩ := surjective_unitSphereRadialMap E x
    rw [hH]
    have hi : rimCollarInnerRadius 0 r = r := by
      apply Subtype.ext
      simp [rimCollarInnerRadius, rimCollarThreshold, min_eq_right r.property.2]
    change (if _ then inner (0, r, u) else outer (0, r, u)) = _
    rw [if_pos (show (r : ℝ) ≤ rimCollarThreshold 0 by
      simpa [rimCollarThreshold] using r.property.2)]
    change f (unitSphereRadialMap E (rimCollarInnerRadius 0 r, u)) = _
    rw [hi]
  · intro t u
    have hu : unitSphereRadialMap E (1, u) =
        ⟨u, sphere_subset_closedBall u.property⟩ := Subtype.ext (one_smul ℝ _)
    rw [← hu, hH]
    have ho : rimCollarDepth t 1 = 0 := by
      apply Subtype.ext
      simp [rimCollarDepth, min_eq_right (by
        dsimp [rimCollarThreshold]; linarith [t.property.1] :
          (0 : ℝ) ≤ 1 - rimCollarThreshold t)]
    change (if _ then inner (t, 1, u) else outer (t, 1, u)) = _
    split_ifs with ht
    · have ht' : (1 : ℝ) = rimCollarThreshold t := by
        dsimp [rimCollarThreshold] at *
        linarith [t.property.1]
      rw [hseam (t, 1, u) ht']
      exact (congrArg (fun s => c (u, s)) ho).trans ((hc u).trans (congrArg f hu).symm)
    · exact (congrArg (fun s => c (u, s)) ho).trans ((hc u).trans (congrArg f hu).symm)
  · intro r u hr
    rw [hH]
    change (if _ then inner (1, r, u) else outer (1, r, u)) = _
    split_ifs with hri
    · exact hseam (1, r, u) (by
        dsimp [rimCollarThreshold] at *
        norm_num at hri ⊢
        linarith)
    · rfl

end PoincareConjecture.M76
