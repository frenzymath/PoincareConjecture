import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Homotopy.Affine
import Mathlib.Topology.UnitInterval










set_option autoImplicit false

open Set Metric Topology
open scoped unitInterval

namespace Poincare.Topology


theorem exists_closedBall_cylinder_retraction
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    ∃ r : C(unitInterval × closedBall (0 : E) 1, unitInterval × closedBall (0 : E) 1),
      (∀ z, (r z).1 = 0 ∨ ‖((r z).2 : E)‖ = 1) ∧
      ∀ z, z.1 = 0 ∨ ‖(z.2 : E)‖ = 1 → r z = z := by
  let D := unitInterval × closedBall (0 : E) 1
  let d : D → ℝ := fun z => max ‖(z.2 : E)‖ (1 - (z.1 : ℝ) / 2)
  have hdpos (z : D) : 0 < d z := by
    have ht := z.1.property.2
    have hle := le_max_right ‖(z.2 : E)‖ (1 - (z.1 : ℝ) / 2)
    dsimp [d]
    linarith
  have hdle (z : D) : d z ≤ 1 := by
    apply max_le
    · simpa only [mem_closedBall, dist_zero_right] using z.2.property
    · linarith [z.1.property.1]
  have hdnorm (z : D) : ‖(z.2 : E)‖ ≤ d z := le_max_left _ _
  have hdtime (z : D) : 1 - (z.1 : ℝ) / 2 ≤ d z := le_max_right _ _
  have hdcont : Continuous d := by
    change Continuous (fun z : unitInterval × closedBall (0 : E) 1 =>
      max ‖(z.2 : E)‖ (1 - (z.1 : ℝ) / 2))
    fun_prop
  let u : D → E := fun z => (d z)⁻¹ • (z.2 : E)
  let s : D → ℝ := fun z => (2 * d z + (z.1 : ℝ) - 2) / d z
  have hunorm (z : D) : ‖u z‖ = ‖(z.2 : E)‖ / d z := by
    simp only [u, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hdpos z)),
      div_eq_mul_inv]
    ring
  have hu (z : D) : u z ∈ closedBall (0 : E) 1 := by
    rw [mem_closedBall, dist_zero_right, hunorm]
    exact (div_le_iff₀ (hdpos z)).mpr (by simpa using hdnorm z)
  have hs (z : D) : s z ∈ Icc (0 : ℝ) 1 := by
    constructor
    · apply div_nonneg _ (hdpos z).le
      linarith [hdtime z]
    · apply (div_le_iff₀ (hdpos z)).mpr
      linarith [hdle z, z.1.property.2]
  have hucont : Continuous u := by
    exact (hdcont.inv₀ (fun z => (hdpos z).ne')).smul
      (continuous_subtype_val.comp continuous_snd)
  have hscont : Continuous s := by
    exact (((continuous_const.mul hdcont).add continuous_fst.subtype_val).sub
      continuous_const).div hdcont (fun z => (hdpos z).ne')
  let r : C(D, D) :=
    ⟨fun z => (⟨s z, hs z⟩, ⟨u z, hu z⟩),
      (hscont.subtype_mk hs).prodMk (hucont.subtype_mk hu)⟩
  refine ⟨r, ?_, ?_⟩
  · intro z
    by_cases hz : ‖(z.2 : E)‖ ≤ 1 - (z.1 : ℝ) / 2
    · left
      apply Subtype.ext
      change s z = 0
      have hdz : d z = 1 - (z.1 : ℝ) / 2 := max_eq_right hz
      dsimp [s]
      rw [hdz]
      have hnum : 2 * (1 - (z.1 : ℝ) / 2) + (z.1 : ℝ) - 2 = 0 := by ring
      rw [hnum, zero_div]
    · right
      change ‖u z‖ = 1
      rw [hunorm]
      have hdz : d z = ‖(z.2 : E)‖ := max_eq_left (le_of_not_ge hz)
      have hn : 0 < ‖(z.2 : E)‖ := hdz ▸ hdpos z
      rw [hdz, div_self hn.ne']
  · intro z hz
    have hdz : d z = 1 := by
      rcases hz with ht | hn
      · have ht' : (z.1 : ℝ) = 0 := congrArg Subtype.val ht
        dsimp [d]
        rw [ht']
        simpa only [zero_div, sub_zero] using
          (max_eq_right (show ‖(z.2 : E)‖ ≤ 1 from
            by simpa only [mem_closedBall, dist_zero_right] using z.2.property))
      · dsimp [d]
        rw [hn]
        exact max_eq_left (by linarith [z.1.property.1])
    apply Prod.ext
    · apply Subtype.ext
      change s z = (z.1 : ℝ)
      dsimp [s]
      rw [hdz]
      ring
    · apply Subtype.ext
      change u z = (z.2 : E)
      simp only [u, hdz, inv_one, one_smul]


theorem exists_closedBall_homotopy_extension
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace X]
    (f : C(closedBall (0 : E) 1, X)) (h : C(unitInterval × sphere (0 : E) 1, X))
    (hh : ∀ x : sphere (0 : E) 1,
      h (0, x) = f ⟨x, sphere_subset_closedBall x.property⟩) :
    ∃ F : C(unitInterval × closedBall (0 : E) 1, X),
      (∀ x, F (0, x) = f x) ∧
      ∀ t (x : sphere (0 : E) 1), F (t, ⟨x, sphere_subset_closedBall x.property⟩) = h (t, x) := by
  classical
  let A : Set (unitInterval × closedBall (0 : E) 1) :=
    {z | z.1 = 0 ∨ ‖(z.2 : E)‖ = 1}
  let B : Set A := {z | z.1.1 = 0}
  let S : Set A := {z | ‖(z.1.2 : E)‖ = 1}
  let g : A → X := fun z =>
    if ht : z.1.1 = 0 then f z.1.2
    else h (z.1.1, ⟨z.1.2, mem_sphere_zero_iff_norm.mpr (z.property.resolve_left ht)⟩)
  have hgB (z : A) (hz : z ∈ B) : g z = f z.1.2 := by
    change z.1.1 = 0 at hz
    dsimp [g]
    rw [dif_pos hz]
  have hgS (z : A) (hz : z ∈ S) :
      g z = h (z.1.1, ⟨z.1.2, mem_sphere_zero_iff_norm.mpr hz⟩) := by
    dsimp [g]
    split_ifs with ht
    · simpa only [ht] using (hh ⟨z.1.2, mem_sphere_zero_iff_norm.mpr hz⟩).symm
    · rfl
  have hBclosed : IsClosed B := by
    change IsClosed {z : A | z.1.1 = 0}
    have hc : Continuous (fun z : A => z.1.1) := by fun_prop
    exact isClosed_eq hc continuous_const
  have hSclosed : IsClosed S := by
    change IsClosed {z : A | ‖(z.1.2 : E)‖ = 1}
    have hc : Continuous (fun z : A => ‖(z.1.2 : E)‖) := by fun_prop
    exact isClosed_singleton.preimage hc
  have hBS : B ∪ S = univ := by
    ext z
    simp only [mem_union, mem_univ, iff_true]
    exact z.property
  have hcontB : ContinuousOn g B := by
    apply (f.continuous.comp (continuous_snd.comp continuous_subtype_val)).continuousOn.congr
    exact hgB
  have hcontS : ContinuousOn g S := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    let k : S → unitInterval × sphere (0 : E) 1 := fun z =>
      (z.1.1.1, ⟨z.1.1.2, mem_sphere_zero_iff_norm.mpr z.property⟩)
    have hk : Continuous k := by
      have ht : Continuous (fun z : S => z.1.1.1) := by fun_prop
      have hv : Continuous (fun z : S => (z.1.1.2 : E)) := by fun_prop
      exact ht.prodMk (hv.subtype_mk _)
    convert h.continuous.comp hk using 1
    funext z
    exact hgS z.1 z.property
  have hgcont : Continuous g := by
    apply continuousOn_univ.mp
    rw [← hBS]
    exact hcontB.union_of_isClosed hcontS hBclosed hSclosed
  obtain ⟨r, hrA, hrfix⟩ := exists_closedBall_cylinder_retraction (E := E)
  let rA : C(unitInterval × closedBall (0 : E) 1, A) :=
    ⟨fun z => ⟨r z, hrA z⟩, r.continuous.subtype_mk hrA⟩
  refine ⟨(⟨g, hgcont⟩ : C(A, X)).comp rA, ?_, ?_⟩
  · intro x
    change g ⟨r (0, x), hrA (0, x)⟩ = f x
    have hr0 := hrfix (0, x) (Or.inl rfl)
    have hgb := hgB ⟨r (0, x), hrA (0, x)⟩ (by change (r (0, x)).1 = 0; rw [hr0])
    simpa only [hr0] using hgb
  · intro t x
    let xb : closedBall (0 : E) 1 := ⟨x, sphere_subset_closedBall x.property⟩
    change g ⟨r (t, xb), hrA (t, xb)⟩ = h (t, x)
    have hrx := hrfix (t, xb) (Or.inr (mem_sphere_zero_iff_norm.mp x.property))
    have hgs := hgS ⟨r (t, xb), hrA (t, xb)⟩ (by
      change ‖((r (t, xb)).2 : E)‖ = 1
      rw [hrx]
      exact mem_sphere_zero_iff_norm.mp x.property)
    simpa only [hrx] using hgs


theorem sphere_nullhomotopic_iff_extends_closedBall
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace X]
    (p : C(sphere (0 : E) 1, X)) :
    p.Nullhomotopic ↔ ∃ F : C(closedBall (0 : E) 1, X),
      ∀ x : sphere (0 : E) 1, F ⟨x, sphere_subset_closedBall x.property⟩ = p x := by
  constructor
  · rintro ⟨x, ⟨H⟩⟩
    obtain ⟨F, _, hFS⟩ := exists_closedBall_homotopy_extension
      (ContinuousMap.const _ x) H.symm.toContinuousMap (fun z => H.symm.apply_zero z)
    refine ⟨F.comp ⟨fun z => (1, z), continuous_const.prodMk continuous_id⟩, ?_⟩
    intro z
    exact (hFS 1 z).trans (H.symm.apply_one z)
  · rintro ⟨F, hF⟩
    let := contractibleSpace_closedBall (x := (0 : E)) (r := 1) zero_le_one
    let i : C(sphere (0 : E) 1, closedBall (0 : E) 1) :=
      ⟨fun z => ⟨z, sphere_subset_closedBall z.property⟩,
        continuous_subtype_val.subtype_mk _⟩
    have hN := ((id_nullhomotopic (closedBall (0 : E) 1)).comp_right F).comp_left i
    have hp : (F.comp (ContinuousMap.id _)).comp i = p := by
      ext z
      exact hF z
    rwa [hp] at hN


theorem exists_closedBall_cylinder_deformation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    ∃ r : C(unitInterval × closedBall (0 : E) 1, unitInterval × closedBall (0 : E) 1),
      (∀ z, (r z).1 = 0 ∨ ‖((r z).2 : E)‖ = 1) ∧
      (ContinuousMap.id _).HomotopicRel r {z | z.1 = 0 ∨ ‖(z.2 : E)‖ = 1} := by
  let D := unitInterval × closedBall (0 : E) 1
  let B : Set (ℝ × E) := Icc (0 : ℝ) 1 ×ˢ closedBall (0 : E) 1
  let a : C(unitInterval × closedBall (0 : E) 1, ℝ × E) :=
    ⟨fun z => ((z.1 : ℝ), (z.2 : E)), by fun_prop⟩
  have ha (z : D) : a z ∈ B := ⟨z.1.property, z.2.property⟩
  have hB : Convex ℝ B := Convex.prod (convex_Icc _ _) (convex_closedBall _ _)
  obtain ⟨r, hrA, hrfix⟩ := exists_closedBall_cylinder_retraction (E := E)
  let H := ContinuousMap.Homotopy.affine a (a.comp r)
  have hH (t : unitInterval × D) : H t ∈ B :=
    hB.lineMap_mem (ha t.2) (ha (r t.2)) t.1.property
  refine ⟨r, hrA, ⟨{
    toHomotopy := {
      toFun := fun t => (⟨(H t).1, (hH t).1⟩, ⟨(H t).2, (hH t).2⟩)
      continuous_toFun :=
        ((map_continuous H).fst.subtype_mk (fun t => (hH t).1)).prodMk
          ((map_continuous H).snd.subtype_mk (fun t => (hH t).2))
      map_zero_left := ?_
      map_one_left := ?_
    }
    prop' := ?_
  }⟩⟩
  · intro z
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst (H.apply_zero z)
    · apply Subtype.ext
      exact congrArg Prod.snd (H.apply_zero z)
  · intro z
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst (H.apply_one z)
    · apply Subtype.ext
      exact congrArg Prod.snd (H.apply_one z)
  · intro t z hz
    have hHz : H (t, z) = a z := by
      change AffineMap.lineMap (a z) (a (r z)) (t : ℝ) = a z
      rw [hrfix z hz, AffineMap.lineMap_same_apply]
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst hHz
    · apply Subtype.ext
      exact congrArg Prod.snd hHz

end Poincare.Topology
