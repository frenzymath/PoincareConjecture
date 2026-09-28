import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Regions.ProtectedCollaredPolygonFilling
import PoincareConjecture.Proofs.M76.Mathlib.RadialBallQuotient
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.Connected.Clopen










set_option autoImplicit false

open Set Metric unitInterval NormedSpace

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Q" => sphere (0 : V2) 1
local notation "D" => closedBall (0 : V2) 1

private noncomputable def clipUnit (r : ℝ) : I := projIcc 0 1 zero_le_one r

private theorem continuous_clipUnit : Continuous clipUnit := continuous_projIcc (h := zero_le_one)

private theorem clipUnit_eq {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    clipUnit r = ⟨r, hr⟩ := projIcc_of_mem zero_le_one hr

private theorem clipUnit_zero : clipUnit 0 = 0 := by
  exact Subtype.ext (congrArg Subtype.val (clipUnit_eq ⟨le_rfl, zero_le_one⟩))

private theorem clipUnit_one : clipUnit 1 = 1 := by
  exact Subtype.ext (congrArg Subtype.val (clipUnit_eq ⟨zero_le_one, le_rfl⟩))




theorem exists_radial_two_annulus_filling
    {X : Type*} [TopologicalSpace X] {N Y F : Set X}
    (gamma : C(Q, F)) (g : C(D, Y)) (A B : C(I × Q, Y))
    (hA0 : ∀ u : Q, (A (0, u) : X) = (gamma u : X))
    (hAB : ∀ u : Q, A (1, u) = B (0, u))
    (hB1 : ∀ u : Q, B (1, u) = g ⟨u, sphere_subset_closedBall u.property⟩)
    (hg : ∀ x : D, (g x : X) ∈ interior N)
    (hA : ∀ (t : I) (u : Q), 0 < (t : ℝ) → (A (t, u) : X) ∈ interior N)
    (hB : ∀ (t : I) (u : Q), (B (t, u) : X) ∈ interior N) :
    ∃ f : C(D, Y),
      (∀ u : Q, (f ⟨u, sphere_subset_closedBall u.property⟩ : X) = (gamma u : X)) ∧
      (∀ x : D, (x : V2) ∈ interior D → (f x : X) ∈ interior N) ∧
      (∀ (r : I) (u : Q), (r : ℝ) ≤ 1 / 3 →
        f (unitSphereRadialMap V2 (r, u)) =
          g (unitSphereRadialMap V2 (clipUnit (3 * (r : ℝ)), u))) ∧
      (∀ (r : I) (u : Q), 1 / 3 < (r : ℝ) → (r : ℝ) ≤ 2 / 3 →
        f (unitSphereRadialMap V2 (r, u)) = B (clipUnit (2 - 3 * (r : ℝ)), u)) ∧
      ∀ (r : I) (u : Q), 2 / 3 < (r : ℝ) →
        f (unitSphereRadialMap V2 (r, u)) = A (clipUnit (3 - 3 * (r : ℝ)), u) := by
  classical
  let inner : C(I × Q, Y) := g.comp ((unitSphereRadialMap V2).comp
    ⟨fun z => (clipUnit (3 * (z.1 : ℝ)), z.2), by
      exact (continuous_clipUnit.comp (by fun_prop)).prodMk continuous_snd⟩)
  let mid : C(I × Q, Y) := B.comp
    ⟨fun z => (clipUnit (2 - 3 * (z.1 : ℝ)), z.2), by
      exact (continuous_clipUnit.comp (by fun_prop)).prodMk continuous_snd⟩
  let outer : C(I × Q, Y) := A.comp
    ⟨fun z => (clipUnit (3 - 3 * (z.1 : ℝ)), z.2), by
      exact (continuous_clipUnit.comp (by fun_prop)).prodMk continuous_snd⟩
  have hmid (z : I × Q) (hz : (z.1 : ℝ) = 2 / 3) : mid z = outer z := by
    change B (clipUnit (2 - 3 * (z.1 : ℝ)), z.2) =
      A (clipUnit (3 - 3 * (z.1 : ℝ)), z.2)
    rw [hz]
    norm_num only at *
    simpa only [clipUnit_zero, clipUnit_one] using (hAB z.2).symm
  let ann : C(I × Q, Y) := ⟨fun z =>
    if (z.1 : ℝ) ≤ 2 / 3 then mid z else outer z,
    mid.continuous.if_le outer.continuous (by fun_prop) continuous_const hmid⟩
  have hinner (z : I × Q) (hz : (z.1 : ℝ) = 1 / 3) : inner z = ann z := by
    have hzle : (z.1 : ℝ) ≤ 2 / 3 := by rw [hz]; norm_num
    change g (unitSphereRadialMap V2 (clipUnit (3 * (z.1 : ℝ)), z.2)) =
      if (z.1 : ℝ) ≤ 2 / 3 then mid z else outer z
    rw [if_pos hzle]
    change g (unitSphereRadialMap V2 (clipUnit (3 * (z.1 : ℝ)), z.2)) =
      B (clipUnit (2 - 3 * (z.1 : ℝ)), z.2)
    rw [hz]
    norm_num only
    rw [clipUnit_one]
    simpa [unitSphereRadialMap] using (hB1 z.2).symm
  let radial : C(I × Q, Y) := ⟨fun z =>
    if (z.1 : ℝ) ≤ 1 / 3 then inner z else ann z,
    inner.continuous.if_le ann.continuous (by fun_prop) continuous_const hinner⟩
  have hfactor : Function.FactorsThrough radial (unitSphereRadialMap V2) := by
    intro z w hzw
    obtain ⟨hr, hz | hu⟩ := (unitSphereRadialMap_eq_iff V2 z w).mp hzw
    · have hw : w.1 = 0 := hr ▸ hz
      change (if (z.1 : ℝ) ≤ 1 / 3 then inner z else ann z) =
        if (w.1 : ℝ) ≤ 1 / 3 then inner w else ann w
      rw [if_pos (by rw [hz]; norm_num), if_pos (by rw [hw]; norm_num)]
      change g (unitSphereRadialMap V2 (clipUnit (3 * (z.1 : ℝ)), z.2)) =
        g (unitSphereRadialMap V2 (clipUnit (3 * (w.1 : ℝ)), w.2))
      simp [hz, hw, clipUnit_zero, unitSphereRadialMap]
    · exact congrArg radial (Prod.ext hr hu)
  let f := (isQuotientMap_unitSphereRadialMap V2).lift radial hfactor
  have hf (z : I × Q) : f (unitSphereRadialMap V2 z) = radial z :=
    congrArg (fun k : C(I × Q, Y) => k z)
      ((isQuotientMap_unitSphereRadialMap V2).lift_comp radial hfactor)
  have hcentral (r : I) (u : Q) (hr : (r : ℝ) ≤ 1 / 3) :
      f (unitSphereRadialMap V2 (r, u)) =
        g (unitSphereRadialMap V2 (clipUnit (3 * (r : ℝ)), u)) := by
    rw [hf]
    exact if_pos hr
  have hmiddle (r : I) (u : Q) (hr : 1 / 3 < (r : ℝ)) (hr' : (r : ℝ) ≤ 2 / 3) :
      f (unitSphereRadialMap V2 (r, u)) = B (clipUnit (2 - 3 * (r : ℝ)), u) := by
    rw [hf]
    change (if (r : ℝ) ≤ 1 / 3 then _ else if (r : ℝ) ≤ 2 / 3 then _ else _) = _
    rw [if_neg (not_le.mpr hr), if_pos hr']
    rfl
  have houter (r : I) (u : Q) (hr : 2 / 3 < (r : ℝ)) :
      f (unitSphereRadialMap V2 (r, u)) = A (clipUnit (3 - 3 * (r : ℝ)), u) := by
    rw [hf]
    change (if (r : ℝ) ≤ 1 / 3 then _ else if (r : ℝ) ≤ 2 / 3 then _ else _) = _
    rw [if_neg (by linarith), if_neg (not_le.mpr hr)]
    rfl
  refine ⟨f, ?_, ?_, hcentral, hmiddle, houter⟩
  · intro u
    have hu : unitSphereRadialMap V2 (1, u) = ⟨u, sphere_subset_closedBall u.property⟩ :=
      Subtype.ext (one_smul ℝ (u : V2))
    rw [← hu, houter 1 u (by norm_num)]
    simpa [clipUnit_zero] using hA0 u
  · intro x hx
    obtain ⟨⟨r, u⟩, rfl⟩ := surjective_unitSphereRadialMap V2 x
    have hr : (r : ℝ) < 1 := by
      rw [interior_closedBall _ one_ne_zero, mem_ball, dist_zero_right,
        norm_unitSphereRadialMap] at hx
      exact hx
    by_cases hri : (r : ℝ) ≤ 1 / 3
    · rw [hcentral r u hri]
      exact hg _
    · by_cases hrm : (r : ℝ) ≤ 2 / 3
      · rw [hmiddle r u (lt_of_not_ge hri) hrm]
        exact hB _ _
      · rw [houter r u (lt_of_not_ge hrm)]
        apply hA
        have ht : 3 - 3 * (r : ℝ) ∈ Icc (0 : ℝ) 1 := by
          constructor <;> linarith
        rw [clipUnit_eq ht]
        change 0 < 3 - 3 * (r : ℝ)
        linarith

theorem PLDomain.exists_proper_filling_of_empty_frontier_preimage
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {N Y F : Set X}
    (hN : PLDomain e N) (hcut : Y ∩ frontier N = F)
    (gamma : C(Q, F)) (g : C(D, Y)) (A B : C(I × Q, Y))
    (hA0 : ∀ u : Q, (A (0, u) : X) = (gamma u : X))
    (hAB : ∀ u : Q, A (1, u) = B (0, u))
    (hB1 : ∀ u : Q, B (1, u) = g ⟨u, sphere_subset_closedBall u.property⟩)
    (havoid : ∀ z : D, (g z : X) ∉ F)
    (hA : ∀ (t : I) (u : Q), 0 < (t : ℝ) → (A (t, u) : X) ∈ interior N)
    (hB : ∀ (t : I) (u : Q), (B (t, u) : X) ∈ interior N) :
    ∃ f : C(D, Y),
      (∀ u : Q, (f ⟨u, sphere_subset_closedBall u.property⟩ : X) = (gamma u : X)) ∧
      (∀ z : D, (f z : X) ∈ N) ∧
      (∀ z : D, (z : V2) ∈ interior D → (f z : X) ∈ interior N) ∧
      ∀ z : D, (f z : X) ∈ F ↔ (z : V2) ∈ Q := by
  let : PreconnectedSpace D :=
    Subtype.preconnectedSpace (convex_closedBall (0 : V2) 1).isPreconnected
  have hconn : IsPreconnected (range (fun z : D => (g z : X))) :=
    isPreconnected_range (continuous_subtype_val.comp g.continuous)
  have hcover : range (fun z : D => (g z : X)) ⊆ interior N ∪ Nᶜ := by
    rintro _ ⟨z, rfl⟩
    by_cases hz : (g z : X) ∈ N
    · exact Or.inl ((mem_interior_iff_notMem_frontier hz).mpr
        (fun h => havoid z (hcut ▸ ⟨(g z).property, h⟩)))
    · exact Or.inr hz
  have hdisjoint : Disjoint (interior N) Nᶜ :=
    Set.disjoint_left.mpr (fun _ hi hc => hc (interior_subset hi))
  have hg : ∀ z : D, (g z : X) ∈ interior N := by
    rcases hconn.subset_or_subset isOpen_interior hN.closed.isOpen_compl
        hdisjoint hcover with hi | hc
    · exact fun z => hi (mem_range_self z)
    · let u : Q := Dehn.squareRimBase
      have hin := hB 1 u
      rw [hB1 u] at hin
      exact False.elim (hc (mem_range_self _) (interior_subset hin))
  obtain ⟨f, hf, hfi, _⟩ := exists_radial_two_annulus_filling gamma g A B
    hA0 hAB hB1 hg hA hB
  have hnotrim {z : D} (hz : (z : V2) ∉ Q) : (z : V2) ∈ interior D := by
    rw [interior_closedBall _ one_ne_zero]
    exact lt_of_le_of_ne z.property hz
  have hrim {z : D} (hz : (z : V2) ∈ Q) : (f z : X) ∈ F := by
    rw [hf ⟨z, hz⟩]
    exact (gamma ⟨z, hz⟩).property
  refine ⟨f, hf, ?_, hfi, ?_⟩
  · intro z
    by_cases hz : (z : V2) ∈ Q
    · exact hN.closed.frontier_subset ((hcut.symm ▸ hrim hz).2)
    · exact interior_subset (hfi z (hnotrim hz))
  · intro z
    refine ⟨?_, hrim⟩
    intro hzF
    by_contra hz
    exact Set.disjoint_left.mp disjoint_interior_frontier (hfi z (hnotrim hz))
      ((hcut.symm ▸ hzF).2)

end PoincareConjecture.M76
