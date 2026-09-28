import PoincareConjecture.Proofs.M25.Topology3D.Plane.PolygonalParameter
import PoincareConjecture.Proofs.M25.Topology3D.Polygon.PolygonalArc
import Mathlib.Topology.Homeomorph.Lemmas

set_option autoImplicit false

open Set

namespace PoincareConjecture.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem polygonLinearParameter_natVertex {m : ℕ} [NeZero m]
    (p : Polygon E m) (i : Fin m) :
    polygonLinearParameter p (i.val : ℝ) = p i := by
  have ht : (i.val : ℝ) ∈ Icc ((i.val : ℤ) : ℝ) (((i.val : ℤ) : ℝ) + 1) := by
    simp only [Int.cast_natCast, mem_Icc]
    exact ⟨le_rfl, by linarith⟩
  rw [polygonLinearParameter_eq_edge p (i.val : ℤ) ht, polygonIntegerIndex_nat]
  simp only [Int.cast_natCast, sub_self, Polygon.edgePath, AffineMap.lineMap_apply_zero]

private theorem exists_open_arc_parameter_edge {n : ℕ} {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (n + 1 : ℕ)) :
    ∃ i : Fin (n + 1), t ∈ Icc (i.val : ℝ) ((i.val : ℝ) + 1) := by
  by_cases heq : t = (n + 1 : ℕ)
  · refine ⟨Fin.last n, ?_⟩
    rw [heq]
    simp only [Fin.val_last, Nat.cast_add, Nat.cast_one, mem_Icc]
    exact ⟨by linarith, le_rfl⟩
  · let j : ℤ := ⌊t⌋
    have hj0 : 0 ≤ j := Int.floor_nonneg.mpr ht.1
    have hjn : j < (n + 1 : ℕ) := by
      exact_mod_cast (Int.floor_le t).trans_lt (lt_of_le_of_ne ht.2 heq)
    let i : Fin (n + 1) := ⟨j.toNat, (Int.toNat_lt hj0).mpr hjn⟩
    have hval : (i.val : ℝ) = (j : ℝ) := by
      dsimp only [i]
      exact_mod_cast Int.toNat_of_nonneg hj0
    refine ⟨i, ?_⟩
    rw [hval]
    exact ⟨Int.floor_le t, (Int.lt_floor_add_one t).le⟩

private theorem open_arc_parameter_eq_edge {n : ℕ} (p : Polygon E (n + 2))
    (i : Fin (n + 1)) {t : ℝ} (ht : t ∈ Icc (i.val : ℝ) ((i.val : ℝ) + 1)) :
    polygonLinearParameter p t = p.edgePath ℝ i.castSucc (t - i.val) := by
  have hi : polygonIntegerIndex (n + 2) (i.val : ℤ) = i.castSucc :=
    polygonIntegerIndex_nat i.castSucc
  simpa only [hi, Int.cast_natCast] using
    polygonLinearParameter_eq_edge p (i.val : ℤ) (by simpa only [Int.cast_natCast] using ht)

private theorem continuous_open_arc_parameter {n : ℕ} (p : Polygon E (n + 2)) :
    Continuous (polygonLinearParameter p) := by
  have h : Continuous (fun x : Unit × ℝ => polygonLinearParameter p x.2) :=
    continuous_polygonLinearParameter (p := fun _ : Unit => p) (fun _ => continuous_const)
  exact h.comp (show Continuous (fun t : ℝ => ((), t)) from
    continuous_const.prodMk continuous_id)

theorem image_polygonLinearParameter_arc {n : ℕ} (p : Polygon E (n + 2)) :
    polygonLinearParameter p '' Icc (0 : ℝ) (n + 1 : ℕ) = polygonArcBoundary p := by
  apply subset_antisymm
  · rintro _ ⟨t, ht, rfl⟩
    obtain ⟨i, hi⟩ := exists_open_arc_parameter_edge ht
    apply polygon_arcEdge_subset_boundary p i
    refine ⟨t - i.val, ⟨by linarith [hi.1], by linarith [hi.2]⟩, ?_⟩
    exact (open_arc_parameter_eq_edge p i hi).symm
  · intro x hx
    obtain ⟨i, θ, hθ, rfl⟩ := mem_iUnion.mp hx
    have ht : (i.val : ℝ) + θ ∈ Icc (0 : ℝ) (n + 1 : ℕ) := by
      have hi : (i.val : ℝ) + 1 ≤ (n + 1 : ℕ) := by exact_mod_cast i.isLt
      constructor
      · exact add_nonneg (Nat.cast_nonneg _) hθ.1
      · linarith [hθ.2]
    refine ⟨(i.val : ℝ) + θ, ht, ?_⟩
    rw [open_arc_parameter_eq_edge p i (by constructor <;> linarith [hθ.1, hθ.2])]
    congr 1
    ring

theorem IsSimplePolygonalArc.injOn_polygonLinearParameter {n : ℕ}
    {p : Polygon E (n + 2)} (hp : IsSimplePolygonalArc p) :
    InjOn (polygonLinearParameter p) (Icc (0 : ℝ) (n + 1 : ℕ)) := by
  intro s hs t ht heq
  obtain ⟨i, hi⟩ := exists_open_arc_parameter_edge hs
  obtain ⟨j, hj⟩ := exists_open_arc_parameter_edge ht
  rw [open_arc_parameter_eq_edge p i hi, open_arc_parameter_eq_edge p j hj] at heq
  by_cases hij : i = j
  · subst j
    have hab := hp.edgePath_injective i heq
    linarith
  · have hends := hp.edges_inter i j hij
      ⟨⟨s - i.val, ⟨by linarith [hi.1], by linarith [hi.2]⟩, rfl⟩,
        ⟨t - j.val, ⟨by linarith [hj.1], by linarith [hj.2]⟩, heq.symm⟩⟩
    have hendpoint (l : Fin (n + 1)) (u : ℝ) (v : E)
        (hu : p.edgePath ℝ l.castSucc (u - l.val) = v)
        (hv : v ∈ ({p l.castSucc, p l.succ} : Set E)) :
        ∃ k : Fin (n + 2), v = p k ∧ u = (k.val : ℝ) := by
      have hnext : finRotate (n + 2) l.castSucc = l.succ := finRotate_of_lt l.isLt
      rcases hv with hv | hv
      · have hparam : u - l.val = 0 := hp.edgePath_injective l (by
          simpa only [Polygon.edgePath, AffineMap.lineMap_apply_zero] using hu.trans hv)
        exact ⟨l.castSucc, hv, by simpa only [Fin.val_castSucc] using sub_eq_zero.mp hparam⟩
      · have hparam : u - l.val = 1 := hp.edgePath_injective l (by
          simpa only [Polygon.edgePath, AffineMap.lineMap_apply_one, hnext] using hu.trans hv)
        refine ⟨l.succ, hv, ?_⟩
        simp only [Fin.val_succ, Nat.cast_add, Nat.cast_one]
        linarith
    obtain ⟨a, ha, hsa⟩ := hendpoint i s _ rfl hends.1
    obtain ⟨b, hb, htb⟩ := hendpoint j t _ heq.symm hends.2
    have hab := hp.vertices_injective (ha.symm.trans hb)
    rw [hsa, htb, hab]

noncomputable def IsSimplePolygonalArc.polygonArcHomeomorph {n : ℕ}
    {p : Polygon E (n + 2)} (hp : IsSimplePolygonalArc p) :
    Icc (0 : ℝ) (n + 1 : ℕ) ≃ₜ polygonArcBoundary p := by
  let F : Icc (0 : ℝ) (n + 1 : ℕ) → polygonArcBoundary p := fun t =>
    ⟨polygonLinearParameter p t, (image_polygonLinearParameter_arc p) ▸
      mem_image_of_mem (polygonLinearParameter p) t.property⟩
  have hbij : Function.Bijective F := by
    constructor
    · intro s t h
      exact Subtype.ext (hp.injOn_polygonLinearParameter s.property t.property
        (congrArg Subtype.val h))
    · intro x
      have hx : (x : E) ∈ polygonLinearParameter p '' Icc (0 : ℝ) (n + 1 : ℕ) := by
        rw [image_polygonLinearParameter_arc]
        exact x.property
      obtain ⟨t, ht, htx⟩ := hx
      exact ⟨⟨t, ht⟩, Subtype.ext htx⟩
  let e := Equiv.ofBijective F hbij
  have he : Continuous e :=
    ((continuous_open_arc_parameter p).comp continuous_subtype_val).subtype_mk _
  exact he.homeoOfEquivCompactToT2

theorem IsSimplePolygonalArc.polygonArcHomeomorph_apply {n : ℕ}
    {p : Polygon E (n + 2)} (hp : IsSimplePolygonalArc p)
    (t : Icc (0 : ℝ) (n + 1 : ℕ)) :
    (hp.polygonArcHomeomorph t : E) = polygonLinearParameter p t := rfl

theorem polygon_arcBoundary_isPathConnected {n : ℕ} (p : Polygon E (n + 2)) :
    IsPathConnected (polygonArcBoundary p) := by
  rw [← image_polygonLinearParameter_arc]
  apply ((convex_Icc (0 : ℝ) (n + 1 : ℕ)).isPathConnected ?_).image
    (continuous_open_arc_parameter p)
  exact ⟨0, le_rfl, Nat.cast_nonneg _⟩

end PoincareConjecture.M25.Topology3D
