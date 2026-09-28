import PoincareConjecture.Proofs.M76.Horizon.Polyhedral.Maps.ConvexBoundaryConeMap
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.UnitInterval










set_option autoImplicit false

open Set Geometry NormedSpace unitInterval
open scoped Topology

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E] [Nontrivial E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]




theorem AffineOnFaces.exists_convex_boundary_cone_homotopy
    {K : SimplicialComplex ℝ E} {b : E → F} (hb : K.AffineOnFaces b)
    (hK : K.faces.Finite) {S : Set E} (hS : IsCompact S) (hScv : Convex ℝ S)
    (hS0 : (0 : E) ∈ interior S) (hKS : K.space = frontier S)
    {W : Set F} (hW : Convex ℝ W) (f : E →ᴬ[ℝ] F) (hfW : MapsTo f S W)
    (B : C(I × frontier S, W))
    (hB0 : ∀ u : frontier S, (B (0, u) : F) = f u)
    (hB1 : ∀ u : frontier S, (B (1, u) : F) = b u)
    (a : F) (ha : a ∈ W) :
    ∃ (hlin : ∀ s ∈ K.faces, LinearIndependent ℝ ((↑) : s → E))
      (hrad : InjOn (normalize : E → E) K.space) (g : E → F)
      (H : C(I × S, W)),
      (K.coneAtZero hlin hrad).space = S ∧
      (K.coneAtZero hlin hrad).AffineOnFaces g ∧
      FinitePiecewiseAffineOn g S ∧ g 0 = a ∧ EqOn g b (frontier S) ∧
      MapsTo g S W ∧
      (∀ u ∈ frontier S, ∀ r ∈ Icc (0 : ℝ) 1,
        g (r • u) = (1 - r) • a + r • b u) ∧
      (∀ x : S, (H (0, x) : F) = f x) ∧
      (∀ x : S, (H (1, x) : F) = g x) ∧
      ∀ (t : I) (u : frontier S),
        H (t, ⟨u, hS.isClosed.frontier_subset u.property⟩) = B (t, u) := by
  have hbW : MapsTo b (frontier S) W := by
    intro u hu
    rw [← hB1 ⟨u, hu⟩]
    exact (B (1, ⟨u, hu⟩)).property
  obtain ⟨hlin, hrad, g, hCS, hg, hgPL, hg0, hgb, hgW, hgray⟩ :=
    hb.exists_convex_boundary_cone hK hS hScv hS0 hKS hW hbW a ha
  have hfrontne : (frontier S).Nonempty :=
    nonempty_frontier_iff.mpr ⟨⟨0, interior_subset hS0⟩, hS.ne_univ⟩
  let : CompactSpace (frontier S) :=
    isCompact_iff_compactSpace.mp (hS.of_isClosed_subset isClosed_frontier hS.isClosed.frontier_subset)
  let radial : C(I × frontier S, S) :=
    ⟨fun z => ⟨(z.1 : ℝ) • (z.2 : E), by
      have h := hScv (interior_subset hS0) (hS.isClosed.frontier_subset z.2.property)
        (sub_nonneg.mpr z.1.property.2) z.1.property.1 (sub_add_cancel 1 (z.1 : ℝ))
      simpa only [smul_zero, zero_add] using h⟩,
      by fun_prop⟩
  have hradial : Function.Surjective radial := by
    intro x
    by_cases hx : (x : E) = 0
    · obtain ⟨u, hu⟩ := hfrontne
      exact ⟨(0, ⟨u, hu⟩), Subtype.ext (by simpa [radial] using hx.symm)⟩
    · obtain ⟨u, hu, r, hr, hxr⟩ := hS.exists_frontier_pos_smul hScv hS0 x.property hx
      exact ⟨(⟨r, hr.1.le, hr.2⟩, ⟨u, hu⟩), Subtype.ext hxr.symm⟩
  let p : C(I × (I × frontier S), I × S) :=
    ⟨fun z => (z.1, radial z.2), continuous_fst.prodMk (radial.continuous.comp continuous_snd)⟩
  have hp : Function.Surjective p := by
    rintro ⟨t, x⟩
    obtain ⟨z, hz⟩ := hradial x
    exact ⟨(t, z), Prod.ext rfl hz⟩
  have hpq : Topology.IsQuotientMap p :=
    Topology.IsQuotientMap.of_surjective_continuous hp p.continuous
  let apex : I → F := fun t => (1 - (t : ℝ)) • f 0 + (t : ℝ) • a
  have hapex (t : I) : apex t ∈ W :=
    hW (hfW (interior_subset hS0)) ha (sub_nonneg.mpr t.property.2)
      t.property.1 (sub_add_cancel 1 (t : ℝ))
  let T : C(I × (I × frontier S), W) :=
    ⟨fun z => ⟨(1 - (z.2.1 : ℝ)) • apex z.1 + (z.2.1 : ℝ) • (B (z.1, z.2.2) : F),
      hW (hapex z.1) (B (z.1, z.2.2)).property (sub_nonneg.mpr z.2.1.property.2)
        z.2.1.property.1 (sub_add_cancel 1 (z.2.1 : ℝ))⟩,
      by dsimp [apex]; fun_prop⟩
  have hfactor : Function.FactorsThrough T p := by
    intro z w hzw
    have ht : z.1 = w.1 := congrArg (fun v : I × S => v.1) hzw
    have hv : (z.2.1 : ℝ) • (z.2.2 : E) = (w.2.1 : ℝ) • (w.2.2 : E) :=
      congrArg (fun v : I × S => (v.2 : E)) hzw
    have hzG : gauge S (z.2.2 : E) = 1 :=
      (gauge_eq_one_iff_mem_frontier hScv (mem_interior_iff_mem_nhds.mp hS0)).mpr z.2.2.property
    have hwG : gauge S (w.2.2 : E) = 1 :=
      (gauge_eq_one_iff_mem_frontier hScv (mem_interior_iff_mem_nhds.mp hS0)).mpr w.2.2.property
    have hr : (z.2.1 : ℝ) = (w.2.1 : ℝ) := by
      have hh := congrArg (gauge S) hv
      simpa only [gauge_smul_of_nonneg z.2.1.property.1,
        gauge_smul_of_nonneg w.2.1.property.1, hzG, hwG, smul_eq_mul, mul_one] using hh
    by_cases hz : (z.2.1 : ℝ) = 0
    · apply Subtype.ext
      change (1 - (z.2.1 : ℝ)) • apex z.1 + (z.2.1 : ℝ) • (B (z.1, z.2.2) : F) =
        (1 - (w.2.1 : ℝ)) • apex w.1 + (w.2.1 : ℝ) • (B (w.1, w.2.2) : F)
      rw [← hr, hz, ht]
      simp
    · have hu : z.2.2 = w.2.2 := by
        apply Subtype.ext
        rw [← hr] at hv
        exact smul_right_injective E hz hv
      exact congrArg T (Prod.ext ht (Prod.ext (Subtype.ext hr) hu))
  let H := hpq.lift T hfactor
  have hH (t r : I) (u : frontier S) : H (t, radial (r, u)) = T (t, r, u) :=
    congrArg (fun k : C(I × (I × frontier S), W) => k (t, r, u))
      (hpq.lift_comp T hfactor)
  refine ⟨hlin, hrad, g, H, hCS, hg, hgPL, hg0, hgb, hgW, hgray, ?_, ?_, ?_⟩
  · intro x
    obtain ⟨⟨r, u⟩, rfl⟩ := hradial x
    rw [hH]
    change (1 - (r : ℝ)) • apex 0 + (r : ℝ) • (B (0, u) : F) = f ((r : ℝ) • (u : E))
    rw [hB0]
    have hzero : apex 0 = f 0 := by simp [apex]
    rw [hzero]
    have hf (y : E) : f y = f.contLinear y + f 0 := congrFun (f : E →ᵃ[ℝ] F).decomp y
    rw [hf ((r : ℝ) • (u : E)), hf u, map_smul]
    module
  · intro x
    obtain ⟨⟨r, u⟩, rfl⟩ := hradial x
    rw [hH]
    change (1 - (r : ℝ)) • apex 1 + (r : ℝ) • (B (1, u) : F) = g ((r : ℝ) • (u : E))
    rw [hB1, hgray u u.property r r.property]
    simp [apex]
  · intro t u
    have hu : radial (1, u) = ⟨u, hS.isClosed.frontier_subset u.property⟩ :=
      Subtype.ext (one_smul ℝ _)
    rw [← hu, hH]
    apply Subtype.ext
    change (1 - (1 : ℝ)) • apex t + (1 : ℝ) • (B (t, u) : F) = _
    simp

end Geometry.SimplicialComplex
