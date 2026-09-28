import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.RegularBand.CapGraph.Representation
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.RegularBand.CapGraph.Transport



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

open Poincare.Geometry.Euclidean

private abbrev E3 := EuclideanSpace Real (Fin 3)




theorem exists_upper_cap_interior_normalization
    {v : E3} (hv : ‖v‖ = 1)
    (P : Diffeomorph 𝓘(Real, Hemisphere.Plane v) 𝓘(Real, Hemisphere.Plane v)
      (Hemisphere.Plane v) (Hemisphere.Plane v) ∞)
    (hball : P '' ball (0 : Hemisphere.Plane v) 1 = ball (0 : Hemisphere.Plane v) 1)
    (hboundary : P '' sphere (0 : Hemisphere.Plane v) 1 = sphere (0 : Hemisphere.Plane v) 1)
    {ε : Real} (hε : 0 < ε) (hε1 : ε < 1)
    (hcollar : ∀ x : Hemisphere.Plane v, |‖x‖ - 1| < ε → ‖P x‖ = ‖x‖) :
    ∃ K : Set E3, IsCompact K ∧
      K ⊆ {y | 0 < inner Real v y ∧
        ‖(Hemisphere.Plane v).orthogonalProjectionOnto y‖ < 1} ∧
      ∃ D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        (∀ y, (Hemisphere.Plane v).orthogonalProjectionOnto (D y) =
          (Hemisphere.Plane v).orthogonalProjectionOnto y) ∧
        (∀ y ∉ K, D y = y) ∧
        D '' (liftPlaneDiffeomorph hv 0 1 one_ne_zero P '' boundedCylinderNorthernCap v) =
          boundedCylinderNorthernCap v := by
  obtain ⟨K, hK, hKO, F, hFfirst, hFfix, hFgraph⟩ :=
    exists_cap_graph_normalization P hball hε hε1 hcollar
  let C := ((ContinuousLinearEquiv.prodComm Real (Hemisphere.Plane v) Real).trans
    (heightCoordinates hv)).toDiffeomorph
  have hC (z : Hemisphere.Plane v × Real) : C z = z.2 • v + (z.1 : E3) := rfl
  have hCinv (y : E3) : C.symm y =
      ((Hemisphere.Plane v).orthogonalProjectionOnto y, inner Real v y) := rfl
  have hCproj (z : Hemisphere.Plane v × Real) :
      (Hemisphere.Plane v).orthogonalProjectionOnto (C z) = z.1 :=
    congrArg Prod.fst (C.symm_apply_apply z)
  have hCheight (z : Hemisphere.Plane v × Real) : inner Real v (C z) = z.2 :=
    congrArg Prod.snd (C.symm_apply_apply z)
  let D := (C.symm.trans F).trans C
  have hD (z : Hemisphere.Plane v × Real) : D (C z) = C (F z) := by
    change C (F (C.symm (C z))) = _
    rw [C.symm_apply_apply]
  let L := liftPlaneDiffeomorph hv 0 1 one_ne_zero P
  have hLC (z : Hemisphere.Plane v × Real) : L (C z) = C (P z.1, z.2) := by
    change liftPlaneDiffeomorph hv 0 1 one_ne_zero P (C z) = _
    rw [liftPlaneDiffeomorph_apply]
    change (0 + 1 * inner Real v (C z)) • v +
      (P ((Hemisphere.Plane v).orthogonalProjectionOnto (C z)) : E3) = _
    rw [zero_add, one_mul, hCheight, hCproj, hC]
  have hB (x : Hemisphere.Plane v) : ‖P x‖ < 1 ↔ ‖x‖ < 1 := by
    constructor
    · intro hx
      have hmem : P x ∈ P '' ball (0 : Hemisphere.Plane v) 1 := by
        rw [hball]; exact mem_ball_zero_iff.mpr hx
      obtain ⟨y, hy, heq⟩ := hmem
      have := P.injective heq
      subst y
      exact mem_ball_zero_iff.mp hy
    · intro hx
      have hmem : P x ∈ P '' ball (0 : Hemisphere.Plane v) 1 :=
        ⟨x, mem_ball_zero_iff.mpr hx, rfl⟩
      rw [hball] at hmem
      exact mem_ball_zero_iff.mp hmem
  have hS (x : Hemisphere.Plane v) : ‖P x‖ = 1 ↔ ‖x‖ = 1 := by
    constructor
    · intro hx
      have hmem : P x ∈ P '' sphere (0 : Hemisphere.Plane v) 1 := by
        rw [hboundary]; exact mem_sphere_zero_iff_norm.mpr hx
      obtain ⟨y, hy, heq⟩ := hmem
      have := P.injective heq
      subst y
      exact mem_sphere_zero_iff_norm.mp hy
    · intro hx
      have hmem : P x ∈ P '' sphere (0 : Hemisphere.Plane v) 1 :=
        ⟨x, mem_sphere_zero_iff_norm.mpr hx, rfl⟩
      rw [hboundary] at hmem
      exact mem_sphere_zero_iff_norm.mp hmem
  have hcap (z : Hemisphere.Plane v × Real) : C z ∈ boundedCylinderNorthernCap v ↔
      (‖z.1‖ = 1 ∧ z.2 ∈ Icc (0 : Real) 1) ∨
        (‖z.1‖ < 1 ∧ z.2 = boundedCapHeight (‖z.1‖ ^ 2)) := by
    rw [mem_boundedCylinderNorthernCap_iff_cases hv, hCproj, hCheight]
  have hFboundary (x : Hemisphere.Plane v) (t : Real) (hx : ‖x‖ = 1) :
      F (x, t) = (x, t) := by
    apply hFfix
    intro hmem
    have hh := mem_ball_zero_iff.mp (hKO hmem).1
    linarith
  refine ⟨C '' K, hK.image C.continuous, ?_, D, ?_, ?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact ⟨by rw [hCheight]; exact (hKO hz).2,
      by rw [hCproj]; exact mem_ball_zero_iff.mp (hKO hz).1⟩
  · intro y
    change (Hemisphere.Plane v).orthogonalProjectionOnto (C (F (C.symm y))) = _
    rw [hCproj, hFfirst]
    rfl
  · intro y hy
    have hnot : C.symm y ∉ K := fun h => hy ⟨C.symm y, h, C.apply_symm_apply y⟩
    change C (F (C.symm y)) = y
    rw [hFfix _ hnot, C.apply_symm_apply]
  · change D '' (L '' boundedCylinderNorthernCap v) = boundedCylinderNorthernCap v
    ext y
    constructor
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      obtain ⟨⟨x, t⟩, rfl⟩ := C.surjective z
      change C (x, t) ∈ boundedCylinderNorthernCap v at hz
      change D (L (C (x, t))) ∈ boundedCylinderNorthernCap v
      rw [hLC, hD]
      rcases (hcap (x, t)).mp hz with ⟨hx, ht⟩ | ⟨hx, ht⟩
      · rw [hFboundary _ _ ((hS x).mpr hx)]
        exact (hcap _).mpr (Or.inl ⟨(hS x).mpr hx, ht⟩)
      · have hPx : P x ∈ ball (0 : Hemisphere.Plane v) 1 :=
          mem_ball_zero_iff.mpr ((hB x).mpr hx)
        change t = boundedCapHeight (‖x‖ ^ 2) at ht
        have hf : F (P x, t) = (P x, boundedCapHeight (‖P x‖ ^ 2)) := by
          simpa only [P.symm_apply_apply, ← ht] using hFgraph (P x) hPx
        rw [hf]
        exact (hcap _).mpr (Or.inr ⟨(hB x).mpr hx, rfl⟩)
    · intro hy
      obtain ⟨⟨x, t⟩, rfl⟩ := C.surjective y
      change C (x, t) ∈ boundedCylinderNorthernCap v at hy
      change C (x, t) ∈ D '' (L '' boundedCylinderNorthernCap v)
      rcases (hcap (x, t)).mp hy with ⟨hx, ht⟩ | ⟨hx, ht⟩
      · have hPx : ‖P.symm x‖ = 1 := (hS _).mp (by simpa)
        refine ⟨L (C (P.symm x, t)), ⟨C (P.symm x, t),
          (hcap _).mpr (Or.inl ⟨hPx, ht⟩), rfl⟩, ?_⟩
        rw [hLC, P.apply_symm_apply, hD, hFboundary x t hx]
      · have hPx : ‖P.symm x‖ < 1 := (hB _).mp (by simpa)
        change t = boundedCapHeight (‖x‖ ^ 2) at ht
        let z := C (P.symm x, boundedCapHeight (‖P.symm x‖ ^ 2))
        refine ⟨L z, ⟨z, (hcap _).mpr (Or.inr ⟨hPx, rfl⟩), rfl⟩, ?_⟩
        change D (L (C _)) = C (x, t)
        rw [hLC, P.apply_symm_apply, hD, hFgraph x (mem_ball_zero_iff.mpr hx), ht]

end Poincare.Manifold.Schoenflies
