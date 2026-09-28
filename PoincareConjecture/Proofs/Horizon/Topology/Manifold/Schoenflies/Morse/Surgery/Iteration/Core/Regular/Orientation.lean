import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.Boundary
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.CapHeight

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.SphereSurgeryCoreCap

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1

variable {v : E3} {g : S2 -> E3} {B : Set Real}

theorem end_scales_of_annular_core
    (L : List (SphereSurgeryCoreCap v g B))
    (hpair : L.Pairwise (fun D E => Disjoint
      (D.chart '' closedBall 0 1) (E.chart '' closedBall 0 1)))
    (hg : Continuous g)
    {C : Set S2} (hcore : C = (⋃ D ∈ L, D.chart '' ball 0 1)ᶜ)
    (F : OpenPartialHomeomorph (S1 × Real) S2)
    {a b δ : Real} (hab : a < b) (hδ : 0 < δ)
    (hFs : F.source = univ ×ˢ Ioo (a - δ) (b + δ))
    (hheight : ∀ q t, t ∈ Ioo (a - δ) (b + δ) ->
      inner Real v (g (F (q, t))) = t)
    (hCband : C = F '' (univ ×ˢ Icc a b))
    (D E : SphereSurgeryCoreCap v g B) (hD : D ∈ L) (hE : E ∈ L)
    (hDa : D.center = a) (hEb : E.center = b) :
    D.scale < 0 ∧ 0 < E.scale := by
  let H : S2 -> Real := fun p => inner Real v (g p)
  have hH : Continuous H := (innerSL Real v).continuous.comp hg
  obtain ⟨x, hx⟩ := (NormedSpace.sphere_nonempty (E := E2)).mpr zero_le_one
  have hband : Icc a b ⊆ Ioo (a - δ) (b + δ) := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have htarget : C ⊆ F.target := by
    rw [hCband]
    rintro p ⟨⟨q, t⟩, ⟨_, ht⟩, rfl⟩
    exact F.map_source (hFs ▸ ⟨mem_univ q, hband ht⟩)
  have hmem (p : S2) (hp : p ∈ F.target) (hh : H p ∈ Icc a b) : p ∈ C := by
    have hs := F.map_target hp
    have ht := hheight (F.symm p).1 (F.symm p).2 (hFs ▸ hs).2
    rw [F.right_inv hp] at ht
    rw [hCband]
    exact ⟨F.symm p, ⟨mem_univ _, ht ▸ hh⟩, F.right_inv hp⟩
  have hboundary (A : SphereSurgeryCoreCap v g B) (hA : A ∈ L) :
      A.chart x ∈ C :=
    ((core_inter_closed_disk L hpair hcore A hA).superset
      (mem_image_of_mem _ hx)).1
  have hclosure (A : SphereSurgeryCoreCap v g B) :
      A.chart x ∈ closure (A.chart '' ball (0 : E2) 1) := by
    rw [ParallelDisks.closure_image_ball zero_lt_one A.chart A.source]
    exact mem_image_of_mem _ (sphere_subset_closedBall hx)
  have hdisjoint (A : SphereSurgeryCoreCap v g B) (hA : A ∈ L)
      {p : S2} (hp : p ∈ A.chart '' ball (0 : E2) 1) : p ∉ C := by
    rw [hcore]
    exact fun hn => hn (mem_iUnion_of_mem A (mem_iUnion_of_mem hA hp))
  constructor
  · by_contra hneg
    have hs : 0 < D.scale := lt_of_le_of_ne (le_of_not_gt hneg) D.scale_ne_zero.symm
    let U : Set S2 := F.target ∩ H ⁻¹' Iio b
    have hU : IsOpen U := F.open_target.inter (hH.isOpen_preimage _ isOpen_Iio)
    have hpU : D.chart x ∈ U := by
      refine ⟨htarget (hboundary D hD), ?_⟩
      change H (D.chart x) < b
      have hh := D.height_eq_on_boundary (D.chart x) (mem_image_of_mem _ hx)
      change H (D.chart x) = D.center at hh
      rw [hh, hDa]
      exact hab
    obtain ⟨p, hpU, hpD⟩ := mem_closure_iff.mp (hclosure D) U hU hpU
    have hpH := mul_pos (D.normalized_height_pos_on_open_disk hpD) hs
    rw [div_mul_cancel₀ _ D.scale_ne_zero] at hpH
    have hpa : a < H p := by change 0 < H p - D.center at hpH; rw [hDa] at hpH; linarith
    exact hdisjoint D hD hpD (hmem p hpU.1 ⟨hpa.le, hpU.2.le⟩)
  · by_contra hpos
    have hs : E.scale < 0 := lt_of_le_of_ne (le_of_not_gt hpos) E.scale_ne_zero
    let U : Set S2 := F.target ∩ H ⁻¹' Ioi a
    have hU : IsOpen U := F.open_target.inter (hH.isOpen_preimage _ isOpen_Ioi)
    have hpU : E.chart x ∈ U := by
      refine ⟨htarget (hboundary E hE), ?_⟩
      change a < H (E.chart x)
      have hh := E.height_eq_on_boundary (E.chart x) (mem_image_of_mem _ hx)
      change H (E.chart x) = E.center at hh
      rw [hh, hEb]
      exact hab
    obtain ⟨p, hpU, hpE⟩ := mem_closure_iff.mp (hclosure E) U hU hpU
    have hpH := mul_neg_of_pos_of_neg (E.normalized_height_pos_on_open_disk hpE) hs
    rw [div_mul_cancel₀ _ E.scale_ne_zero] at hpH
    have hpb : H p < b := by change H p - E.center < 0 at hpH; rw [hEb] at hpH; linarith
    exact hdisjoint E hE hpE (hmem p hpU.1 ⟨hpU.2.le, hpb.le⟩)

end Poincare.Manifold.Schoenflies.SphereSurgeryCoreCap
