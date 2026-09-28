import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.Boundary
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.RegularLevel.CircleInAnnulus
import PoincareConjecture.Proofs.Horizon.Topology.Connected.Fibers

open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.PoincareConjecture

namespace M38Schoenflies

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
local notation "Iprod" => ModelWithCorners.prod (𝓡 1) 𝓘(Real, Real)

variable {v : E3} {g : S2 -> E3} {B : Set Real}

theorem smooth_boundary (D : SphereSurgeryCoreCap v g B) :
    ContMDiff (𝓡 1) (𝓡 2) ∞ (fun q : S1 => D.chart q) := by
  intro q
  exact (D.smooth.contMDiffAt (D.chart.open_source.mem_nhds
    (D.source (sphere_subset_closedBall q.property)))).comp q (contMDiff_coe_sphere q)

theorem boundary_deriv_injective (D : SphereSurgeryCoreCap v g B) (q : S1) :
    Function.Injective (mfderiv (𝓡 1) (𝓡 2) (fun p : S1 => D.chart p) q) := by
  let d : PartialDiffeomorph (𝓡 2) (𝓡 2) E2 S2 ∞ := {
    toPartialEquiv := D.chart.toPartialEquiv
    open_source := D.chart.open_source
    open_target := D.chart.open_target
    contMDiffOn_toFun := D.smooth
    contMDiffOn_invFun := D.symm_smooth }
  have hloc : IsLocalDiffeomorphAt (𝓡 2) (𝓡 2) ∞ D.chart (q : E2) :=
    ⟨d, D.source (sphere_subset_closedBall q.property), fun _ _ => rfl⟩
  have hd := (D.smooth.contMDiffAt (D.chart.open_source.mem_nhds
    (D.source (sphere_subset_closedBall q.property)))).mdifferentiableAt (by simp)
  have hcoe : MDifferentiableAt (𝓡 1) (𝓡 2) (Subtype.val : S1 -> E2) q :=
    (contMDiff_coe_sphere (n := 1) (m := ∞) q).mdifferentiableAt (by simp)
  change Function.Injective (mfderiv (𝓡 1) (𝓡 2) (D.chart ∘ Subtype.val) q)
  rw [mfderiv_comp q hd hcoe]
  apply (hloc.mfderivToContinuousLinearEquiv (by simp)).injective.comp
  convert! injective_mvfderiv_subtypeVal_sphere q

theorem boundary_eq_annular_slice (D : SphereSurgeryCoreCap v g B)
    (F : OpenPartialHomeomorph (S1 × Real) S2) {a b : Real}
    (hFs : F.source = univ ×ˢ Ioo a b)
    (hF : ContMDiffOn Iprod (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) Iprod ∞ F.symm F.target)
    {h : S2 -> Real} (hheight : ∀ q t, t ∈ Ioo a b -> h (F (q, t)) = t)
    (hc : D.center ∈ Ioo a b)
    (htarget : D.chart '' sphere (0 : E2) 1 ⊆ F.target)
    (hDheight : ∀ p ∈ D.chart '' sphere (0 : E2) 1, h p = D.center) :
    D.chart '' sphere (0 : E2) 1 = range (fun q : S1 => F (q, D.center)) := by
  have hrange : range (fun q : S1 => D.chart q) = D.chart '' sphere (0 : E2) 1 := by
    ext p
    constructor
    · rintro ⟨q, rfl⟩
      exact mem_image_of_mem D.chart q.property
    · rintro ⟨q, hq, rfl⟩
      exact ⟨⟨q, hq⟩, rfl⟩
  rw [← hrange]
  apply range_eq_annular_slice_of_immersed_circle F hFs hF hFi hheight hc
    (fun q : S1 => D.chart q) D.smooth_boundary D.boundary_deriv_injective
  · rwa [hrange]
  · exact fun q => hDheight _ (mem_image_of_mem D.chart q.property)

theorem core_eq_annular_band
    (L : List (SphereSurgeryCoreCap v g B))
    (hpair : L.Pairwise (fun D E => Disjoint
      (D.chart '' closedBall 0 1) (E.chart '' closedBall 0 1)))
    {C : Set S2} (hcore : C = (⋃ D ∈ L, D.chart '' ball 0 1)ᶜ)
    (hC : IsPreconnected C)
    (F : OpenPartialHomeomorph (S1 × Real) S2) {a b δ : Real} (hδ : 0 < δ)
    (hFs : F.source = univ ×ˢ Ioo (a - δ) (b + δ))
    (hF : ContMDiffOn Iprod (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) Iprod ∞ F.symm F.target)
    {h : S2 -> Real} (hh : ContinuousOn h C)
    (hheight : ∀ q t, t ∈ Ioo (a - δ) (b + δ) -> h (F (q, t)) = t)
    (hactual : EqOn h (fun p => inner Real v (g p)) C)
    (hcover : C ⊆ F '' (univ ×ˢ Icc a b))
    (ha : a ∈ h '' C) (hb : b ∈ h '' C) :
    C = F '' (univ ×ˢ Icc a b) := by
  let : ConnectedSpace S1 := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (E := E2) (by rw [← Module.finrank_eq_rank]; norm_num)
      0 zero_le_one)
  have hband : Icc a b ⊆ Ioo (a - δ) (b + δ) := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have htarget : C ⊆ F.target := by
    intro p hp
    obtain ⟨⟨q, t⟩, ⟨_, ht⟩, rfl⟩ := hcover hp
    exact F.map_source (hFs ▸ ⟨mem_univ _, hband ht⟩)
  have hboundary (D : SphereSurgeryCoreCap v g B) (hD : D ∈ L) :
      D.chart '' sphere (0 : E2) 1 ⊆ C := fun p hp =>
    ((core_inter_closed_disk L hpair hcore D hD).superset hp).1
  have hDheight (D : SphereSurgeryCoreCap v g B) (hD : D ∈ L) :
      ∀ p ∈ D.chart '' sphere (0 : E2) 1, h p = D.center := by
    intro p hp
    exact (hactual (hboundary D hD hp)).trans (D.height_eq_on_boundary p hp)
  refine Poincare.Topology.eq_image_closed_band_of_frontier_saturated F ?_ hC hh
    (fun q t ht => hheight q t (hband ht)) hcover ha hb ?_
  · intro t ht
    apply ContinuousOn.comp_continuous hF.continuousOn (continuous_id.prodMk continuous_const)
    exact fun q => hFs ▸ ⟨mem_univ q, hband ht⟩
  · intro t ht q hq
    rw [frontier_core L hpair hcore] at hq
    simp only [mem_iUnion] at hq
    obtain ⟨D, hD, hqD⟩ := hq
    have hct : D.center = t := (hDheight D hD _ hqD).symm.trans (hheight q t (hband ht))
    have hcircle := D.boundary_eq_annular_slice F hFs hF hFi hheight
      (hct ▸ hband ht) ((hboundary D hD).trans htarget) (hDheight D hD)
    rw [← hct, ← hcircle]
    exact hboundary D hD

end Poincare.Manifold.Schoenflies.SphereSurgeryCoreCap

end

end M38Schoenflies
