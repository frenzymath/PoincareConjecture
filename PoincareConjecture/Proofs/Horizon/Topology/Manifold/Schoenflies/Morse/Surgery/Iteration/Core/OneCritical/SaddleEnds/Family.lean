import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.OneCritical.SaddleEnds.UpperAnnulus

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.SphereSurgeryCoreCap

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1
local notation "Iprod" => ModelWithCorners.prod (𝓡 1) 𝓘(Real, Real)

variable {v : E3} {g : S2 → E3} {B : Set Real}

structure LowerAnnularEnd (D : SphereSurgeryCoreCap v g B)
    (C : Set S2) (h : S2 → Real) (a b : Real) where
  delta : Real
  delta_pos : 0 < delta
  chart : OpenPartialHomeomorph (S1 × Real) S2
  source : chart.source = univ ×ˢ Ioo (a - delta) (b + delta)
  smooth : ContMDiffOn Iprod (𝓡 2) ∞ chart chart.source
  symm_smooth : ContMDiffOn (𝓡 2) Iprod ∞ chart.symm chart.target
  height : ∀ q t, t ∈ Ioo (a - delta) (b + delta) → h (chart (q, t)) = t
  boundary : range (fun q : S1 => chart (q, D.center)) = D.chart '' sphere (0 : E2) 1
  retained : chart '' (univ ×ˢ Icc D.center b) ⊆ C
  interior : chart '' (univ ×ˢ Ioo D.center b) ⊆ interior C
  actual_height : ∀ q t, t ∈ Icc D.center b → inner Real v (g (chart (q, t))) = t
  component : ∀ p ∈ D.chart '' sphere (0 : E2) 1,
    chart '' (univ ×ˢ Icc a b) = connectedComponentIn (h ⁻¹' Icc a b) p
  scale_neg : D.scale < 0

theorem exists_lowerAnnularEnd
    (L : List (SphereSurgeryCoreCap v g B))
    (hpair : L.Pairwise (fun D E => Disjoint
      (D.chart '' closedBall 0 1) (E.chart '' closedBall 0 1)))
    {C : Set S2} (hcore : C = (⋃ D ∈ L, D.chart '' ball 0 1)ᶜ)
    (hC : IsPreconnected C) (hclosed : IsClosed C)
    {h : S2 → Real} (hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h)
    (hgerm : ∀ p ∈ C, h =ᶠ[𝓝 p] (fun q => inner Real v (g q)))
    {a b : Real} (hab : a < b)
    (hlower : ∀ p ∈ C, a ≤ h p) (hgreater : ∃ p ∈ C, b < h p)
    (hregular : ∀ p, h p ∈ Icc a b → mfderiv (𝓡 2) 𝓘(Real, Real) h p ≠ 0)
    (D : SphereSurgeryCoreCap v g B) (hD : D ∈ L) (hDb : D.center < b) :
    Nonempty (LowerAnnularEnd D C h a b) := by
  obtain ⟨hs, δ, hδ, F, hFs, hF, hFi, hheight, hcircle, hretained,
      hinterior, hactual, hcomponent⟩ :=
    exists_lower_annular_end L hpair hcore hC hclosed hh hgerm hab hlower hgreater
      hregular D hD hDb
  exact ⟨⟨δ, hδ, F, hFs, hF, hFi, hheight, hcircle, hretained,
    hinterior, hactual, hcomponent, hs⟩⟩

namespace LowerAnnularEnd

variable {D E : SphereSurgeryCoreCap v g B} {C : Set S2} {h : S2 → Real} {a b : Real}

def band (A : LowerAnnularEnd D C h a b) : Set S2 :=
  A.chart '' (univ ×ˢ Icc a b)

def region (A : LowerAnnularEnd D C h a b) : Set S2 :=
  A.chart '' (univ ×ˢ Icc D.center b)

theorem band_subset_target (A : LowerAnnularEnd D C h a b) : A.band ⊆ A.chart.target := by
  rintro p ⟨⟨q, t⟩, ⟨_, ht⟩, rfl⟩
  apply A.chart.map_source
  rw [A.source]
  exact ⟨mem_univ _, by linarith [ht.1, A.delta_pos], by linarith [ht.2, A.delta_pos]⟩

theorem region_subset_band (A : LowerAnnularEnd D C h a b) (hDa : a ≤ D.center) :
    A.region ⊆ A.band :=
  image_mono (prod_mono Subset.rfl (Icc_subset_Icc_left hDa))

theorem boundary_mem_band (A : LowerAnnularEnd D C h a b)
    (hDa : a ≤ D.center) (hDb : D.center ≤ b)
    {p : S2} (hp : p ∈ D.chart '' sphere (0 : E2) 1) : p ∈ A.band := by
  rw [← A.boundary] at hp
  obtain ⟨q, rfl⟩ := hp
  exact mem_image_of_mem _ ⟨mem_univ _, hDa, hDb⟩

theorem eq_cap_of_boundary_mem_band
    (L : List (SphereSurgeryCoreCap v g B))
    (hpair : L.Pairwise (fun D E => Disjoint
      (D.chart '' closedBall 0 1) (E.chart '' closedBall 0 1)))
    (hcore : C = (⋃ D ∈ L, D.chart '' ball 0 1)ᶜ)
    (hh : Continuous h)
    (hgerm : ∀ p ∈ C, h =ᶠ[𝓝 p] (fun q => inner Real v (g q)))
    (A : LowerAnnularEnd D C h a b) (hD : D ∈ L)
    (hDa : a ≤ D.center) (hDb : D.center < b)
    (hE : E ∈ L) (hEb : E.center < b)
    {p : S2} (hpE : p ∈ E.chart '' sphere (0 : E2) 1) (hpA : p ∈ A.band) : D = E := by
  have hboundary (J : SphereSurgeryCoreCap v g B) (hJ : J ∈ L) :
      J.chart '' sphere (0 : E2) 1 ⊆ C := fun y hy =>
    ((core_inter_closed_disk L hpair hcore J hJ).superset hy).1
  have hheight (J : SphereSurgeryCoreCap v g B) (hJ : J ∈ L)
      (y : S2) (hy : y ∈ J.chart '' sphere (0 : E2) 1) : h y = J.center :=
    ((hgerm y (hboundary J hJ hy)).eq_of_nhds).trans (J.height_eq_on_boundary y hy)
  obtain ⟨⟨q, t⟩, ⟨_, ht⟩, rfl⟩ := hpA
  have hts : t ∈ Ioo (a - A.delta) (b + A.delta) :=
    ⟨by linarith [ht.1, A.delta_pos], by linarith [ht.2, A.delta_pos]⟩
  have hte : t = E.center := (A.height q t hts).symm.trans (hheight E hE _ hpE)
  obtain ⟨z, hzD⟩ := D.isConnected_boundary.nonempty
  have hzA := A.band_subset_target (A.boundary_mem_band hDa hDb.le hzD)
  have hdc : D.center ∈ Ioo (a - A.delta) (b + A.delta) :=
    ⟨by linarith [A.delta_pos], by linarith [A.delta_pos]⟩
  rcases lt_trichotomy t D.center with hlt | heq | hgt
  · have hcap := D.lower_annular_strip_subset_open_disk_of_scale_neg A.scale_neg hh
      A.chart A.source A.height hdc (hheight D hD) hzD hzA (hgerm z (hboundary D hD hzD))
    have hpD := hcap (mem_image_of_mem A.chart
      (show (q, t) ∈ univ ×ˢ Ioo (a - A.delta) D.center from ⟨mem_univ _, hts.1, hlt⟩))
    have hpC := hcore.subset (hboundary E hE hpE)
    exact False.elim (hpC (mem_iUnion_of_mem D (mem_iUnion_of_mem hD hpD)))
  · have hpD : A.chart (q, t) ∈ D.chart '' sphere (0 : E2) 1 := by
      rw [← A.boundary, heq]
      exact mem_range_self q
    by_contra hne
    exact Set.disjoint_left.mp (hpair.forall hD hE hne)
      (image_mono sphere_subset_closedBall hpD) (image_mono sphere_subset_closedBall hpE)
  · have hpint := A.interior (mem_image_of_mem A.chart
      (show (q, t) ∈ univ ×ˢ Ioo D.center b from ⟨mem_univ _, hgt, hte ▸ hEb⟩))
    have hpfront : A.chart (q, t) ∈ frontier C := by
      rw [frontier_core L hpair hcore]
      exact mem_iUnion_of_mem E (mem_iUnion_of_mem hE hpE)
    exact False.elim (hpfront.2 hpint)

theorem disjoint_band
    (L : List (SphereSurgeryCoreCap v g B))
    (hpair : L.Pairwise (fun D E => Disjoint
      (D.chart '' closedBall 0 1) (E.chart '' closedBall 0 1)))
    (hcore : C = (⋃ D ∈ L, D.chart '' ball 0 1)ᶜ)
    (hh : Continuous h)
    (hgerm : ∀ p ∈ C, h =ᶠ[𝓝 p] (fun q => inner Real v (g q)))
    (A : LowerAnnularEnd D C h a b) (AE : LowerAnnularEnd E C h a b)
    (hD : D ∈ L) (hE : E ∈ L) (hDa : a ≤ D.center) (hEa : a ≤ E.center)
    (hDb : D.center < b) (hEb : E.center < b) (hne : D ≠ E) :
    Disjoint A.band AE.band := by
  apply Set.disjoint_left.mpr
  intro p hpA hpE
  obtain ⟨d, hd⟩ := D.isConnected_boundary.nonempty
  obtain ⟨e, he⟩ := E.isConnected_boundary.nonempty
  have hAd : A.band = connectedComponentIn (h ⁻¹' Icc a b) d := A.component d hd
  have hEe : AE.band = connectedComponentIn (h ⁻¹' Icc a b) e := AE.component e he
  have heq : A.band = AE.band := by
    rw [hAd, hEe]
    exact (connectedComponentIn_eq (hAd ▸ hpA)).trans
      (connectedComponentIn_eq (hEe ▸ hpE)).symm
  exact hne (A.eq_cap_of_boundary_mem_band L hpair hcore hh hgerm hD hDa hDb hE hEb he
    (heq ▸ AE.boundary_mem_band hEa hEb.le he))

theorem disjoint_region
    (L : List (SphereSurgeryCoreCap v g B))
    (hpair : L.Pairwise (fun D E => Disjoint
      (D.chart '' closedBall 0 1) (E.chart '' closedBall 0 1)))
    (hcore : C = (⋃ D ∈ L, D.chart '' ball 0 1)ᶜ)
    (hh : Continuous h)
    (hgerm : ∀ p ∈ C, h =ᶠ[𝓝 p] (fun q => inner Real v (g q)))
    (A : LowerAnnularEnd D C h a b) (AE : LowerAnnularEnd E C h a b)
    (hD : D ∈ L) (hE : E ∈ L) (hDa : a ≤ D.center) (hEa : a ≤ E.center)
    (hDb : D.center < b) (hEb : E.center < b) (hne : D ≠ E) :
    Disjoint A.region AE.region :=
  (A.disjoint_band L hpair hcore hh hgerm AE hD hE hDa hEa hDb hEb hne).mono
    (A.region_subset_band hDa) (AE.region_subset_band hEa)

end LowerAnnularEnd

end Poincare.Manifold.Schoenflies.SphereSurgeryCoreCap
