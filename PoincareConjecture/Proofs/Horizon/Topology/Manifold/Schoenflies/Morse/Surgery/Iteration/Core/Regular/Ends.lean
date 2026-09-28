import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.AnnularRegion



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



theorem cap_eq_end_of_annular_core
    {v : E3} {g : S2 -> E3} {B : Set Real}
    (L : List (SphereSurgeryCoreCap v g B))
    (hpair : L.Pairwise (fun D E => Disjoint
      (D.chart '' closedBall 0 1) (E.chart '' closedBall 0 1)))
    {C : Set S2} (hcore : C = (⋃ D ∈ L, D.chart '' ball 0 1)ᶜ)
    (F : OpenPartialHomeomorph (S1 × Real) S2) {a b δ : Real} (hδ : 0 < δ)
    (hFs : F.source = univ ×ˢ Ioo (a - δ) (b + δ))
    (hF : ContMDiffOn Iprod (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) Iprod ∞ F.symm F.target)
    {h : S2 -> Real}
    (hheight : ∀ q t, t ∈ Ioo (a - δ) (b + δ) -> h (F (q, t)) = t)
    (hactual : EqOn h (fun p => inner Real v (g p)) C)
    (hCband : C = F '' (univ ×ˢ Icc a b))
    (D E : SphereSurgeryCoreCap v g B) (hD : D ∈ L) (hE : E ∈ L)
    (hDa : D.center = a) (hEb : E.center = b) :
    ∀ A ∈ L, A = D ∨ A = E := by
  classical
  obtain ⟨q₀, hq₀⟩ := (NormedSpace.sphere_nonempty (E := E2)).mpr zero_le_one
  let q : S1 := ⟨q₀, hq₀⟩
  have hband : Icc a b ⊆ Ioo (a - δ) (b + δ) := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hsource : univ ×ˢ Ioo a b ⊆ F.source := by
    rintro ⟨z, t⟩ ⟨_, ht⟩
    rw [hFs]
    exact ⟨mem_univ z, hband ⟨ht.1.le, ht.2.le⟩⟩
  have hopen : IsOpen (F '' (univ ×ˢ Ioo a b)) :=
    F.isOpen_image_of_subset_source (isOpen_univ.prod isOpen_Ioo) hsource
  have hopenCore : F '' (univ ×ˢ Ioo a b) ⊆ interior C := by
    apply interior_maximal ?_ hopen
    rw [hCband]
    exact image_mono (prod_mono Subset.rfl Ioo_subset_Icc_self)
  have hboundary (A : SphereSurgeryCoreCap v g B) (hA : A ∈ L) :
      A.chart '' sphere (0 : E2) 1 ⊆ C := fun p hp =>
    ((core_inter_closed_disk L hpair hcore A hA).superset hp).1
  have hfront (A : SphereSurgeryCoreCap v g B) (hA : A ∈ L) :
      A.chart '' sphere (0 : E2) 1 ⊆ frontier C := by
    rw [frontier_core L hpair hcore]
    exact fun p hp => mem_iUnion_of_mem A (mem_iUnion_of_mem hA hp)
  have htarget : C ⊆ F.target := by
    rw [hCband]
    rintro p ⟨⟨z, t⟩, ⟨_, ht⟩, rfl⟩
    exact F.map_source (hFs ▸ ⟨mem_univ z, hband ht⟩)
  have hDheight (A : SphereSurgeryCoreCap v g B) (hA : A ∈ L) :
      ∀ p ∈ A.chart '' sphere (0 : E2) 1, h p = A.center := by
    intro p hp
    exact (hactual (hboundary A hA hp)).trans (A.height_eq_on_boundary p hp)
  have hlevels (A : SphereSurgeryCoreCap v g B) (hA : A ∈ L) :
      A.center ∈ Icc a b ∧ (A.center = a ∨ A.center = b) := by
    have hp : A.chart q ∈ A.chart '' sphere (0 : E2) 1 := mem_image_of_mem _ q.property
    obtain ⟨⟨z, t⟩, ⟨_, ht⟩, hzp⟩ := hCband ▸ hboundary A hA hp
    have hct : A.center = t :=
      (hDheight A hA _ hp).symm.trans ((congrArg h hzp).symm.trans (hheight z t (hband ht)))
    refine ⟨hct ▸ ht, ?_⟩
    by_contra hnot
    have hca : A.center ≠ a := fun hh => hnot (Or.inl hh)
    have hcb : A.center ≠ b := fun hh => hnot (Or.inr hh)
    have hti : t ∈ Ioo a b :=
      ⟨lt_of_le_of_ne ht.1 (fun hh => hca (hct.trans hh.symm)),
        lt_of_le_of_ne ht.2 (fun hh => hcb (hct.trans hh))⟩
    exact (hfront A hA hp).2 (hopenCore ⟨(z, t), ⟨mem_univ _, hti⟩, hzp⟩)
  have hcircles (A : SphereSurgeryCoreCap v g B) (hA : A ∈ L) :
      A.chart '' sphere (0 : E2) 1 = range (fun z : S1 => F (z, A.center)) :=
    A.boundary_eq_annular_slice F hFs hF hFi hheight (hband (hlevels A hA).1)
      ((hboundary A hA).trans htarget) (hDheight A hA)
  have hequal (A A' : SphereSurgeryCoreCap v g B) (hA : A ∈ L) (hA' : A' ∈ L)
      (hc : A.center = A'.center) : A = A' := by
    by_contra hne
    have heq : A.chart '' sphere (0 : E2) 1 = A'.chart '' sphere (0 : E2) 1 := by
      rw [hcircles A hA, hcircles A' hA', hc]
    have hp : A.chart q ∈ A.chart '' sphere (0 : E2) 1 := mem_image_of_mem _ q.property
    exact Set.disjoint_left.mp (hpair.forall hA hA' hne)
      (image_mono sphere_subset_closedBall hp)
      (image_mono sphere_subset_closedBall (heq ▸ hp))
  intro A hA
  rcases (hlevels A hA).2 with ha | hb
  · exact Or.inl (hequal A D hA hD (ha.trans hDa.symm))
  · exact Or.inr (hequal A E hA hE (hb.trans hEb.symm))

end Poincare.Manifold.Schoenflies.SphereSurgeryCoreCap
