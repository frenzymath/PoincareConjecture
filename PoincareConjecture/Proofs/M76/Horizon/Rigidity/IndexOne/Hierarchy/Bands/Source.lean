import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Hierarchy.Bands.StandardPL
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Hierarchy.Boundary.OriginalPLInverse
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Hierarchy.Disks.SourceMeridian










set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1
local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "R" => latticeHandleDomain (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "B" => latticeHandleBoundary (Fin 1) (Fin 2) L
local notation "p" => (4 * (128 : ℝ))
local notation "C" => AddCircle p
local notation "Ann" => squareAnnulus 8 1


noncomputable def sourceMeridianBandCylinder
    {phi : C(H, H)} {a b : ℝ} (hab : a < b) (hshort : b < a + p)
    (E : frontier (sourceSlab phi a b) ≃ₜ frontier (sourceSlab (ContinuousMap.id H) a b)) :
    (Q ×ˢ I) ≃ₜ frontierBandPullback E (standardMeridianBand a b) :=
  pulledBackBandCylinder E (standardMeridianBand_subset_frontier a b hab hshort)
    (standardMeridianBandCoordinates a b hab hshort)



theorem exists_sourceMeridianBand_parameter
    {α β : Type*}
    {e : α → OpenPartialHomeomorph X V3} {d : β → OpenPartialHomeomorph X V3}
    (hd : StandardLatticeHandleAtlas (Fin 1) (Fin 2) L d)
    (phi : C(H, H))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 1) (Fin 2) L phi))
    (F : (ContinuousMap.id H).HomotopyRel phi B)
    {c a b : ℝ} (ha : c < a) (hab : a < b) (hb : b < c + p)
    (hfront : frontier (sourceSlab phi a b) =
      (sourceSlab phi a b ∩ frontier R) ∪
        (sourceSurface phi (a : C) ∪ sourceSurface phi (b : C)))
    (A : ∀ theta ∈ ({(a : C), (b : C)} : Set C), Ann ≃ₜ sourceSurface phi theta)
    (qA : ∀ theta ∈ ({(a : C), (b : C)} : Set C), (ℝ × ℝ) → X)
    (hqA : ∀ theta htheta, PolyhedralPLInCharts e (qA theta htheta) Ann)
    (hA : ∀ theta htheta (z : Ann), (A theta htheta z : X) = qA theta htheta z)
    (E : frontier (sourceSlab phi a b) ≃ₜ frontier (sourceSlab (ContinuousMap.id H) a b))
    (hfix : ∀ x : frontier (sourceSlab phi a b), (x : X) ∈ frontier R → (E x : X) = x)
    (hphase : ∀ theta htheta (x : frontier (sourceSlab phi a b))
      (hx : (x : X) ∈ sourceSurface phi theta),
      (E x : X) = (standardTargetAnnulus theta ((A theta htheta).symm ⟨x, hx⟩) : X)) :
    ∃ q : (V2 × ℝ) → X, PolyhedralPLInCharts e q (Q ×ˢ I) ∧
      ∀ z : Q ×ˢ I, (sourceMeridianBandCylinder hab (by linarith) E z : X) = q z := by
  obtain ⟨K, hK, hKS⟩ := exists_finite_hamiltonMeridianBand
    (a := (-1 : ℝ)) (b := 1) (by norm_num)
  have hshort : b < a + p := by linarith
  have hqPL : PolyhedralPLInCharts d (standardMeridianBandParameter a b) K.space :=
    hKS.symm ▸ polyhedralPL_standardMeridianBandParameter hd a b
  have hqfront : MapsTo (standardMeridianBandParameter a b) K.space
      (frontier (sourceSlab (ContinuousMap.id H) a b)) := by
    intro z hz
    have hz' := hKS.subset hz
    exact mapsTo_standardMeridianBandParameter_frontier a b hab hshort
      ⟨hz'.1, mem_univ _⟩
  obtain ⟨q, hq, heq⟩ := exists_original_frontier_inverse_parameter
    hd phi hphi F ha hab hb hfront A qA hqA hA E hfix hphase
    K hK (standardMeridianBandParameter a b) hqPL hqfront
  refine ⟨q, hKS ▸ hq, ?_⟩
  intro z
  exact (heq z (hKS.symm.subset z.property)).symm




theorem exists_proper_sourceMeridianBand_disk
    {α : Type*} (e : α → OpenPartialHomeomorph X V3)
    (phi : C(H, H)) (F : (ContinuousMap.id H).HomotopyRel phi B)
    {a b : ℝ} (hab : a < b) (hshort : b < a + p)
    (hN : PLDomain e (sourceSlab phi a b))
    (hinj : ∀ x : sourceSlab phi a b, Function.Injective (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(sourceSlab phi a b, X)) x))
    (E : frontier (sourceSlab phi a b) ≃ₜ frontier (sourceSlab (ContinuousMap.id H) a b))
    (G : (phi.comp (slabFrontierHandleInclusion phi a b)).HomotopyRel
      ((slabFrontierHandleInclusion (ContinuousMap.id H) a b).comp ⟨E, E.continuous⟩)
      {x | (x : X) ∈ frontier R}) :
    ∃ (j : V2 → X)
      (rim : C(Q, cylinderBandInterior (sourceMeridianBandCylinder hab hshort E))),
      PolyhedralPLInCharts e j D ∧ Topology.IsEmbedding (fun x : D => j x) ∧
      MapsTo j D (sourceSlab phi a b) ∧ (∀ x : Q, j x = (rim x : X)) ∧
      (∀ x : D, j x ∈ frontier (sourceSlab phi a b) ↔ (x : V2) ∈ Q) ∧
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
        ((Dehn.squareRimLoop.map rim.continuous).map
          (ContinuousMap.inclusion
            (cylinderBandInterior_subset (sourceMeridianBandCylinder hab hshort E))).continuous)) ≠ 1 := by
  let : T2Space X := ((Homeomorph.refl (Fin 1 → ℝ)).prodCongr
    (hamiltonLowerLatticePiEquiv (Fin 2))).isEmbedding.t2Space
  refine exists_proper_disk_in_pulledBackBand e hN hinj E
    (slab_frontier_ambient_homotopic phi F a b E G)
    (standardMeridianBand_subset_frontier a b hab hshort)
    (standardMeridianBandCoordinates a b hab hshort) ?_
    (standardMeridianBandFilling a b hab hshort)
    (standardMeridianBandFilling_boundary a b hab hshort)
    (standardMeridianBandProjection a b hab hshort)
    (standardMeridianBandProjection_apply a b hab hshort)
  rw [standardMeridianBand_interior_eq]
  exact isOpen_standardMeridianOpenBand a b hab hshort

end PoincareConjecture.M76.HamiltonIntervalTorus
