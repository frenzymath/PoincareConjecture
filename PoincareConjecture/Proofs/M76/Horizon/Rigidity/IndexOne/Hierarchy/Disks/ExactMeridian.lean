import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Hierarchy.Bands.Source
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Hierarchy.Bands.FiniteCollar

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

theorem exists_exact_source_slab_meridian
    {α β : Type*}
    {e : α → OpenPartialHomeomorph X V3} {d : β → OpenPartialHomeomorph X V3}
    (hd : StandardLatticeHandleAtlas (Fin 1) (Fin 2) L d)
    (phi : C(H, H))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 1) (Fin 2) L phi))
    (F : (ContinuousMap.id H).HomotopyRel phi B)
    {c a b : ℝ} (ha : c < a) (hab : a < b) (hb : b < c + p)
    (hN : PLDomain e (sourceSlab phi a b))
    (hinj : ∀ x : sourceSlab phi a b, Function.Injective (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(sourceSlab phi a b, X)) x))
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
      (E x : X) = (standardTargetAnnulus theta ((A theta htheta).symm ⟨x, hx⟩) : X))
    (G : (phi.comp (slabFrontierHandleInclusion phi a b)).HomotopyRel
      ((slabFrontierHandleInclusion (ContinuousMap.id H) a b).comp ⟨E, E.continuous⟩)
      {x | (x : X) ∈ frontier R}) :
    ∃ (q : (V2 × ℝ) → X) (j : V2 → X),
      PolyhedralPLInCharts e q (Q ×ˢ I) ∧
      (∀ z : Q ×ˢ I, (sourceMeridianBandCylinder hab (by linarith) E z : X) = q z) ∧
      PolyhedralPLInCharts e j D ∧ Topology.IsEmbedding (fun z : D => j z) ∧
      MapsTo j D (sourceSlab phi a b) ∧
      (∀ z : D, j z ∈ frontier (sourceSlab phi a b) ↔ (z : V2) ∈ Q) ∧
      ∀ z : Q, j z = (cylinderZeroSection
        (sourceMeridianBandCylinder hab (by linarith) E) z : X) := by
  let : T2Space X := ((Homeomorph.refl (Fin 1 → ℝ)).prodCongr
    (hamiltonLowerLatticePiEquiv (Fin 2))).isEmbedding.t2Space
  have hshort : b < a + p := by linarith
  obtain ⟨q, hq, hcq⟩ := exists_sourceMeridianBand_parameter
    hd phi hphi F ha hab hb hfront A qA hqA hA E hfix hphase
  obtain ⟨j, rim, hj, hji, hjN, hjrim, _, hess⟩ :=
    exists_proper_sourceMeridianBand_disk e phi F hab hshort hN hinj E G
  obtain ⟨j', hj', hi', hmap', hproper', hrim'⟩ :=
    exists_exact_proper_disk_of_original_cylindrical_band hN
      (sourceSlab_isCompact phi a b) (sourceMeridianBandCylinder hab hshort E)
      (frontierBandPullback_subset E) q hq hcq j hj hji hjN rim hjrim hess
  exact ⟨q, j', hq, hcq, hj', hi', hmap', hproper', hrim'⟩

end PoincareConjecture.M76.HamiltonIntervalTorus
