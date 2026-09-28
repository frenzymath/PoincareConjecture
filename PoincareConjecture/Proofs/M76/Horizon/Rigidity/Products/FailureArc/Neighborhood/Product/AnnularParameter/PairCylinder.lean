import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.AnnularParameter.PairCoordinates
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.AnnularParameter.SourceCylinder

set_option autoImplicit false
noncomputable section
open Set Metric Geometry

namespace PoincareConjecture.M76.Dehn.Annuli.AnnularParameter

local notation "V2" => (Fin 2 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "I" => Icc (0 : ℝ) 1
local notation "RimV" => sphere (0 : V2) 1
local notation "RimP" => sphere (0 : P2) 1

def pairCylinderCoordinates : (P2 × ℝ) ≃L[ℝ] (V2 × ℝ) :=
  pairCoordinates.symm.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ)

theorem pairCylinderCoordinates_image :
    pairCylinderCoordinates.symm '' (RimV ×ˢ I) = RimP ×ˢ I := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨(pairCoordinates_rim q.1).mp hq.1, hq.2⟩
  · intro hp
    refine ⟨pairCylinderCoordinates p, ?_, pairCylinderCoordinates.symm_apply_apply p⟩
    refine ⟨(pairCoordinates_rim _).mpr ?_, hp.2⟩
    simpa [pairCylinderCoordinates] using hp.1

theorem pairCylinderCoordinates_finitePL :
    FinitePiecewiseAffineOn pairCylinderCoordinates (RimP ×ˢ I) := by
  obtain ⟨C, hC, _⟩ := exists_source_cylinder
  obtain ⟨v, hv, _⟩ := hC.symm
  obtain ⟨K, hK, hKs, _⟩ := hv
  have hid : FinitePiecewiseAffineOn (id : V2 × ℝ → V2 × ℝ) (RimV ×ˢ I) :=
    ⟨K, hK, hKs, K.affineOnFaces_affine (ContinuousAffineMap.id ℝ (V2 × ℝ))⟩
  have h := hid.precomp_affineEquiv pairCylinderCoordinates.toContinuousAffineEquiv
  change FinitePiecewiseAffineOn pairCylinderCoordinates
    (pairCylinderCoordinates.symm '' (RimV ×ˢ I)) at h
  rwa [pairCylinderCoordinates_image] at h

def pairCylinder {X : Type*} (b : V2 × ℝ → X) : P2 × ℝ → X :=
  b ∘ pairCylinderCoordinates

theorem pairCylinder_match {X : Type*} (b : V2 × ℝ → X) (z : V2) (t : ℝ) :
    pairCylinder b (pairCoordinates z, t) = b (z, t) := by
  simp [pairCylinder, pairCylinderCoordinates]

theorem pairCylinder_properties
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {b : V2 × ℝ → X}
    (hb : PolyhedralPLInCharts e b (RimV ×ˢ I))
    (hbi : InjOn b (RimV ×ˢ I)) :
    PolyhedralPLInCharts e (pairCylinder b) (RimP ×ˢ I) ∧
      InjOn (pairCylinder b) (RimP ×ˢ I) ∧
      pairCylinder b '' (RimP ×ˢ I) = b '' (RimV ×ˢ I) ∧
      ∀ t : ℝ, pairCylinder b '' (RimP ×ˢ {t}) = b '' (RimV ×ˢ {t}) := by
  have hmap : MapsTo pairCylinderCoordinates (RimP ×ˢ I) (RimV ×ˢ I) := by
    intro p hp
    refine ⟨(pairCoordinates_rim _).mpr ?_, hp.2⟩
    simpa [pairCylinderCoordinates] using hp.1
  have hpl := pairCylinderCoordinates_finitePL
  obtain ⟨K, hK, hKs, _⟩ := hpl
  refine ⟨?_, hbi.comp pairCylinderCoordinates.injective.injOn hmap, ?_, ?_⟩
  · exact hKs ▸ hb.comp_finitePiecewiseAffineOn K hK
      (hKs.symm ▸ pairCylinderCoordinates_finitePL)
      (fun p hp => hmap (hKs.subset hp))
  · rw [← pairCylinderCoordinates_image, image_image]
    congr 1
    funext p
    exact congrArg b (pairCylinderCoordinates.apply_symm_apply p)
  · intro t
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      refine ⟨pairCylinderCoordinates p, ⟨?_, hp.2⟩, rfl⟩
      apply (pairCoordinates_rim _).mpr
      simpa [pairCylinderCoordinates] using hp.1
    · rintro ⟨p, hp, rfl⟩
      refine ⟨(pairCoordinates p.1, p.2),
        ⟨(pairCoordinates_rim p.1).mp hp.1, hp.2⟩, ?_⟩
      exact pairCylinder_match b p.1 p.2

end PoincareConjecture.M76.Dehn.Annuli.AnnularParameter
