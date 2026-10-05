import PoincareLib.Geometry.RicciFlow.Blowup.Controlled.Data
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.EpochExtension.Spacetime.GeneralizedCylinderRestriction

/-!
# Restricting the cylinders of Chapter 11

Morgan--Tian Definition 3.38, p. 61, and Theorem 11.8, p. 272: a compatible
cylinder restricts to smaller space and time domains. The total maps are
unchanged, and a closed backward slab is taken strictly inside an open-left
slab. This is data restriction; endpoint metric jets are a later obligation.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT.M30

namespace Cylinder

variable {F : GeneralizedRicciFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
  {origin scale : ℝ} {I J : Set ℝ} {U V : Set C.carrier}

/-- Restrict a compatible cylinder, preserving both total maps (Definition
3.38, p. 61). This reuses M12's raw-cylinder restriction. -/
noncomputable def restrict
    (e : GeneralizedFlowCylinder F C origin scale I U)
    (hJI : J ⊆ I) (hVU : V ⊆ U) :
    GeneralizedFlowCylinder F C origin scale J V :=
  e.restrict hJI hVU

/-- Restriction preserves the actual spacetime point (Definition 3.38, p. 61). -/
@[simp] theorem restrict_pointMap
    (e : GeneralizedFlowCylinder F C origin scale I U)
    (hJI : J ⊆ I) (hVU : V ⊆ U) (s : ℝ) (hs : s ∈ J) (x : C.carrier) :
    (restrict e hJI hVU).pointMap s hs x = e.pointMap s (hJI hs) x := rfl

/-- Restriction preserves the pullback metric because it reuses the total
spatial maps (Definition 3.38, p. 61; Definition 5.12, p. 90). -/
@[simp] theorem restrict_pullbackInner
    (e : GeneralizedFlowCylinder F C origin scale I U)
    (hJI : J ⊆ I) (hVU : V ⊆ U) (s : ℝ) (hs : s ∈ J) (x : C.carrier)
    (v w : TangentSpace (𝓡 3) x) :
    (restrict e hJI hVU).pullbackInner s hs x v w =
      e.pullbackInner s (hJI hs) x v w := rfl

end Cylinder

/-- A strictly shorter closed slab lies inside the slab of Theorem 11.8,
p. 272. Positivity is needed separately to use it as a nontrivial flow. -/
theorem closedSlab_subset_openSlab {T' T : ℝ} (h : T' < T) :
    Set.Icc (-T') 0 ⊆ Set.Ioc (-T) 0 := by
  intro t ht
  exact ⟨(neg_lt_neg h).trans_le ht.1, ht.2⟩

namespace FiniteHorizonSlab

variable {S : GeneralizedBlowupSequence.{u}} {k : ℕ} {A T kappa r₀ : ℝ}

/-- Theorem 11.8's open-left slab supplies its closed subslab with exactly
the same total maps (p. 272; Definition 5.12, p. 90). -/
noncomputable def closedEmbedding (e : M30FiniteHorizonSlab S k A T kappa r₀)
    {T' : ℝ} (h : T' < T) :
    GeneralizedFlowCylinder (S.flow k) ((S.flow k).slice (S.base k).1)
      (S.base k).1 (S.scale k) (Set.Icc (-T') 0) (S.baseBall k A) :=
  Cylinder.restrict e.embedding (closedSlab_subset_openSlab h) Set.Subset.rfl

/-- The restricted slab retains its terminal identity (Theorem 11.8, p. 272). -/
theorem closedEmbedding_zero_identity (e : M30FiniteHorizonSlab S k A T kappa r₀)
    {T' : ℝ} (h : T' < T) (h₀ : 0 ∈ Set.Icc (-T') 0)
    (x : ((S.flow k).slice (S.base k).1).carrier) (hx : x ∈ S.baseBall k A) :
    (closedEmbedding e h).pointMap 0 h₀ x =
      (⟨(S.base k).1, x⟩ : (S.flow k).point) :=
  e.zero_identity _ x hx

/-- Pointwise original-scale noncollapse survives slab restriction
(Theorem 11.8, p. 272). -/
theorem closedEmbedding_noncollapsed (e : M30FiniteHorizonSlab S k A T kappa r₀)
    {T' : ℝ} (h : T' < T) (s : ℝ) (hs : s ∈ Set.Icc (-T') 0)
    (x : ((S.flow k).slice (S.base k).1).carrier) (hx : x ∈ S.baseBall k A) :
    GeneralizedKappaNoncollapsedAt (S.flow k)
      ((closedEmbedding e h).pointMap s hs x) kappa r₀ :=
  e.noncollapsed s _ x hx

end FiniteHorizonSlab

end PoincareMT.M30
