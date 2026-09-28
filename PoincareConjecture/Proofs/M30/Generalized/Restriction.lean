import PoincareConjecture.Definitions.M30ControlledBlowupLimits
import PoincareConjecture.Proofs.M12.GeneralizedCylinderRestriction

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M30

namespace Cylinder

variable {F : GeneralizedRicciFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
  {origin scale : ℝ} {I J : Set ℝ} {U V : Set C.carrier}

noncomputable def restrict
    (e : GeneralizedFlowCylinder F C origin scale I U)
    (hJI : J ⊆ I) (hVU : V ⊆ U) :
    GeneralizedFlowCylinder F C origin scale J V :=
  e.restrict hJI hVU

@[simp] theorem restrict_pointMap
    (e : GeneralizedFlowCylinder F C origin scale I U)
    (hJI : J ⊆ I) (hVU : V ⊆ U) (s : ℝ) (hs : s ∈ J) (x : C.carrier) :
    (restrict e hJI hVU).pointMap s hs x = e.pointMap s (hJI hs) x := rfl

@[simp] theorem restrict_pullbackInner
    (e : GeneralizedFlowCylinder F C origin scale I U)
    (hJI : J ⊆ I) (hVU : V ⊆ U) (s : ℝ) (hs : s ∈ J) (x : C.carrier)
    (v w : TangentSpace (𝓡 3) x) :
    (restrict e hJI hVU).pullbackInner s hs x v w =
      e.pullbackInner s (hJI hs) x v w := rfl

end Cylinder

theorem closedSlab_subset_openSlab {T' T : ℝ} (h : T' < T) :
    Set.Icc (-T') 0 ⊆ Set.Ioc (-T) 0 := by
  intro t ht
  exact ⟨(neg_lt_neg h).trans_le ht.1, ht.2⟩

namespace FiniteHorizonSlab

variable {S : GeneralizedBlowupSequence.{u}} {k : ℕ} {A T kappa r₀ : ℝ}

noncomputable def closedEmbedding (e : M30FiniteHorizonSlab S k A T kappa r₀)
    {T' : ℝ} (h : T' < T) :
    GeneralizedFlowCylinder (S.flow k) ((S.flow k).slice (S.base k).1)
      (S.base k).1 (S.scale k) (Set.Icc (-T') 0) (S.baseBall k A) :=
  Cylinder.restrict e.embedding (closedSlab_subset_openSlab h) Set.Subset.rfl

theorem closedEmbedding_zero_identity (e : M30FiniteHorizonSlab S k A T kappa r₀)
    {T' : ℝ} (h : T' < T) (h₀ : 0 ∈ Set.Icc (-T') 0)
    (x : ((S.flow k).slice (S.base k).1).carrier) (hx : x ∈ S.baseBall k A) :
    (closedEmbedding e h).pointMap 0 h₀ x =
      (⟨(S.base k).1, x⟩ : (S.flow k).point) :=
  e.zero_identity _ x hx

theorem closedEmbedding_noncollapsed (e : M30FiniteHorizonSlab S k A T kappa r₀)
    {T' : ℝ} (h : T' < T) (s : ℝ) (hs : s ∈ Set.Icc (-T') 0)
    (x : ((S.flow k).slice (S.base k).1).carrier) (hx : x ∈ S.baseBall k A) :
    GeneralizedKappaNoncollapsedAt (S.flow k)
      ((closedEmbedding e h).pointMap s hs x) kappa r₀ :=
  e.noncollapsed s _ x hx

end FiniteHorizonSlab

end PoincareConjecture.M30
