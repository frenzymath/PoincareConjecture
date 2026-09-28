import PoincareConjecture.Proofs.M47.LimitFinitePhysicalCoherence
import PoincareConjecture.Proofs.M47.LimitFiniteEndpointExtraction









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "V" => E →L[ℝ] E →L[ℝ] ℝ

private noncomputable local instance finiteEndpointCompatDualAdd :
    NormedAddCommGroup (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance finiteEndpointCompatDualSpace :
    NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
private noncomputable local instance finiteEndpointCompatBilinAdd :
    NormedAddCommGroup V := ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance finiteEndpointCompatBilinSpace :
    NormedSpace ℝ V := ContinuousLinearMap.toNormedSpace



theorem limitFinite_endpoint_physical_compatibility
    (F : ℕ → SurgeryFlowData.{u}) (C : GeneralizedSliceCarrier.{u})
    (origin Q b c : ℕ → ℝ) (U W : TopologicalSpace.Opens C.carrier)
    (e : ∀ k, SurgeryFlowCylinder (F k) C (origin k) (Q k) (Icc (b k) 0) U)
    (f : ∀ k, SurgeryFlowCylinder (F k) C (origin k) (Q k) (Icc (c k) 0) W)
    {t : ℝ} (ht : t ≤ 0) (htime : ∀ᶠ k in atTop, b k ≤ t ∧ c k ≤ t)
    (hzero : ∀ᶠ k in atTop,
      ∀ he0 : 0 ∈ Icc (b k) 0, ∀ hf0 : 0 ∈ Icc (c k) 0,
        ∀ x ∈ (U : Set C.carrier) ∩ W, (e k).forward 0 he0 x = (f k).forward 0 hf0 x)
    (g : ℕ → RiemannianMetric 3 U) (h : ℕ → RiemannianMetric 3 W)
    (hg : ∀ᶠ k in atTop, ∀ htk : t ∈ Icc (b k) 0,
      ∀ (x : U) (v w : TangentSpace (𝓡 3) x),
        (g k).inner x v w = (e k).pullbackInner t htk x.val
          (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) x v)
          (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) x w))
    (hh : ∀ᶠ k in atTop, ∀ htk : t ∈ Icc (c k) 0,
      ∀ (x : W) (v w : TangentSpace (𝓡 3) x),
        (h k).inner x v w = (f k).pullbackInner t htk x.val
          (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : W → C.carrier) x v)
          (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : W → C.carrier) x w))
    (Φ : PartialDiffeomorph (𝓡 3) (𝓡 3) E U ∞)
    (Ψ : PartialDiffeomorph (𝓡 3) (𝓡 3) E W ∞) (z w : E)
    (hpoint : (Φ z).val = (Ψ w).val) (v1 u1 v2 u2 : E)
    (hv : mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) (Φ z)
        (mfderiv (𝓡 3) (𝓡 3) Φ z v1) =
      mfderiv (𝓡 3) (𝓡 3) (Subtype.val : W → C.carrier) (Ψ w)
        (mfderiv (𝓡 3) (𝓡 3) Ψ w v2))
    (hu : mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) (Φ z)
        (mfderiv (𝓡 3) (𝓡 3) Φ z u1) =
      mfderiv (𝓡 3) (𝓡 3) (Subtype.val : W → C.carrier) (Ψ w)
        (mfderiv (𝓡 3) (𝓡 3) Ψ w u2))
    (B1 B2 : V)
    (hconv1 : ∀ v u, Tendsto (fun k => (g k).pullbackCoefficients Φ z v u)
      atTop (𝓝 (B1 v u)))
    (hconv2 : ∀ v u, Tendsto (fun k => (h k).pullbackCoefficients Ψ w v u)
      atTop (𝓝 (B2 v u))) :
    B1 v1 u1 = B2 v2 u2 := by
  have hpair : ∀ᶠ k in atTop,
      (g k).pullbackCoefficients Φ z v1 u1 = (h k).pullbackCoefficients Ψ w v2 u2 := by
    filter_upwards [htime, hzero, hg, hh] with k hk hz hkg hkh
    have hI : Icc t 0 ⊆ Icc (b k) 0 := Icc_subset_Icc hk.1 le_rfl
    have hJ : Icc t 0 ⊆ Icc (c k) 0 := Icc_subset_Icc hk.2 le_rfl
    have hx : (Φ z).val ∈ (U : Set C.carrier) ∩ W := by
      refine ⟨(Φ z).property, ?_⟩
      rw [hpoint]
      exact (Ψ w).property
    have heq := limitFinite_physical_pullback_eq (e k) (f k) U.isOpen W.isOpen ht hI hJ
      (hz _ _) hx
      (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) (Φ z)
        (mfderiv (𝓡 3) (𝓡 3) Φ z v1))
      (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) (Φ z)
        (mfderiv (𝓡 3) (𝓡 3) Φ z u1))
    have hleft := hkg ⟨hk.1, ht⟩ (Φ z)
      (mfderiv (𝓡 3) (𝓡 3) Φ z v1) (mfderiv (𝓡 3) (𝓡 3) Φ z u1)
    have hright := hkh ⟨hk.2, ht⟩ (Ψ w)
      (mfderiv (𝓡 3) (𝓡 3) Ψ w v2) (mfderiv (𝓡 3) (𝓡 3) Ψ w u2)
    change (g k).pullbackCoefficients Φ z v1 u1 = _ at hleft
    change (h k).pullbackCoefficients Ψ w v2 u2 = _ at hright
    apply hleft.trans
    apply heq.trans
    change (f k).pullbackInner t ⟨hk.2, ht⟩ (Φ z).val
      (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) (Φ z)
        (mfderiv (𝓡 3) (𝓡 3) Φ z v1))
      (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) (Φ z)
        (mfderiv (𝓡 3) (𝓡 3) Φ z u1)) = _
    rw [hv, hu, hpoint]
    exact hright.symm
  exact tendsto_nhds_unique (hconv1 v1 u1)
    ((hconv2 v2 u2).congr' (hpair.mono fun _ hk => hk.symm))

end PoincareConjecture.M47
