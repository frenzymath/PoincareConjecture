import PoincareConjecture.Proofs.M76.Mathlib.GeometricResidualTriangle
import PoincareConjecture.Proofs.M76.Mathlib.TaperedSourceIncidence










set_option autoImplicit false

open Set Geometry

namespace TaperedStrip




theorem mem_residualDomain_iff_of_mem_domain {β γ : ℝ}
    (hβ : 0 ≤ β) (hβγ : β ≤ γ) {p : ℝ × ℝ} (hp : p ∈ domain β) :
    p ∈ residualDomain β γ ↔ p.2 = β * p.1 := by
  constructor
  · intro hr
    exact le_antisymm hp.2.2 hr.2.1.1
  · intro ht
    refine ⟨hp.1, ⟨ht.ge, ?_⟩, ?_⟩
    · rw [ht]
      exact mul_le_of_le_one_right hβ hp.1.2
    · rw [ht]
      exact mul_le_mul_of_nonneg_right hβγ hp.1.1

end TaperedStrip

namespace AffineMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]




theorem zeroApexCoordinates_mem_residual_iff (A : E →ᵃ[ℝ] ℝ) {q w v : E}
    (hqw : q ≠ w) (hq : A q = 0) (hw : A w = 0)
    {β : ℝ} (hβ : 0 < β) (hβv : β < A v)
    {p : ℝ × ℝ} (hp : p ∈ TaperedStrip.domain β) :
    A.zeroApexCoordinates q w v p ∈
        convexHull ℝ (insert q ({A.edgeLevel w v β, A.edgeLevel q v β} : Set E)) ↔
      p.2 = β * p.1 := by
  rw [← A.zeroApexCoordinates_residual_image hq hw hβ hβv]
  have hinj := A.zeroApexCoordinates_injective hqw hq hw (hβ.trans hβv).ne'
  constructor
  · rintro ⟨z, hz, heq⟩
    have hzp : z = p := hinj heq
    exact (TaperedStrip.mem_residualDomain_iff_of_mem_domain hβ.le hβv.le hp).mp (hzp ▸ hz)
  · intro ht
    exact ⟨p, (TaperedStrip.mem_residualDomain_iff_of_mem_domain hβ.le hβv.le hp).mpr ht, rfl⟩




theorem geometric_collar_mem_residual_iff (A : E →ᵃ[ℝ] ℝ) {q w v : E}
    (hqw : q ≠ w) (hq : A q = 0) (hw : A w = 0)
    {β : ℝ} (hβ : 0 < β) (hβv : β < A v)
    (a : E →ᵃ[ℝ] ℝ) (haq : a q = 0) (haw : a w = β)
    {p : E × ℝ} (hp : p ∈ TaperedStrip.segmentDomain q w β) :
    p.1 + p.2 • A.heightRay w v ∈
        convexHull ℝ (insert q ({A.edgeLevel w v β, A.edgeLevel q v β} : Set E)) ↔
      p.2 = a p.1 := by
  obtain ⟨s, hs, hbase, ht⟩ := (TaperedStrip.mem_segmentDomain_iff hβ).mp hp
  have hcoord : A.zeroApexCoordinates q w v (s, p.2) =
      p.1 + p.2 • A.heightRay w v := by
    rw [zeroApexCoordinates_apply, hbase, lineMap_apply_module']
    module
  have hroof : a p.1 = β * s := by
    rw [hbase, a.apply_lineMap, haq, haw, lineMap_apply_module']
    simp [mul_comm]
  rw [← hcoord, A.zeroApexCoordinates_mem_residual_iff hqw hq hw hβ hβv
    (show (s, p.2) ∈ TaperedStrip.domain β from ⟨hs, ht⟩), hroof]

end AffineMap
