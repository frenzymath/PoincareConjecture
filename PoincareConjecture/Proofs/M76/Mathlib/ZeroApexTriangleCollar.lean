import PoincareConjecture.Proofs.M76.Mathlib.TaperedTriangleDomain
import PoincareConjecture.Proofs.M76.Mathlib.AffineEdgeLevel
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLSubsets










set_option autoImplicit false

open Set Geometry

namespace AffineMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]




noncomputable def zeroApexCoordinates (A : E →ᵃ[ℝ] ℝ) (q w v : E) :
    (ℝ × ℝ) →ᴬ[ℝ] E :=
  ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (w - q) +
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (A.heightRay w v)).toContinuousAffineMap +
      ContinuousAffineMap.const ℝ (ℝ × ℝ) q



theorem zeroApexCoordinates_apply (A : E →ᵃ[ℝ] ℝ) (q w v : E) (p : ℝ × ℝ) :
    A.zeroApexCoordinates q w v p = p.1 • (w - q) + p.2 • A.heightRay w v + q := rfl



theorem apply_zeroApexCoordinates (A : E →ᵃ[ℝ] ℝ) {q w v : E}
    (hq : A q = 0) (hw : A w = 0) (hv : A v ≠ 0) (p : ℝ × ℝ) :
    A (A.zeroApexCoordinates q w v p) = p.2 := by
  have hvw : A v ≠ A w := by rwa [hw]
  have hbase : A.linear (w - q) = 0 := by
    have h := A.linearMap_vsub w q
    change A.linear (w - q) = A w - A q at h
    simpa only [hw, hq, sub_self] using h
  rw [zeroApexCoordinates_apply]
  change A ((p.1 • (w - q) + p.2 • A.heightRay w v) +ᵥ q) = p.2
  rw [map_vadd, map_add, map_smul, map_smul, hbase, linear_heightRay A hvw, hq]
  change p.1 * 0 + p.2 * 1 + 0 = p.2
  ring




theorem zeroApexCoordinates_injective (A : E →ᵃ[ℝ] ℝ) {q w v : E}
    (hqw : q ≠ w) (hq : A q = 0) (hw : A w = 0) (hv : A v ≠ 0) :
    Function.Injective (A.zeroApexCoordinates q w v) := by
  intro p z hpz
  have ht : p.2 = z.2 := by
    simpa only [apply_zeroApexCoordinates A hq hw hv] using congrArg A hpz
  rw [zeroApexCoordinates_apply, zeroApexCoordinates_apply, ht] at hpz
  have hs := add_right_cancel (add_right_cancel hpz)
  exact Prod.ext (smul_left_injective ℝ (sub_ne_zero.mpr hqw.symm) hs) ht



theorem zeroApexCoordinates_bottom (A : E →ᵃ[ℝ] ℝ) (q w v : E) (s : ℝ) :
    A.zeroApexCoordinates q w v (s, 0) = lineMap q w s := by
  rw [zeroApexCoordinates_apply, lineMap_apply_module']
  simp



theorem zeroApexCoordinates_side (A : E →ᵃ[ℝ] ℝ) (q w v : E)
    (hw : A w = 0) (t : ℝ) :
    A.zeroApexCoordinates q w v (1, t) = A.edgeLevel w v t := by
  rw [zeroApexCoordinates_apply, edgeLevel, hw]
  module




theorem zeroApexCoordinates_image (A : E →ᵃ[ℝ] ℝ) (q w v : E)
    (hw : A w = 0) {β : ℝ} (hβ : 0 < β) :
    A.zeroApexCoordinates q w v '' TaperedStrip.domain β =
      convexHull ℝ (insert q ({w, A.edgeLevel w v β} : Set E)) := by
  let F := A.zeroApexCoordinates q w v
  have h0 : F (0, 0) = q := by
    rw [zeroApexCoordinates_bottom, lineMap_apply_zero]
  have h1 : F (1, 0) = w := by
    rw [zeroApexCoordinates_bottom, lineMap_apply_one]
  have h2 : F (1, β) = A.edgeLevel w v β := A.zeroApexCoordinates_side q w v hw β
  change F.toAffineMap '' TaperedStrip.domain β = _
  rw [TaperedStrip.domain_eq_convexHull hβ, F.toAffineMap.image_convexHull]
  simp only [Matrix.range_cons, Matrix.range_empty, union_empty, singleton_union,
    image_insert_eq, image_singleton]
  change convexHull ℝ {F (0, 0), F (1, 0), F (1, β)} = _
  rw [h0, h1, h2]





theorem exists_zeroApex_tapered_collar (A : E →ᵃ[ℝ] ℝ) {q w v : E}
    (hqw : q ≠ w) (hq : A q = 0) (hw : A w = 0) (hv : A v ≠ 0)
    {β : ℝ} (hβ : 0 < β) :
    ∃ H : TaperedStrip.domain β ≃ₜ
        convexHull ℝ (insert q ({w, A.edgeLevel w v β} : Set E)),
      H.IsFinitePL ∧ (∀ p, (H p : E) = A.zeroApexCoordinates q w v p) ∧
        ∀ p, A (H p) = (p : ℝ × ℝ).2 := by
  obtain ⟨K, hK, hspace⟩ := TaperedStrip.exists_finite_triangulation hβ
  have hf : FinitePiecewiseAffineOn (A.zeroApexCoordinates q w v) (TaperedStrip.domain β) :=
    ⟨K, hK, hspace, K.affineOnFaces_affine _⟩
  obtain ⟨G, hG, hGval⟩ := hf.exists_homeomorph_image
    (A.zeroApexCoordinates_injective hqw hq hw hv).injOn
  let H := (Homeomorph.setCongr (rfl : TaperedStrip.domain β = TaperedStrip.domain β)).trans
    (G.trans (Homeomorph.setCongr (A.zeroApexCoordinates_image q w v hw hβ)))
  refine ⟨H, hG.setCongr rfl (A.zeroApexCoordinates_image q w v hw hβ), hGval, fun p => ?_⟩
  change A (G p) = (p : ℝ × ℝ).2
  rw [hGval]
  exact A.apply_zeroApexCoordinates hq hw hv p




theorem zeroApex_collar_subset_triangle (A : E →ᵃ[ℝ] ℝ) (q : E) {w v : E}
    (hw : A w = 0) (hv : 0 < A v) {β : ℝ} (hβ : 0 < β) (hβv : β ≤ A v) :
    convexHull ℝ (insert q ({w, A.edgeLevel w v β} : Set E)) ⊆
      convexHull ℝ (insert q ({w, v} : Set E)) := by
  have he : A.edgeLevel w v β ∈ segment ℝ w v := by
    rw [edgeLevel_eq_lineMap]
    apply lineMap_mem_segment
    rw [hw, sub_zero, sub_zero]
    exact ⟨div_nonneg hβ.le hv.le, (div_le_one hv).mpr hβv⟩
  apply convexHull_min ?_ (convex_convexHull ℝ _)
  intro x hx
  simp only [mem_insert_iff, mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · exact subset_convexHull ℝ _ (by simp)
  · exact subset_convexHull ℝ _ (by simp)
  · exact (convex_convexHull ℝ _).segment_subset
      (subset_convexHull ℝ _ (by simp)) (subset_convexHull ℝ _ (by simp)) he

end AffineMap
