import PoincareConjecture.Proofs.M76.Mathlib.GeometricResidualTriangle
import PoincareConjecture.Proofs.M76.Mathlib.AffineHalfspaceSubcomplex











set_option autoImplicit false

open Set Geometry

namespace TaperedStrip




theorem exists_residual_finite_triangulation {β γ : ℝ} (hβ : 0 < β) (hβγ : β < γ) :
    ∃ K : SimplicialComplex ℝ (ℝ × ℝ), K.faces.Finite ∧ K.space = residualDomain β γ := by
  classical
  obtain ⟨K, hK, hKs⟩ := exists_finite_triangulation (hβ.trans hβγ)
  let X := (LinearMap.fst ℝ ℝ ℝ).toAffineMap
  let Y := (LinearMap.snd ℝ ℝ ℝ).toAffineMap
  let C : (ℝ × ℝ) →ᵃ[ℝ] ℝ := AffineMap.const ℝ (ℝ × ℝ) β
  obtain ⟨J, hJ, hJs⟩ := K.exists_finite_triangulation_inter_halfspaces hK {Y - C, β • X - Y}
  refine ⟨J, hJ, hJs.trans ?_⟩
  rw [hKs]
  ext p
  simp only [mem_inter_iff, mem_ofPred_eq, Finset.mem_insert, Finset.mem_singleton,
    forall_eq_or_imp, forall_eq]
  change ((p.1 ∈ Icc 0 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ γ * p.1) ∧
      p.2 - β ≤ 0 ∧ β * p.1 - p.2 ≤ 0) ↔
    (p.1 ∈ Icc 0 1 ∧ (β * p.1 ≤ p.2 ∧ p.2 ≤ β) ∧ p.2 ≤ γ * p.1)
  simp only [sub_nonpos]
  constructor
  · rintro ⟨⟨hs, _, hγ⟩, hi, hlo⟩
    exact ⟨hs, ⟨hlo, hi⟩, hγ⟩
  · rintro ⟨hs, ⟨hlo, hi⟩, hγ⟩
    exact ⟨⟨hs, (mul_nonneg hβ.le hs.1).trans hlo, hγ⟩, hi, hlo⟩

end TaperedStrip

namespace AffineMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]




theorem exists_zeroApex_residual_chart (A : E →ᵃ[ℝ] ℝ) {q w v : E}
    (hqw : q ≠ w) (hq : A q = 0) (hw : A w = 0)
    {β : ℝ} (hβ : 0 < β) (hβv : β < A v) :
    ∃ H : TaperedStrip.residualDomain β (A v) ≃ₜ
        convexHull ℝ (insert q ({A.edgeLevel w v β, A.edgeLevel q v β} : Set E)),
      H.IsFinitePL ∧ (∀ p, (H p : E) = A.zeroApexCoordinates q w v p) ∧
        ∀ p, A (H p) = (p : ℝ × ℝ).2 := by
  obtain ⟨K, hK, hKs⟩ := TaperedStrip.exists_residual_finite_triangulation hβ hβv
  have hf : FinitePiecewiseAffineOn (A.zeroApexCoordinates q w v)
      (TaperedStrip.residualDomain β (A v)) :=
    ⟨K, hK, hKs, K.affineOnFaces_affine _⟩
  obtain ⟨G, hG, hGval⟩ := hf.exists_homeomorph_image
    (A.zeroApexCoordinates_injective hqw hq hw (hβ.trans hβv).ne').injOn
  have himage := A.zeroApexCoordinates_residual_image hq hw hβ hβv
  let H := (Homeomorph.setCongr (rfl : TaperedStrip.residualDomain β (A v) =
    TaperedStrip.residualDomain β (A v))).trans (G.trans (Homeomorph.setCongr himage))
  refine ⟨H, hG.setCongr rfl himage, hGval, fun p => ?_⟩
  change A (G p) = (p : ℝ × ℝ).2
  rw [hGval]
  exact A.apply_zeroApexCoordinates hq hw (hβ.trans hβv).ne' p

end AffineMap
