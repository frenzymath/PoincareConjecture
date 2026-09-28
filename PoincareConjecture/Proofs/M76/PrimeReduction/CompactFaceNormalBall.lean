import PoincareConjecture.Proofs.M76.PrimeReduction.CompactFaceNormalProduct
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseProductBall
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallTopology
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages
import PoincareConjecture.Proofs.M76.Mathlib.UnitBallPairs










set_option autoImplicit false

open Set Geometry

namespace OpenPartialHomeomorph

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace X]





theorem exists_compact_face_normal_ball
    (B : OpenPartialHomeomorph X E)
    (T : ((ℝ × ℝ) × ℝ) ≃ᴬ[ℝ] E)
    {D rim : Set (ℝ × ℝ)} (hD : IsFinitePLBallPair (ℝ × ℝ) D rim)
    {U : Set X} (hU : IsOpen U)
    (hzero : ∀ z ∈ D, T (z, 0) ∈ B.target ∧ B.symm (T (z, 0)) ∈ U) :
    ∃ r : ℝ, 0 < r ∧
      let S := D ×ˢ Icc (-r) r
      let bd := (rim ×ˢ Icc (-r) r) ∪ (D ×ˢ {-r, r})
      let j := B.symm ∘ T
      ∃ H : S ≃ₜ j '' S,
        MapsTo T S B.target ∧ (∀ x : S, (H x : X) = j x) ∧
        (∀ y : j '' S, (H.symm y : (ℝ × ℝ) × ℝ) = T.symm (B y)) ∧
        j '' S ⊆ U ∧ IsCompact (j '' S) ∧
        IsFinitePLBallPair ((ℝ × ℝ) × ℝ) S bd ∧
        IsFinitePLBallPair ((ℝ × ℝ) × ℝ) (T '' S) (T '' bd) ∧
        IsUnitBallPair ((ℝ × ℝ) × ℝ) (j '' S) (j '' bd) ∧
        ∀ x : S, (H x : X) ∈ j '' (D ×ˢ {(0 : ℝ)}) ↔ (x : (ℝ × ℝ) × ℝ).2 = 0 := by
  obtain ⟨r, hr, hT, hmap, _, hi, hc, hinverse, hcentral⟩ :=
    B.exists_compact_face_normal_product T hD.isCompact hU hzero
  let S := D ×ˢ Icc (-r) r
  let bd := (rim ×ˢ Icc (-r) r) ∪ (D ×ˢ {-r, r})
  let j := B.symm ∘ T
  let P := T.toHomeomorph.toOpenPartialHomeomorph.trans B.symm
  have hSP : S ⊆ P.source := fun x hx => ⟨mem_univ _, hT hx⟩
  let H : S ≃ₜ j '' S := P.homeomorphOfImageSubsetSource hSP rfl
  have hH (x : S) : (H x : X) = j x := rfl
  have hHinv (y : j '' S) : (H.symm y : (ℝ × ℝ) × ℝ) = T.symm (B y) := by
    have hv : j (H.symm y) = (y : X) :=
      (hH (H.symm y)).symm.trans (congrArg Subtype.val (H.apply_symm_apply y))
    have hz := hinverse (H.symm y) (H.symm y).property
    change T.symm (B (j (H.symm y))) = (H.symm y : (ℝ × ℝ) × ℝ) at hz
    rw [hv] at hz
    exact hz.symm
  have hprod : IsFinitePLBallPair ((ℝ × ℝ) × ℝ) S bd :=
    hD.prod (isFinitePLBallPair_Icc (show -r < r by linarith))
  have hchart := hprod.affine_image T.toContinuousAffineMap T.injective.injOn
  have hunit : IsUnitBallPair ((ℝ × ℝ) × ℝ) S bd := by
    obtain ⟨hb, C, hC, hcv, hne, G, _, hGb⟩ := hprod
    exact (isUnitBallPair_of_compact_convex hC hcv hne).of_homeomorph hb G hGb
  have hmarked (x : S) : (H x : X) ∈ j '' bd ↔ (x : (ℝ × ℝ) × ℝ) ∈ bd := by
    rw [hH]
    constructor
    · rintro ⟨y, hy, heq⟩
      have hyx : y = (x : (ℝ × ℝ) × ℝ) := hi (hprod.1 hy) x.property heq
      exact hyx ▸ hy
    · exact fun hx => ⟨x, hx, rfl⟩
  have himage : IsUnitBallPair ((ℝ × ℝ) × ℝ) (j '' S) (j '' bd) := by
    apply hunit.of_homeomorph (image_mono hprod.1) H.symm
    intro y
    have h := hmarked (H.symm y)
    rw [H.apply_symm_apply] at h
    exact h
  refine ⟨r, hr, H, hT, hH, hHinv, image_subset_iff.mpr hmap, hc,
    hprod, hchart, himage, ?_⟩
  intro x
  rw [hH]
  exact hcentral x x.property

end OpenPartialHomeomorph
