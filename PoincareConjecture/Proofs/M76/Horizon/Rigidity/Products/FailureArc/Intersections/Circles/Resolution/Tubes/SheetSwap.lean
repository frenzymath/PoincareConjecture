import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Circles.Resolution.Tubes.OriginalCollars

set_option autoImplicit false
open Set Geometry Topology PLAnnularStrip _root_.Dehn

namespace PoincareConjecture.M76.Dehn.Annuli.CircleResolution

local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)

def circleSheetSwap : C3 ≃L[ℝ] C3 :=
  ((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr (ContinuousLinearEquiv.neg ℝ)).prodCongr
    (ContinuousLinearEquiv.refl ℝ ℝ)

theorem circleSheetSwap_apply (z : C3) : circleSheetSwap z = ((z.1.1,-z.1.2),z.2) := rfl

theorem circleSheetSwap_mem (L d : ℝ) (z : C3) :
    circleSheetSwap z ∈ identityTube L d ↔ z ∈ identityTube L d := by
  change ((-d ≤ z.1.1 ∧ z.1.1 ≤ d) ∧ (-d ≤ -z.1.2 ∧ -z.1.2 ≤ d)) ∧
    (0 ≤ z.2 ∧ z.2 ≤ 4 * L) ↔ _
  simp only [identityTube,mem_prod,mem_Icc]
  constructor <;> intro h <;> exact ⟨⟨h.1.1,⟨by linarith [h.1.2.2],by linarith [h.1.2.1]⟩⟩,h.2⟩

theorem circleSheetSwap_image (L d : ℝ) :
    circleSheetSwap '' identityTube L d = identityTube L d := by
  apply Subset.antisymm
  · rintro _ ⟨z,hz,rfl⟩
    exact (circleSheetSwap_mem L d z).mpr hz
  · intro z hz
    refine ⟨circleSheetSwap z,(circleSheetSwap_mem L d z).mpr hz,?_⟩
    simp only [circleSheetSwap_apply,neg_neg]

theorem circleSheetSwap_map
    {F X ι : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [TopologicalSpace X]
    (e : ι → OpenPartialHomeomorph X F) {L d : ℝ} (hL : 0 < L) (hd : 0 < d)
    (τ : C3 → X) (hτ : PolyhedralPLInCharts e τ (identityTube L d))
    (hfib : ∀ z ∈ identityTube L d, ∀ w ∈ identityTube L d,
      τ z = τ w ↔ z.1 = w.1 ∧
        (z.2 : AddCircle (4 * L)) = (w.2 : AddCircle (4 * L))) :
    PolyhedralPLInCharts e (τ ∘ circleSheetSwap) (identityTube L d) ∧
      (τ ∘ circleSheetSwap) '' identityTube L d = τ '' identityTube L d ∧
      ∀ z ∈ identityTube L d, ∀ w ∈ identityTube L d,
        (τ ∘ circleSheetSwap) z = (τ ∘ circleSheetSwap) w ↔
          z.1 = w.1 ∧ (z.2 : AddCircle (4 * L)) = (w.2 : AddCircle (4 * L)) := by
  have hmap : MapsTo circleSheetSwap (identityTube L d) (identityTube L d) :=
    fun z hz => (circleSheetSwap_mem L d z).mpr hz
  have hPL : PolyhedralPLInCharts e (τ ∘ circleSheetSwap) (identityTube L d) := by
    have hI := isFinitePLBallPair_Icc (show -d < d by linarith)
    have hbox := (hI.prod hI).prod (isFinitePLBallPair_Icc (show 0 < 4 * L by positivity))
    obtain ⟨_,_,_,_,_,c,hc,_⟩ := hbox
    obtain ⟨_,⟨K,hK,hKs,_⟩,_⟩ := hc
    have hp : FinitePiecewiseAffineOn circleSheetSwap K.space :=
      ⟨K,hK,rfl,K.affineOnFaces_affine circleSheetSwap.toContinuousLinearMap.toContinuousAffineMap⟩
    have hh := hτ.comp_finitePiecewiseAffineOn K hK hp (fun z hz => hmap (hKs.subset hz))
    simpa only [identityTube,hKs] using hh
  refine ⟨hPL,?_,?_⟩
  · rw [image_comp,circleSheetSwap_image]
  · intro z hz w hw
    change τ (circleSheetSwap z) = τ (circleSheetSwap w) ↔ _
    rw [hfib _ (hmap hz) _ (hmap hw)]
    change (((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr
      (ContinuousLinearEquiv.neg ℝ)) z.1 =
      ((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr (ContinuousLinearEquiv.neg ℝ)) w.1 ∧ _) ↔ _
    rw [((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr (ContinuousLinearEquiv.neg ℝ)).injective.eq_iff]
    rfl

end PoincareConjecture.M76.Dehn.Annuli.CircleResolution
