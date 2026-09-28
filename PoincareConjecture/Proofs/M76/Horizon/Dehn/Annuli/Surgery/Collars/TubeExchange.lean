import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Resolution.TubeArmReindex

set_option autoImplicit false
open Set Geometry
open _root_.Dehn

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)



def pairedTubeExchange : C3 ≃L[ℝ] C3 :=
  ((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr (ContinuousLinearEquiv.neg ℝ)).prodCongr
    (ContinuousLinearEquiv.refl ℝ ℝ)

theorem pairedTubeExchange_apply (z : C3) :
    pairedTubeExchange z = ((z.1.1, -z.1.2), z.2) := rfl

theorem pairedTubeExchange_diagonal (k : Fin 2) (u t : ℝ) :
    pairedTubeExchange (sourceTubeDiagonal k u, t) = (sourceTubeDiagonal k.rev u, t) := by
  fin_cases k <;> simp [pairedTubeExchange_apply, sourceTubeDiagonal, Fin.rev]

theorem pairedTubeExchange_mem (L d : ℝ) (z : C3) :
    pairedTubeExchange z ∈ identityTube L d ↔ z ∈ identityTube L d := by
  simp only [pairedTubeExchange_apply, identityTube, mem_prod, mem_Icc]
  constructor <;> rintro ⟨⟨h0, h1⟩, h2⟩ <;>
    exact ⟨⟨h0, by constructor <;> linarith [h1.1, h1.2]⟩, h2⟩

theorem pairedTubeExchange_image (L d : ℝ) :
    pairedTubeExchange '' identityTube L d = identityTube L d := by
  apply Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact (pairedTubeExchange_mem L d z).mpr hz
  · intro z hz
    refine ⟨pairedTubeExchange z, (pairedTubeExchange_mem L d z).mpr hz, ?_⟩
    simp only [pairedTubeExchange_apply, neg_neg]


theorem pairedTubeExchange_map
    {F X ι : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [TopologicalSpace X]
    (e : ι → OpenPartialHomeomorph X F) {L d : ℝ} (hL : 0 < L) (hd : 0 < d)
    (τ : C3 → X) (hτ : PolyhedralPLInCharts e τ (identityTube L d))
    (hfib : ∀ z ∈ identityTube L d, ∀ w ∈ identityTube L d,
      τ z = τ w ↔ z.1 = w.1 ∧
        (z.2 : AddCircle (4 * L)) = (w.2 : AddCircle (4 * L))) :
    PolyhedralPLInCharts e (τ ∘ pairedTubeExchange) (identityTube L d) ∧
      (τ ∘ pairedTubeExchange) '' identityTube L d = τ '' identityTube L d ∧
      ∀ z ∈ identityTube L d, ∀ w ∈ identityTube L d,
        (τ ∘ pairedTubeExchange) z = (τ ∘ pairedTubeExchange) w ↔
          z.1 = w.1 ∧ (z.2 : AddCircle (4 * L)) = (w.2 : AddCircle (4 * L)) := by
  have hmap : MapsTo pairedTubeExchange (identityTube L d) (identityTube L d) :=
    fun z hz ↦ (pairedTubeExchange_mem L d z).mpr hz
  have hPL : PolyhedralPLInCharts e (τ ∘ pairedTubeExchange) (identityTube L d) := by
    have hI := isFinitePLBallPair_Icc (show -d < d by linarith)
    have hbox := (hI.prod hI).prod (isFinitePLBallPair_Icc (show 0 < 4 * L by positivity))
    obtain ⟨_, _, _, _, _, c, hc, _⟩ := hbox
    obtain ⟨_, ⟨K, hK, hKs, _⟩, _⟩ := hc
    have hp : FinitePiecewiseAffineOn pairedTubeExchange K.space :=
      ⟨K, hK, rfl, K.affineOnFaces_affine
        pairedTubeExchange.toContinuousLinearMap.toContinuousAffineMap⟩
    have hh := hτ.comp_finitePiecewiseAffineOn K hK hp
      (fun z hz ↦ hmap (hKs.subset hz))
    simpa only [identityTube, hKs] using hh
  refine ⟨hPL, ?_, ?_⟩
  · rw [image_comp, pairedTubeExchange_image]
  · intro z hz w hw
    change τ (pairedTubeExchange z) = τ (pairedTubeExchange w) ↔ _
    rw [hfib _ (hmap hz) _ (hmap hw)]
    simp only [pairedTubeExchange_apply, Prod.mk.injEq, neg_inj]
    rw [← Prod.ext_iff]

end PoincareConjecture.M76.Dehn.Annuli
