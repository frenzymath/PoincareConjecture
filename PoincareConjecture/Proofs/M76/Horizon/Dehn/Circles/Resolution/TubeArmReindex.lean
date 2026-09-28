import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.IdentityAnnulus
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.PairedSourceAnnuli










set_option autoImplicit false

open Set Geometry

namespace Dehn

local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)


def pairedArmReindex (r₀ r₁ : Bool) : P2 ≃L[ℝ] P2 :=
  if r₀ then
    if r₁ then ContinuousLinearEquiv.neg ℝ else
      (ContinuousLinearEquiv.prodComm ℝ ℝ ℝ).trans (ContinuousLinearEquiv.neg ℝ)
  else if r₁ then ContinuousLinearEquiv.prodComm ℝ ℝ ℝ else ContinuousLinearEquiv.refl ℝ P2

theorem pairedArmReindex_diagonal (r₀ r₁ : Bool) (j : Fin 2) (u : ℝ) :
    pairedArmReindex r₀ r₁ (PoincareConjecture.M76.Dehn.sourceTubeDiagonal j u) =
      PoincareConjecture.M76.Dehn.sourceTubeDiagonal j
        (if (if j = 0 then r₀ else r₁) then -u else u) := by
  fin_cases j <;> cases r₀ <;> cases r₁ <;>
    simp [pairedArmReindex, PoincareConjecture.M76.Dehn.sourceTubeDiagonal]

theorem pairedArmReindex_involutive (r₀ r₁ : Bool) :
    Function.Involutive (pairedArmReindex r₀ r₁) := by
  intro p
  cases r₀ <;> cases r₁ <;> ext <;> simp [pairedArmReindex]

theorem pairedArmReindex_mem_square (r₀ r₁ : Bool) (d : ℝ) (p : P2) :
    pairedArmReindex r₀ r₁ p ∈ Icc (-d) d ×ˢ Icc (-d) d ↔
      p ∈ Icc (-d) d ×ˢ Icc (-d) d := by
  cases r₀ <;> cases r₁ <;>
    simp only [pairedArmReindex, Bool.false_eq_true, if_false, if_true,
      ContinuousLinearEquiv.refl_apply, ContinuousLinearEquiv.trans_apply,
      ContinuousLinearEquiv.prodComm_apply, ContinuousLinearEquiv.neg_apply,
      mem_prod, mem_Icc, Prod.fst_neg, Prod.snd_neg, Prod.fst_swap, Prod.snd_swap] <;>
    constructor <;> intro h <;>
    constructor <;> constructor <;> linarith [h.1.1, h.1.2, h.2.1, h.2.2]


def pairedTubeReindex (r₀ r₁ : Bool) : C3 ≃L[ℝ] C3 :=
  (pairedArmReindex r₀ r₁).prodCongr (ContinuousLinearEquiv.refl ℝ ℝ)

theorem pairedTubeReindex_mem (r₀ r₁ : Bool) (L d : ℝ) (z : C3) :
    pairedTubeReindex r₀ r₁ z ∈ identityTube L d ↔ z ∈ identityTube L d := by
  change (pairedArmReindex r₀ r₁ z.1 ∈ Icc (-d) d ×ˢ Icc (-d) d ∧
    z.2 ∈ Icc 0 (4 * L)) ↔ _
  rw [pairedArmReindex_mem_square]
  rfl

theorem pairedTubeReindex_image (r₀ r₁ : Bool) (L d : ℝ) :
    pairedTubeReindex r₀ r₁ '' identityTube L d = identityTube L d := by
  apply Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact (pairedTubeReindex_mem r₀ r₁ L d z).mpr hz
  · intro z hz
    refine ⟨pairedTubeReindex r₀ r₁ z, (pairedTubeReindex_mem r₀ r₁ L d z).mpr hz, ?_⟩
    exact Prod.ext (pairedArmReindex_involutive r₀ r₁ z.1) rfl



theorem pairedTubeReindex_map
    {F X ι : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [TopologicalSpace X]
    (e : ι → OpenPartialHomeomorph X F) {L d : ℝ} (hL : 0 < L) (hd : 0 < d)
    (r₀ r₁ : Bool)
    (τ : C3 → X) (hτ : PolyhedralPLInCharts e τ (identityTube L d))
    (hfib : ∀ z ∈ identityTube L d, ∀ w ∈ identityTube L d,
      τ z = τ w ↔ z.1 = w.1 ∧
        (z.2 : AddCircle (4 * L)) = (w.2 : AddCircle (4 * L))) :
    PolyhedralPLInCharts e (τ ∘ pairedTubeReindex r₀ r₁) (identityTube L d) ∧
      (τ ∘ pairedTubeReindex r₀ r₁) '' identityTube L d = τ '' identityTube L d ∧
      ∀ z ∈ identityTube L d, ∀ w ∈ identityTube L d,
        (τ ∘ pairedTubeReindex r₀ r₁) z = (τ ∘ pairedTubeReindex r₀ r₁) w ↔
          z.1 = w.1 ∧ (z.2 : AddCircle (4 * L)) = (w.2 : AddCircle (4 * L)) := by
  have hmap : MapsTo (pairedTubeReindex r₀ r₁) (identityTube L d) (identityTube L d) :=
    fun z hz ↦ (pairedTubeReindex_mem r₀ r₁ L d z).mpr hz
  have hPL : PolyhedralPLInCharts e (τ ∘ pairedTubeReindex r₀ r₁) (identityTube L d) := by
    have hI := isFinitePLBallPair_Icc (show -d < d by linarith)
    have hbox := (hI.prod hI).prod (isFinitePLBallPair_Icc (show 0 < 4 * L by positivity))
    obtain ⟨_, _, _, _, _, c, hc, _⟩ := hbox
    obtain ⟨_, ⟨K, hK, hKs, _⟩, _⟩ := hc
    have hp : FinitePiecewiseAffineOn (pairedTubeReindex r₀ r₁) K.space :=
      ⟨K, hK, rfl, K.affineOnFaces_affine
        (pairedTubeReindex r₀ r₁).toContinuousLinearMap.toContinuousAffineMap⟩
    have hh := hτ.comp_finitePiecewiseAffineOn K hK hp
      (fun z hz ↦ hmap (hKs.subset hz))
    simpa only [identityTube, hKs] using hh
  refine ⟨hPL, ?_, ?_⟩
  · rw [image_comp, pairedTubeReindex_image]
  · intro z hz w hw
    change τ (pairedTubeReindex r₀ r₁ z) = τ (pairedTubeReindex r₀ r₁ w) ↔ _
    rw [hfib _ (hmap hz) _ (hmap hw)]
    change (pairedArmReindex r₀ r₁ z.1 = pairedArmReindex r₀ r₁ w.1 ∧ _) ↔ _
    rw [(pairedArmReindex r₀ r₁).injective.eq_iff]
    rfl

end Dehn
