import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Resolution.TubeArmReindex









set_option autoImplicit false

open Set Geometry

namespace Dehn

local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)

def nestedArmReindex (j : Fin 2) : P2 ≃L[ℝ] P2 :=
  if j = 0 then
    (ContinuousLinearEquiv.refl ℝ ℝ).prodCongr (ContinuousLinearEquiv.neg ℝ)
  else ContinuousLinearEquiv.refl ℝ P2

def nestedTubeReindex (j : Fin 2) : C3 ≃L[ℝ] C3 :=
  (nestedArmReindex j).prodCongr (ContinuousLinearEquiv.refl ℝ ℝ)

theorem nestedTubeReindex_corners (j : Fin 2) (d s : ℝ) :
    nestedTubeReindex j ((-d, d), s) =
      (PoincareConjecture.M76.Dehn.sourceTubeDiagonal j (-d), s) ∧
    nestedTubeReindex j ((d, d), s) =
      (PoincareConjecture.M76.Dehn.sourceTubeDiagonal j.rev d, s) := by
  fin_cases j <;>
    simp [nestedTubeReindex, nestedArmReindex, PoincareConjecture.M76.Dehn.sourceTubeDiagonal]

theorem nestedTubeReindex_mem (j : Fin 2) (L d : ℝ) (z : C3) :
    nestedTubeReindex j z ∈ identityTube L d ↔ z ∈ identityTube L d := by
  fin_cases j
  · change ((-d ≤ z.1.1 ∧ z.1.1 ≤ d) ∧ (-d ≤ -z.1.2 ∧ -z.1.2 ≤ d)) ∧
      z.2 ∈ Icc 0 (4 * L) ↔ _
    change _ ↔ ((-d ≤ z.1.1 ∧ z.1.1 ≤ d) ∧ (-d ≤ z.1.2 ∧ z.1.2 ≤ d)) ∧ _
    constructor <;> rintro ⟨⟨hx, hy⟩, ht⟩ <;>
      exact ⟨⟨hx, by constructor <;> linarith [hy.1, hy.2]⟩, ht⟩
  · rfl

theorem nestedTubeReindex_image (j : Fin 2) (L d : ℝ) :
    nestedTubeReindex j '' identityTube L d = identityTube L d := by
  apply Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact (nestedTubeReindex_mem j L d z).mpr hz
  · intro z hz
    refine ⟨nestedTubeReindex j z, (nestedTubeReindex_mem j L d z).mpr hz, ?_⟩
    fin_cases j <;> ext <;> simp [nestedTubeReindex, nestedArmReindex]

theorem nestedTubeReindex_map
    {F X ι : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [TopologicalSpace X]
    (e : ι → OpenPartialHomeomorph X F) {L d : ℝ} (hL : 0 < L) (hd : 0 < d)
    (j : Fin 2) (τ : C3 → X) (hτ : PolyhedralPLInCharts e τ (identityTube L d))
    (hfib : ∀ z ∈ identityTube L d, ∀ w ∈ identityTube L d,
      τ z = τ w ↔ z.1 = w.1 ∧
        (z.2 : AddCircle (4 * L)) = (w.2 : AddCircle (4 * L))) :
    PolyhedralPLInCharts e (τ ∘ nestedTubeReindex j) (identityTube L d) ∧
      (τ ∘ nestedTubeReindex j) '' identityTube L d = τ '' identityTube L d ∧
      ∀ z ∈ identityTube L d, ∀ w ∈ identityTube L d,
        (τ ∘ nestedTubeReindex j) z = (τ ∘ nestedTubeReindex j) w ↔
          z.1 = w.1 ∧ (z.2 : AddCircle (4 * L)) = (w.2 : AddCircle (4 * L)) := by
  have hmap : MapsTo (nestedTubeReindex j) (identityTube L d) (identityTube L d) :=
    fun z hz ↦ (nestedTubeReindex_mem j L d z).mpr hz
  have hPL : PolyhedralPLInCharts e (τ ∘ nestedTubeReindex j) (identityTube L d) := by
    have hI := isFinitePLBallPair_Icc (show -d < d by linarith)
    have hbox := (hI.prod hI).prod (isFinitePLBallPair_Icc (show 0 < 4 * L by positivity))
    obtain ⟨_, _, _, _, _, c, hc, _⟩ := hbox
    obtain ⟨_, ⟨K, hK, hKs, _⟩, _⟩ := hc
    have hp : FinitePiecewiseAffineOn (nestedTubeReindex j) K.space :=
      ⟨K, hK, rfl, K.affineOnFaces_affine
        (nestedTubeReindex j).toContinuousLinearMap.toContinuousAffineMap⟩
    have hh := hτ.comp_finitePiecewiseAffineOn K hK hp
      (fun z hz ↦ hmap (hKs.subset hz))
    simpa only [identityTube, hKs] using hh
  refine ⟨hPL, ?_, ?_⟩
  · rw [image_comp, nestedTubeReindex_image]
  · intro z hz w hw
    change τ (nestedTubeReindex j z) = τ (nestedTubeReindex j w) ↔ _
    rw [hfib _ (hmap hz) _ (hmap hw)]
    change (nestedArmReindex j z.1 = nestedArmReindex j w.1 ∧ _) ↔ _
    rw [(nestedArmReindex j).injective.eq_iff]
    rfl

end Dehn
