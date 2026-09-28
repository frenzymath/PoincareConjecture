import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Disks.RimBands.Collar.Rescaling



set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.RimBands
open TubeExterior TubeExterior.CornerBands

local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "E" => (V2 × ℝ)
local notation "Rim" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1
local notation "J" => Icc (0 : ℝ) 1

theorem exists_partitioned_complement_disk_band
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R W : Set X}
    {S T C D : Set P2} {f₀ f₁ : P2 → X}
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    (hR : IsCompact R) (he : PLDomain e R) {r δ t₀ t₁ : ℝ}
    (hδ : 0 < δ) (hδr : δ < r) (hr1 : r < 1)
    (horder : (t₀=0 ∧ t₁=1) ∨ (t₀=1 ∧ t₁=0)) (j : Bool) {k : P2 → X}
    (hk : PolyhedralPLInCharts e k (J ×ˢ J))
    (hki : IsEmbedding (fun p : J ×ˢ J => k p))
    (hkQ : MapsTo k (J ×ˢ J) (R \ U.map '' openTube r))
    (hkproper : ∀ p ∈ J ×ˢ J,
      k p ∈ frontier (R \ U.map '' openTube r) ↔ p ∈ frontier (J ×ˢ J))
    (himage : k '' (J ×ˢ J) = (if j then f₁ '' T else f₀ '' S) ∩ (R \ U.map '' openTube r))
    (hleft : ∀ t ∈ J, k (0,t) = originalBandMap U r (true,if j then false else true)
      (0,(1-t)*t₀+t*t₁))
    (hright : ∀ t ∈ J, k (1,t) = originalBandMap U r (false,if j then true else false)
      (0,(1-t)*t₀+t*t₁)) :
    ∃ (orientation : Bool → Bool) (ρ : ℝ) (F : E → X), 0 < ρ ∧ ρ < r ∧
      PolyhedralPLInCharts e F (Rim ×ˢ I) ∧ InjOn F (Rim ×ˢ I) ∧
      MapsTo F (Rim ×ˢ I) (frontier (R \ U.map '' openTube r)) ∧
      (∀ z ∈ Rim, F (z,0)=(k ∘ CubeCoordinates.toRectangle) z) ∧
      IsOpen ((Subtype.val : frontier (R \ U.map '' openTube r) → X) ⁻¹'
        (F '' (Rim ×ˢ Ioo (-1 : ℝ) 1))) ∧
      (∀ b t, t ∈ J → ∀ s ∈ I,
        F (rimArm b t,s)=prescribedArmBand U r ρ t₀ t₁ j b (sign (orientation b)*s,t)) ∧
      (∀ z ∈ Rim, ∀ s ∈ I,
        F (z,s) ∈ U.map '' lateral r ↔ ∃ b : Bool, ∃ t ∈ J, z=rimArm b t) := by
  obtain ⟨o,v,F,hv,hF,hi,hQ,hc,ho,harms⟩ := exists_full_complement_disk_band
    U hR he hδ hδr hr1 horder j hk hki hkQ hkproper himage hleft hright
  have hcenter (z : V2) (hz : z ∈ Rim) :
      F (z,0) ∈ (if j then f₁ '' T else f₀ '' S) := by
    rw [hc z hz]
    exact (himage.subset ⟨CubeCoordinates.toRectangle z,
      CubeCoordinates.toRectangle_bijOn.1 (sphere_subset_closedBall hz),rfl⟩).1
  obtain ⟨a,ha,hasmall,_,hpartition,harm⟩ := exists_band_width_with_exact_lateral_partition
    U hδ hδr hr1.le horder j hv hF.continuousOn hi hcenter harms
  obtain ⟨hG,hGi,hGQ,hGc,hGo⟩ := rescaled_boundary_band_properties hF hi hQ hc ho ha (by linarith)
  refine ⟨o,δ*a/2,F ∘ bandTimeScale a,div_pos (mul_pos hδ ha) (by norm_num),
    by nlinarith,hG,hGi,hGQ,hGc,hGo,?_,?_⟩
  · intro b t ht s hs
    have hscaled : a*s ∈ Icc (-a) a := by constructor <;> nlinarith [hs.1,hs.2]
    change F (rimArm b t,a*s)=_
    rw [harm b t ht _ hscaled,prescribedArmBand_rescale]
  · intro z hz s hs
    exact hpartition z hz (a*s) (by constructor <;> nlinarith [hs.1,hs.2])

end PoincareConjecture.M76.Dehn.Annuli.RimBands
