import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Disks.RimBands.Collar.LateralPartition
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.EmbeddedBandOpenness



set_option autoImplicit false
noncomputable section
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.RimBands
open TubeExterior.CornerBands

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "E" => (V2 × ℝ)
local notation "Rim" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1

def bandTimeScale (a : ℝ) : E →ᴬ[ℝ] E :=
  (ContinuousLinearMap.fst ℝ V2 ℝ).toContinuousAffineMap.prod
    (a • (ContinuousLinearMap.snd ℝ V2 ℝ).toContinuousAffineMap)

@[simp] theorem bandTimeScale_apply (a : ℝ) (p : E) : bandTimeScale a p=(p.1,a*p.2) := rfl

theorem bandTimeScale_mapsTo {a : ℝ} (ha : 0 < a) :
    MapsTo (bandTimeScale a) (Rim ×ˢ I) (Rim ×ˢ Icc (-a) a) := by
  intro p hp
  rw [bandTimeScale_apply]
  exact ⟨hp.1,by constructor <;> nlinarith [hp.2.1,hp.2.2]⟩

theorem bandTimeScale_open_image {a : ℝ} (ha : 0 < a) :
    bandTimeScale a '' (Rim ×ˢ Ioo (-1 : ℝ) 1) = Rim ×ˢ Ioo (-a) a := by
  ext p
  constructor
  · rintro ⟨q,hq,rfl⟩
    rw [bandTimeScale_apply]
    exact ⟨hq.1,by constructor <;> nlinarith [hq.2.1,hq.2.2]⟩
  · intro hp
    refine ⟨(p.1,p.2/a),⟨hp.1,?_,?_⟩,?_⟩
    · apply (lt_div_iff₀ ha).mpr
      linarith [hp.2.1]
    · apply (div_lt_iff₀ ha).mpr
      simpa using hp.2.2
    · simp [mul_div_cancel₀ _ ha.ne']

theorem rescaled_boundary_band_properties
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {Q : Set X} {j : V2 → X}
    {F : E → X} (hF : PolyhedralPLInCharts e F (Rim ×ˢ I))
    (hi : InjOn F (Rim ×ˢ I)) (hQ : MapsTo F (Rim ×ˢ I) (frontier Q))
    (hc : ∀ z ∈ Rim, F (z,0)=j z)
    (ho : IsOpen ((Subtype.val : frontier Q → X) ⁻¹' (F '' (Rim ×ˢ Ioo (-1 : ℝ) 1))))
    {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    PolyhedralPLInCharts e (F ∘ bandTimeScale a) (Rim ×ˢ I) ∧
      InjOn (F ∘ bandTimeScale a) (Rim ×ˢ I) ∧
      MapsTo (F ∘ bandTimeScale a) (Rim ×ˢ I) (frontier Q) ∧
      (∀ z ∈ Rim, (F ∘ bandTimeScale a) (z,0)=j z) ∧
      IsOpen ((Subtype.val : frontier Q → X) ⁻¹'
        ((F ∘ bandTimeScale a) '' (Rim ×ˢ Ioo (-1 : ℝ) 1))) := by
  have hmap : MapsTo (bandTimeScale a) (Rim ×ˢ I) (Rim ×ˢ I) := by
    intro p hp
    have hh := bandTimeScale_mapsTo ha hp
    exact ⟨hh.1,by constructor <;> linarith [hh.2.1,hh.2.2]⟩
  obtain ⟨K,hK,hKs⟩ := exists_finite_hamiltonMeridianBand (show (-1 : ℝ) < 1 by norm_num)
  have hscale : FinitePiecewiseAffineOn (bandTimeScale a) K.space :=
    ⟨K,hK,rfl,K.affineOnFaces_affine (bandTimeScale a)⟩
  refine ⟨?_,?_,hQ.comp hmap,?_,?_⟩
  · have h := hF.comp_finitePiecewiseAffineOn K hK hscale
      (fun _ hp => hmap (hKs.subset hp))
    simpa only [hKs,Function.comp_def] using h
  · intro p hp q hq heq
    have hh := hi (hmap hp) (hmap hq) heq
    simp only [bandTimeScale_apply] at hh
    apply Prod.ext
    · have ht := congrArg Prod.fst hh
      exact ht
    · have ht := congrArg Prod.snd hh
      exact (mul_left_cancel₀ ha.ne') ht
  · intro z hz
    simpa using hc z hz
  · rw [image_comp,bandTimeScale_open_image ha]
    exact Set.InjOn.isOpen_smaller_band_image (isCompact_sphere (0 : V2) 1)
      hi hF.continuousOn ho ha1

theorem prescribedArmBand_rescale
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R W : Set X}
    {S T C D : Set (ℝ × ℝ)} {f₀ f₁ : (ℝ × ℝ) → X}
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    (r δ a t₀ t₁ s t : ℝ) (side b o : Bool) :
    prescribedArmBand U r δ t₀ t₁ side b (sign o*(a*s/2),t) =
      prescribedArmBand U r (δ*a/2) t₀ t₁ side b (sign o*s,t) := by
  simp only [prescribedArmBand,Function.comp_apply,armCoordinates_apply]
  apply congrArg (originalBandMap U r (b,if side then !b else b))
  apply Prod.ext
  · ring
  · rfl

end PoincareConjecture.M76.Dehn.Annuli.RimBands
