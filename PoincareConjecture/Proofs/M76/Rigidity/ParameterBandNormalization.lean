import PoincareConjecture.Proofs.M76.Rigidity.MeridianBandCarrier

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "E" => (V2 × ℝ)
local notation "Q" => sphere (0 : V2) 1
local notation "I" => Icc (-(1 / 4 : ℝ)) (1 / 4)
local notation "Io" => Ioo (-(1 / 4 : ℝ)) (1 / 4)

noncomputable def originalPrescribedTimeScaling (a : ℝ) : E →ᴬ[ℝ] E :=
  (ContinuousLinearMap.fst ℝ V2 ℝ).toContinuousAffineMap.prod
    ((4 * a) • (ContinuousLinearMap.snd ℝ V2 ℝ).toContinuousAffineMap)

theorem originalPrescribedTimeScaling_mapsTo {a : ℝ} (ha : 0 < a) :
    MapsTo (originalPrescribedTimeScaling a) (Q ×ˢ I) (Q ×ˢ Icc (-a) a) := by
  intro z hz
  refine ⟨hz.1, ?_⟩
  change -a ≤ 4 * a * z.2 ∧ 4 * a * z.2 ≤ a
  constructor <;> nlinarith [hz.2.1, hz.2.2]

theorem originalPrescribedTimeScaling_open_image {a : ℝ} (ha : 0 < a) :
    originalPrescribedTimeScaling a '' (Q ×ˢ Io) = Q ×ˢ Ioo (-a) a := by
  have hscale : 0 < 4 * a := by positivity
  apply Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    refine ⟨hz.1, ?_⟩
    change -a < 4 * a * z.2 ∧ 4 * a * z.2 < a
    constructor <;> nlinarith [hz.2.1, hz.2.2]
  · intro z hz
    refine ⟨(z.1, z.2 / (4 * a)), ⟨hz.1, ?_⟩, ?_⟩
    · constructor
      · apply (lt_div_iff₀ hscale).mpr
        linarith [hz.2.1]
      · apply (div_lt_iff₀ hscale).mpr
        linarith [hz.2.2]
    · change (z.1, 4 * a * (z.2 / (4 * a))) = z
      exact Prod.ext rfl (mul_div_cancel₀ z.2 hscale.ne')

theorem originalNormalizedBand_properties {a : ℝ} (ha : 0 < a) (q : E → E)
    (hq : FinitePiecewiseAffineOn q (Q ×ˢ Icc (-a) a))
    (hqi : InjOn q (Q ×ˢ Icc (-a) a))
    (hqm : MapsTo q (Q ×ˢ Icc (-a) a)
      (Q ×ˢ Ioo (-(1 / 2 : ℝ)) (1 / 2)))
    (hqc : ∀ z ∈ Q, q (z, 0) = (z, 0))
    (hopen : IsOpen ((fun z : Q × ℝ => ((z.1 : V2), z.2)) ⁻¹'
      (q '' (Q ×ˢ Ioo (-a) a)))) :
    FinitePiecewiseAffineOn (q ∘ originalPrescribedTimeScaling a) (Q ×ˢ I) ∧
      InjOn (q ∘ originalPrescribedTimeScaling a) (Q ×ˢ I) ∧
      MapsTo (q ∘ originalPrescribedTimeScaling a) (Q ×ˢ I)
        (Q ×ˢ Ioo (-(1 / 2 : ℝ)) (1 / 2)) ∧
      (∀ z ∈ Q, (q ∘ originalPrescribedTimeScaling a) (z, 0) = (z, 0)) ∧
      IsOpen ((fun z : Q × ℝ => ((z.1 : V2), z.2)) ⁻¹'
        ((q ∘ originalPrescribedTimeScaling a) '' (Q ×ˢ Io))) := by
  let r := originalPrescribedTimeScaling a
  have hrmap := originalPrescribedTimeScaling_mapsTo ha
  have hri : Function.Injective r := by
    intro x y hxy
    have hfirst := congrArg (fun z : E => z.1) hxy
    change x.1 = y.1 at hfirst
    have hsecond : 4 * a * x.2 = 4 * a * y.2 :=
      congrArg (fun z : E => z.2) hxy
    exact Prod.ext hfirst (mul_left_cancel₀ (by positivity : 4 * a ≠ 0) hsecond)
  obtain ⟨K, hK, hKS⟩ := exists_finite_hamiltonMeridianBand
    (show -(1 / 4 : ℝ) < 1 / 4 by norm_num)
  have hr : FinitePiecewiseAffineOn r (Q ×ˢ I) :=
    ⟨K, hK, hKS, K.affineOnFaces_affine r⟩
  refine ⟨hq.comp hr hrmap, fun x hx y hy hxy =>
    hri (hqi (hrmap hx) (hrmap hy) hxy), hqm.comp hrmap, ?_, ?_⟩
  · intro z hz
    change q (z, 4 * a * 0) = (z, 0)
    rw [mul_zero]
    exact hqc z hz
  · rw [Set.image_comp, originalPrescribedTimeScaling_open_image ha]
    exact hopen

end PoincareConjecture.M76
