import PoincareConjecture.Proofs.M76.Rigidity.CorrectedParameterProduct
import PoincareConjecture.Proofs.M76.Rigidity.ParameterBandNormalization









set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "E" => (V2 × ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1
local notation "J" => Icc (-(1 / 4 : ℝ)) (1 / 4)




theorem exists_normalized_corrected_parameter_product {a : ℝ} (ha : 0 < a) (q : E → E)
    (hq : FinitePiecewiseAffineOn q (Q ×ˢ Icc (-a) a))
    (hqi : InjOn q (Q ×ˢ Icc (-a) a))
    (hqm : MapsTo q (Q ×ˢ Icc (-a) a)
      (Q ×ˢ Ioo (-(1 / 2 : ℝ)) (1 / 2)))
    (hqc : ∀ z ∈ Q, q (z, 0) = (z, 0))
    (hopen : IsOpen ((fun z : Q × ℝ => ((z.1 : V2), z.2)) ⁻¹'
      (q '' (Q ×ˢ Ioo (-a) a)))) :
    ∃ f : E → E, FinitePiecewiseAffineOn f (D ×ˢ I) ∧ InjOn f (D ×ˢ I) ∧
      MapsTo f (D ×ˢ I) (D ×ˢ Ioo (-1 : ℝ) 1) ∧
      (∀ z ∈ D ×ˢ I, (f z).1 ∈ Q ↔ z.1 ∈ Q) ∧
      (∀ z ∈ Q, ∀ t ∈ I, f (z, t) = q (z, a * t)) ∧
      (∀ z ∈ D, f (z, 0) = (z, 0)) ∧
      ∀ v : ℝ, 0 < v → v ≤ 1 →
        IsOpen ((Subtype.val : (D ×ˢ I : Set E) → E) ⁻¹'
          (f '' (D ×ˢ Ioo (-v) v))) := by
  obtain ⟨hB, hBi, hBm, hBc, hBo⟩ := originalNormalizedBand_properties ha q hq hqi hqm hqc hopen
  obtain ⟨g, hg, hgi, hgm, hgb, hgl, hgc, hgo⟩ :=
    exists_corrected_parameter_product (q ∘ originalPrescribedTimeScaling a) hB hBi hBm hBc hBo
  let r : E →ᴬ[ℝ] E :=
    (ContinuousLinearMap.fst ℝ V2 ℝ).toContinuousAffineMap.prod
      ((1 / 4 : ℝ) • (ContinuousLinearMap.snd ℝ V2 ℝ).toContinuousAffineMap)
  have hrmap : MapsTo r (D ×ˢ I) (D ×ˢ J) := by
    intro z hz
    refine ⟨hz.1, ?_⟩
    change -(1 / 4 : ℝ) ≤ (1 / 4 : ℝ) * z.2 ∧ (1 / 4 : ℝ) * z.2 ≤ 1 / 4
    constructor <;> linarith [hz.2.1, hz.2.2]
  have hri : Function.Injective r := by
    intro z w hzw
    have hfirst := congrArg (fun x : E => x.1) hzw
    have hsecond := congrArg (fun x : E => x.2) hzw
    change z.1 = w.1 at hfirst
    change (1 / 4 : ℝ) * z.2 = (1 / 4 : ℝ) * w.2 at hsecond
    exact Prod.ext hfirst (by linarith)
  obtain ⟨K, hK, hKS⟩ := exists_finite_originalParameterPrism
  have hr : FinitePiecewiseAffineOn r (D ×ˢ I) :=
    ⟨K, hK, hKS, K.affineOnFaces_affine r⟩
  refine ⟨g ∘ r, hg.comp hr hrmap, fun z hz w hw hzw =>
    hri (hgi (hrmap hz) (hrmap hw) hzw), hgm.comp hrmap,
    fun z hz => hgb (r z) (hrmap hz), ?_, ?_, ?_⟩
  · intro z hz t ht
    have hquarter : (1 / 4 : ℝ) * t ∈ J :=
      (@hrmap (z, t) ⟨sphere_subset_closedBall hz, ht⟩).2
    change g (z, (1 / 4 : ℝ) * t) = q (z, a * t)
    rw [hgl z hz _ hquarter]
    change q (z, 4 * a * ((1 / 4 : ℝ) * t)) = q (z, a * t)
    have htime : 4 * a * ((1 / 4 : ℝ) * t) = a * t := by ring
    rw [htime]
  · intro z hz
    change g (z, (1 / 4 : ℝ) * 0) = (z, 0)
    rw [mul_zero]
    exact hgc z hz
  · intro v hv hvsmall
    have hrimage : r '' (D ×ˢ Ioo (-v) v) = D ×ˢ Ioo (-(v / 4)) (v / 4) := by
      apply Subset.antisymm
      · rintro _ ⟨z, hz, rfl⟩
        refine ⟨hz.1, ?_⟩
        change -(v / 4) < (1 / 4 : ℝ) * z.2 ∧ (1 / 4 : ℝ) * z.2 < v / 4
        constructor <;> linarith [hz.2.1, hz.2.2]
      · intro z hz
        refine ⟨(z.1, 4 * z.2), ⟨hz.1, ?_⟩, ?_⟩
        · constructor <;> linarith [hz.2.1, hz.2.2]
        · change (z.1, (1 / 4 : ℝ) * (4 * z.2)) = z
          exact Prod.ext rfl (by ring)
    rw [Set.image_comp, hrimage]
    exact hgo (v / 4) (by positivity) (by linarith)

end PoincareConjecture.M76
