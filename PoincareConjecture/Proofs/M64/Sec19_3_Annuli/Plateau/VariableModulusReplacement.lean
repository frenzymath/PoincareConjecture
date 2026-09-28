import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.VariableModulusEnergy
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeakReplacementEnergy













set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped Topology Manifold ContDiff

namespace PoincareConjecture




theorem m64VariableModulus_integral_comparison
    {X : Type*} [MeasurableSpace X] {mu : Measure X} {f0 f1 : X → ℝ}
    (hf0 : Integrable f0 mu) (hf1 : Integrable f1 mu)
    (h0 : ∀ᵐ p ∂mu, 0 ≤ f0 p) (h1 : ∀ᵐ p ∂mu, 0 ≤ f1 p)
    {r : ℝ} (hr : 0 < r) :
    (∫ p, (f0 p + f1 p) / 2 ∂mu) ≤
        max r r⁻¹ * (∫ p, (r * f0 p + r⁻¹ * f1 p) / 2 ∂mu) ∧
      (∫ p, (r * f0 p + r⁻¹ * f1 p) / 2 ∂mu) ≤
        max r r⁻¹ * (∫ p, (f0 p + f1 p) / 2 ∂mu) := by
  have hu := (hf0.add hf1).div_const 2
  have hw := ((hf0.const_mul r).add (hf1.const_mul r⁻¹)).div_const 2
  have hDr : 1 ≤ max r r⁻¹ * r := by
    simpa only [inv_mul_cancel₀ hr.ne'] using
      mul_le_mul_of_nonneg_right (le_max_right r r⁻¹) hr.le
  have hDinv : 1 ≤ max r r⁻¹ * r⁻¹ := by
    simpa only [mul_inv_cancel₀ hr.ne'] using
      mul_le_mul_of_nonneg_right (le_max_left r r⁻¹) (inv_nonneg.mpr hr.le)
  constructor
  · rw [← integral_const_mul]
    apply integral_mono_ae hu (hw.const_mul _)
    filter_upwards [h0, h1] with p hp0 hp1
    change (f0 p + f1 p) / 2 ≤ max r r⁻¹ * ((r * f0 p + r⁻¹ * f1 p) / 2)
    have ha := mul_le_mul_of_nonneg_right hDr hp0
    have hb := mul_le_mul_of_nonneg_right hDinv hp1
    nlinarith
  · rw [← integral_const_mul]
    apply integral_mono_ae hw (hu.const_mul _)
    filter_upwards [h0, h1] with p hp0 hp1
    change (r * f0 p + r⁻¹ * f1 p) / 2 ≤ max r r⁻¹ * ((f0 p + f1 p) / 2)
    have ha := mul_le_mul_of_nonneg_right (le_max_left r r⁻¹) hp0
    have hb := mul_le_mul_of_nonneg_right (le_max_right r r⁻¹) hp1
    nlinarith

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e : M → EuclideanSpace ℝ (Fin m)} {c0 c1 : ℝ → M}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S



theorem m64VariableModulus_column_integrable
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (hQ : Continuous Q)
    {C : ℝ} (hb : ∀ q, ‖Q q‖ ≤ C) {K : Set LoopPlane}
    (f : LoopPlane → M) (hf : AEStronglyMeasurable f (volume.restrict K))
    (V : LoopPlane → E) (hV : MemLp V 2 (volume.restrict K)) :
    IntegrableOn (fun p => Q (f p) (V p) (V p)) K volume := by
  simpa only [add_self_div_two] using
    m64Observed_energyDensity_integrable Q hQ hb f hf (fun _ => V) (fun _ => hV)




theorem m64VariableModulus_replacement_energy
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (hQ : Continuous Q) (hei : IsEmbedding e)
    {C : ℝ} (hb : ∀ q, ‖Q q‖ ≤ C) (r : ℝ)
    (A W : M64ObservedWeakAnnulus (n := n) e c0 c1)
    {K : Set LoopPlane} [DecidablePred (· ∈ K)] (hK : MeasurableSet K) (hKS : K ⊆ S)
    (f : LoopPlane → M) (hf : AEStronglyMeasurable f (volume.restrict K))
    (V : Fin 2 → LoopPlane → E) (hV : ∀ i, MemLp (V i) 2 (volume.restrict K))
    (hmap : W.map = K.piecewise f A.map)
    (hcol : ∀ i, (W.column i : LoopPlane → E) =ᵐ[mu] K.piecewise (V i) (A.column i)) :
    W.weightedEnergy Q r = A.weightedEnergy Q r +
      (∫ p in K, (r * Q (f p) (V 0 p) (V 0 p) + r⁻¹ * Q (f p) (V 1 p) (V 1 p)) / 2) -
      ∫ p in K, (r * Q (A.map p) (A.column 0 p) (A.column 0 p) +
        r⁻¹ * Q (A.map p) (A.column 1 p) (A.column 1 p)) / 2 := by
  classical
  let old := fun p => (r * Q (A.map p) (A.column 0 p) (A.column 0 p) +
    r⁻¹ * Q (A.map p) (A.column 1 p) (A.column 1 p)) / 2
  let new := fun p => (r * Q (f p) (V 0 p) (V 0 p) + r⁻¹ * Q (f p) (V 1 p) (V 1 p)) / 2
  have heq : (fun p => (r * Q (W.map p) (W.column 0 p) (W.column 0 p) +
      r⁻¹ * Q (W.map p) (W.column 1 p) (W.column 1 p)) / 2) =ᵐ[mu] K.piecewise new old := by
    filter_upwards [hcol 0, hcol 1] with p h0 h1
    rw [h0, h1, hmap]
    by_cases hp : p ∈ K <;> simp only [piecewise, hp, if_true, if_false, new, old]
  have hi (i : Fin 2) := m64VariableModulus_column_integrable Q hQ hb f hf (V i) (hV i)
  unfold M64ObservedWeakAnnulus.weightedEnergy
  rw [integral_congr_ae heq]
  exact m64Integral_piecewise_of_subset hK hKS
    (((hi 0).const_mul r).add ((hi 1).const_mul r⁻¹) |>.div_const 2)
    (A.weightedEnergy_integrable Q hQ hei hb r)




theorem M64ObservedWeakAnnulus.weighted_local_energy_le_of_matching_flux
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (hQ : Continuous Q) (hei : IsEmbedding e)
    {C : ℝ} (hb : ∀ q, ‖Q q‖ ≤ C) (hpos : ∀ q v, 0 ≤ Q q v v)
    {r : ℝ} (hr : 0 < r)
    (hmin : ∀ W : M64ObservedWeakAnnulus (n := n) e c0 c1,
      A.weightedEnergy Q r ≤ W.weightedEnergy Q r)
    {K : Set LoopPlane} (hK : MeasurableSet K) (hKS : K ⊆ S)
    (f : LoopPlane → M) (hf : AEStronglyMeasurable f (volume.restrict K))
    (V : Fin 2 → LoopPlane → E) (hV : ∀ i, MemLp (V i) 2 (volume.restrict K))
    (hfl : MemLp (e ∘ f) 2 (volume.restrict K))
    (ht : ∀ i, ∀ᵐ p ∂volume.restrict K,
      V i p ∈ range (mfderiv (𝓡 n) (𝓡 m) e (f p)))
    (hgreen : ∀ (phi : LoopPlane → ℝ), ContDiff ℝ 1 phi → ∀ i : Fin 2,
      (∫ p in K, phi p • V i p) +
        (∫ p in K, fderiv ℝ phi p (EuclideanSpace.single i 1) • e (f p)) =
      (∫ p in K, phi p • A.column i p) +
        (∫ p in K, fderiv ℝ phi p (EuclideanSpace.single i 1) • e (A.map p))) :
    (∫ p in K, (Q (A.map p) (A.column 0 p) (A.column 0 p) +
      Q (A.map p) (A.column 1 p) (A.column 1 p)) / 2) ≤
      (max r r⁻¹) ^ 2 *
        ∫ p in K, (Q (f p) (V 0 p) (V 0 p) + Q (f p) (V 1 p) (V 1 p)) / 2 := by
  classical
  obtain ⟨W, hmap, hcol⟩ := A.replace hK hKS f V hfl hV ht hgreen
  have hE := m64VariableModulus_replacement_energy Q hQ hei hb r A W hK hKS
    f hf V hV hmap hcol
  have hm := hmin W
  have hlocal : (∫ p in K, (r * Q (A.map p) (A.column 0 p) (A.column 0 p) +
        r⁻¹ * Q (A.map p) (A.column 1 p) (A.column 1 p)) / 2) ≤
      ∫ p in K, (r * Q (f p) (V 0 p) (V 0 p) + r⁻¹ * Q (f p) (V 1 p) (V 1 p)) / 2 := by
    linarith
  have hD : 0 ≤ max r r⁻¹ := hr.le.trans (le_max_left _ _)
  have hold := (m64VariableModulus_integral_comparison
    ((A.column_energy_integrable Q hQ hei hb 0).mono_set hKS)
    ((A.column_energy_integrable Q hQ hei hb 1).mono_set hKS)
    (Eventually.of_forall fun p => hpos (A.map p) (A.column 0 p))
    (Eventually.of_forall fun p => hpos (A.map p) (A.column 1 p)) hr).1
  have hnew := (m64VariableModulus_integral_comparison
    (m64VariableModulus_column_integrable Q hQ hb f hf (V 0) (hV 0))
    (m64VariableModulus_column_integrable Q hQ hb f hf (V 1) (hV 1))
    (Eventually.of_forall fun p => hpos (f p) (V 0 p))
    (Eventually.of_forall fun p => hpos (f p) (V 1 p)) hr).2
  exact (hold.trans (mul_le_mul_of_nonneg_left hlocal hD)).trans
    ((mul_le_mul_of_nonneg_left hnew hD).trans_eq (by ring))

end PoincareConjecture
