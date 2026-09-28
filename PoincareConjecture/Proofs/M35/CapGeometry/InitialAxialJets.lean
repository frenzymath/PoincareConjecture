import PoincareConjecture.Proofs.M35.CapGeometry.InitialAxialCoefficient
import PoincareConjecture.Proofs.M35.CapGeometry.InitialCylinderFiniteJets
import PoincareConjecture.Proofs.M35.CapGeometry.RadialCylinderTensor
import PoincareConjecture.Proofs.M35.CapGeometry.VanishingMetricErrorJets
import PoincareConjecture.Proofs.M35.Thm12_28.NeckPullbackSmoothness

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35

local notation "V" => RoundCylinderCoordinates
local notation "E2" => EuclideanSpace ℝ (Fin 2)

theorem initial_axial_jetError_tendsto_zero
    (delta u v Q c s : ℕ → ℝ) (g : ℕ → RiemannianMetric 3 StandardCapSpace)
    (x : ℕ → StandardCapSpace) (N : ∀ k, StandardCylinderPatch (delta k)⁻¹ (x k))
    (epsilon : ℝ) (he : 0 < epsilon) (hc : ∀ k, 0 < c k)
    (hcl : ∀ k, c k * epsilon⁻¹ ≤ (delta k)⁻¹)
    (q : ℕ → UnitTwoSphere) (order : ℕ)
    (hd : ∀ k, 0 < delta k) (hvlo : ∀ k, -1 ≤ v k) (hvhi : ∀ k, v k < 1)
    (hs : ∀ k, s k ∈ Ioo (-epsilon⁻¹) epsilon⁻¹)
    (hclose : ∀ k, RoundCylinderClose (delta k) (v k)
      (roundCylinderPullback (g k) (N k).coordinate))
    (hdegree : ∀ k, order ≤ ⌊(delta k)⁻¹⌋₊)
    (hunit : ∀ k, Q k * c k ^ 2 = 1)
    {u₀ Q₀ c₀ s₀ : ℝ} (hu : ∀ k, u k < 1) (hu₀ : u₀ < 1)
    (hdlim : Tendsto delta atTop (𝓝 0)) (hulim : Tendsto u atTop (𝓝 u₀))
    (hQlim : Tendsto Q atTop (𝓝 Q₀)) (hclim : Tendsto c atTop (𝓝 c₀))
    (hslim : Tendsto s atTop (𝓝 s₀))
    (hnormal : Tendsto (fun k => Q k * (1 - v k) - (1 - u k)) atTop (𝓝 0)) :
    Tendsto (fun k => roundCylinderJetErrorSquared (u k)
      (fun z a b => Q k * roundCylinderPullback (g k)
        ((N k).axialRescale (c k) epsilon⁻¹ (hc k) (inv_pos.mpr he) (hcl k)).coordinate
          z a b) order (q k, s k)) atTop (𝓝 0) := by
  let p (k : ℕ) : V := (0, s k)
  let p₀ : V := (0, s₀)
  let T (k : ℕ) (y : V) : V := (y.1, c k * y.2)
  let M k := (N k).axialRescale (c k) epsilon⁻¹ (hc k) (inv_pos.mpr he) (hcl k)
  let B (k : ℕ) : RoundCylinderTwoTensor := roundCylinderPullback (g k) (N k).coordinate
  let C (k : ℕ) : RoundCylinderTwoTensor :=
    fun z a b => Q k * roundCylinderPullback (g k) (M k).coordinate z a b
  have hp : Tendsto p atTop (𝓝 p₀) := tendsto_const_nhds.prodMk_nhds hslim
  have hT (k : ℕ) : ContDiff ℝ ∞ (T k) :=
    contDiff_fst.prodMk (contDiff_const.mul contDiff_snd)
  have hid : HasUniformJetBoundsAt order (fun _ : ℕ => (id : V → V)) p := by
    intro j _hj
    have hdiff : ContDiffAt ℝ ∞ (id : V → V) p₀ := contDiffAt_id
    have hjet := (hdiff.continuousAt_iteratedFDeriv
      (by exact_mod_cast le_top (a := (j : ℕ∞)))).tendsto.comp hp
    obtain ⟨D, hD⟩ := (Metric.isBounded_range_of_tendsto _ hjet).exists_norm_le
    exact ⟨D, fun k => hD _ (mem_range_self k)⟩
  have hcjet : HasUniformJetBoundsAt order (fun k (_ : V) => c k) p := by
    intro j _hj
    cases j with
    | zero =>
      obtain ⟨D, hD⟩ := (Metric.isBounded_range_of_tendsto _ hclim).exists_norm_le
      exact ⟨D, fun k => by
        simpa only [norm_iteratedFDeriv_zero] using hD _ (mem_range_self k)⟩
    | succ j =>
      exact ⟨0, fun k => by
        simp only [iteratedFDeriv_succ_const, Pi.zero_apply, norm_zero, le_refl]⟩
  have hfst := hid.clm (fun _ => contDiffAt_id) (ContinuousLinearMap.fst ℝ E2 ℝ)
  have hsnd := hid.clm (fun _ => contDiffAt_id) (ContinuousLinearMap.snd ℝ E2 ℝ)
  have hcs := hcjet.bilinear hsnd (fun _ => contDiffAt_const) (fun _ => contDiffAt_snd)
    (ContinuousLinearMap.mul ℝ ℝ)
  have hTjet : HasUniformJetBoundsAt order T p :=
    hfst.prodMk hcs (fun _ => contDiffAt_fst)
      (fun _ => contDiffAt_const.mul contDiffAt_snd)
  have hsource (k : ℕ) : c k * s k ∈ Ioo (-(delta k)⁻¹) (delta k)⁻¹ := by
    have hlo := mul_lt_mul_of_pos_left (hs k).1 (hc k)
    have hhi := mul_lt_mul_of_pos_left (hs k).2 (hc k)
    constructor <;> nlinarith only [hlo, hhi, hcl k]
  have hCsmooth (k : ℕ) (i j : Fin 3) : ContDiffAt ℝ ∞
      (fun y => roundCylinderTensorCoefficient (C k) (chartAt E2 (q k)) y i j) (p k) := by
    have h := roundCylinderPullback_scaled_smoothOn (g k) (M k).coordinate epsilon
      (Q k) (M k).coordinate_smooth
    apply (h (q k) i j).contDiffAt
    apply ((chartAt E2 (q k)).open_target.prod isOpen_Ioo).mem_nhds
    exact ⟨by rw [sphere_chart_target]; trivial, hs k⟩
  have herr (r : ℕ) (hr : r ≤ order) (i j : Fin 3) : Tendsto
      (fun k => iteratedFDeriv ℝ r (fun y =>
        roundCylinderTensorCoefficient (C k) (chartAt E2 (q k)) y i j -
          roundCylinderGram (u k) (chartAt E2 (q k)) y i j) (p k)) atTop (𝓝 0) := by
    let F (k : ℕ) (y : V) :=
      roundCylinderTensorCoefficient (B k) (chartAt E2 (q k)) y i j -
        roundCylinderGram (v k) (chartAt E2 (q k)) y i j
    let w (k : ℕ) (a : Fin 3) := if a = 2 then c k else 1
    let alpha (k : ℕ) := Q k * w k i * w k j
    let mu (k : ℕ) := Q k * (1 - v k) - (1 - u k)
    let H (y : V) := roundCylinderGram 0 (chartAt E2 (q 0)) y i j -
      (roundCylinderCoordinateBasis i).2 * (roundCylinderCoordinateBasis j).2
    have hH : ContDiff ℝ ∞ H := (contDiff_roundCylinderGram 0 (q 0) i j).sub contDiff_const
    have hF (k : ℕ) : ContDiffAt ℝ ∞ (F k) (T k (p k)) :=
      ((hclose k).contDiffAt_coefficient (q k) (0, c k * s k) (hsource k) i j).sub
        (contDiff_roundCylinderGram (v k) (q k) i j).contDiffAt
    have hFcomp (k : ℕ) : ContDiffAt ℝ ∞ (F k ∘ T k) (p k) :=
      (hF k).comp (p k) (hT k).contDiffAt
    have hFjet : Tendsto (fun k => iteratedFDeriv ℝ r (F k ∘ T k) (p k))
        atTop (𝓝 0) := by
      apply jet_comp_tendsto_zero_of_bounded (hTjet.mono_order hr)
        (Eventually.of_forall fun k => (hT k).contDiffAt) (Eventually.of_forall hF)
      intro m hm
      exact cylinder_metric_error_jets_tendsto_zero delta v (fun k => c k * s k) B q
        (c₀ * s₀) order hd hvlo hvhi hsource hclose hdegree hdlim (hclim.mul hslim)
        m (hm.trans hr) i j
    have hw (a : Fin 3) : Tendsto (fun k => w k a) atTop
        (𝓝 (if a = 2 then c₀ else 1)) := by
      by_cases ha : a = 2
      · simpa only [w, if_pos ha] using hclim
      · simpa only [w, if_neg ha] using tendsto_const_nhds
    have halpha := (hQlim.mul (hw i)).mul (hw j)
    have hrinf : (r : ℕ∞ω) ≤ ∞ := by exact_mod_cast le_top (a := (r : ℕ∞))
    have hfirst : Tendsto (fun k => iteratedFDeriv ℝ r
        (fun y => alpha k * F k (T k y)) (p k)) atTop (𝓝 0) := by
      have h := halpha.smul hFjet
      simp only [smul_zero] at h
      apply h.congr'
      apply Eventually.of_forall
      intro k
      exact (iteratedFDeriv_const_smul_apply' ((hFcomp k).of_le hrinf)).symm
    have hHjet := (hH.contDiffAt.continuousAt_iteratedFDeriv
      (by exact_mod_cast le_top (a := (r : ℕ∞)))).tendsto.comp hp
    have hsecond : Tendsto (fun k => iteratedFDeriv ℝ r
        (fun y => mu k * H y) (p k)) atTop (𝓝 0) := by
      have h := hnormal.smul hHjet
      simp only [zero_smul] at h
      apply h.congr'
      apply Eventually.of_forall
      intro k
      exact (iteratedFDeriv_const_smul_apply' (hH.contDiffAt.of_le hrinf)).symm
    have hsum := hfirst.add hsecond
    simp only [add_zero] at hsum
    apply hsum.congr'
    apply Eventually.of_forall
    intro k
    have heq : (fun y : V => roundCylinderTensorCoefficient (C k)
        (chartAt E2 (q k)) y i j - roundCylinderGram (u k) (chartAt E2 (q k)) y i j)
        =ᶠ[𝓝 (p k)] (fun y => alpha k * F k (T k y) + mu k * H y) := by
      have hnear : ∀ᶠ y : V in 𝓝 (p k), y.2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹ :=
        (isOpen_Ioo.preimage continuous_snd).mem_nhds (hs k)
      filter_upwards [hnear] with y hy
      change Q k * roundCylinderTensorCoefficient
        (roundCylinderPullback (g k) (M k).coordinate) (chartAt E2 (q k)) y i j - _ = _
      rw [initial_axial_patch_coefficient (g k) (N k) (c k) epsilon⁻¹
        (hc k) (inv_pos.mpr he) (hcl k) (q k) y hy i j]
      have hm := initial_axial_model_error (Q k) (c k) (u k) (v k) (hunit k) (q k) y i j
      have hang : roundCylinderGram 0 (chartAt E2 (q k)) y i j =
          roundCylinderGram 0 (chartAt E2 (q 0)) y i j := by
        rw [roundCylinderGram_apply, roundCylinderGram_apply]
      rw [hang] at hm
      dsimp only [alpha, w, F, T, mu, H, B]
      linear_combination hm
    have hadd := fun_iteratedFDeriv_add_apply
      (((contDiffAt_const (c := alpha k)).mul (hFcomp k)).of_le hrinf)
      (((contDiffAt_const (c := mu k)).mul hH.contDiffAt).of_le hrinf)
    exact hadd.symm.trans ((heq.iteratedFDeriv ℝ r).eq_of_nhds).symm
  have h := roundCylinderJetDifferenceSquared_tendsto_zero order u hu u₀ hu₀ hulim q C
    (fun k => EvolvingRoundCylinderMetric (u k)) s s₀ hslim hCsmooth
    (fun k i j => (contDiff_roundCylinderGram (u k) (q k) i j).contDiffAt) herr
  simpa only [roundCylinderJetDifferenceSquared_model] using h

end PoincareConjecture.M35
