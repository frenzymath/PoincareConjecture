import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarConjugateOpen
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarPolarLocal













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M64Uniformization

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "Cover" => ℝ × ℝ




def scalarConjugateNormalization (P c : ℝ) (hP : P ≠ 0) : Plane ≃ₜ Cover where
  toFun x := (x 0, (x 1 + c) / P)
  invFun z := z.1 • EuclideanSpace.basisFun (Fin 2) ℝ 0 +
    (P * z.2 - c) • EuclideanSpace.basisFun (Fin 2) ℝ 1
  left_inv x := by
    ext i
    fin_cases i <;> simp [mul_div_cancel₀ _ hP]
  right_inv z := by
    ext <;> simp [hP]
  continuous_toFun := (EuclideanSpace.proj 0).continuous.prodMk
    (((EuclideanSpace.proj 1).continuous.add continuous_const).div_const P)
  continuous_invFun := (continuous_fst.smul continuous_const).add
    (((continuous_const.mul continuous_snd).sub continuous_const).smul continuous_const)

variable {g : RiemannianMetric 2 Plane} (D : LeviCivitaData g)





theorem scalarNormalizedCoverMap_open_and_discrete {H : Plane → ℝ} {V : Cover → ℝ}
    (hHc : Continuous H)
    (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    (hlap : ∀ x ∈ scalarAnnulus, D.laplacian H x = 0)
    (hinner : ∀ x : Plane, ‖x‖ = 1 → H x = 0)
    (houter : ∀ x : Plane, ‖x‖ = 2 → H x = 1)
    (hdV : ∀ z ∈ scalarCoverStrip, HasFDerivAt V (scalarCoverForm D H z) z)
    {P : ℝ} (hP : P ≠ 0) {z : Cover} (hz : z ∈ scalarCoverStrip) :
    (𝓝 (scalarNormalizedCoverMap H V P z) ≤ map (scalarNormalizedCoverMap H V P) (𝓝 z)) ∧
      ∀ᶠ y in 𝓝[≠] z,
        scalarNormalizedCoverMap H V P y ≠ scalarNormalizedCoverMap H V P z := by
  obtain ⟨r, W, hr, -, hWs, hdW⟩ :=
    exists_local_annular_conjugate D hHs hlap (scalarCoverMap_mem hz)
  obtain ⟨hWopen, hWfiber⟩ := scalarConjugatePair_open_and_discrete D hHc hHs hlap
    hinner houter hWs (scalarCoverMap_mem hz)
    (eventually_of_mem (Metric.ball_mem_nhds (scalarCoverMap z) hr) fun y hy => hdW y hy)
  obtain ⟨s, hs, hball⟩ := Metric.mem_nhds_iff.mp (inter_mem
    (scalarCoverStrip_isOpen.mem_nhds hz)
    (scalarCoverMap_smooth.continuous.continuousAt.preimage_mem_nhds
      (Metric.ball_mem_nhds (scalarCoverMap z) hr)))
  let Q : Cover → ℝ := fun y => V y - W (scalarCoverMap y)
  have hQ (y : Cover) (hy : y ∈ Metric.ball z s) :
      HasFDerivAt Q (0 : Cover →L[ℝ] ℝ) y := by
    have h := (hdV y (hball hy).1).sub ((hdW _ (hball hy).2).comp y
      (scalarCoverMap_smooth.differentiable (by simp) y).hasFDerivAt)
    simpa only [Q, Function.comp_def, scalarCoverForm, sub_self] using! h
  obtain ⟨c, hc⟩ := Metric.isOpen_ball.exists_is_const_of_fderiv_eq_zero
    (convex_ball z s).isPreconnected
    (fun y hy => (hQ y hy).differentiableAt.differentiableWithinAt)
    (fun y hy => (hQ y hy).fderiv)
  let T := scalarConjugateNormalization P c hP
  have heq : scalarNormalizedCoverMap H V P =ᶠ[𝓝 z]
      T ∘ scalarConjugatePair H W ∘ scalarCoverMap := by
    filter_upwards [Metric.ball_mem_nhds z hs] with y hy
    have hyc : V y - W (scalarCoverMap y) = c := hc y hy
    have hv : V y = W (scalarCoverMap y) + c := by linarith
    ext <;> simp [scalarNormalizedCoverMap, T, scalarConjugateNormalization,
      scalarConjugatePair, hv]
  have hmap := Filter.map_mono (m := T) hWopen
  rw [T.map_nhds_eq, ← scalarCoverMap_map_nhds (ne_of_gt (lt_trans zero_lt_one hz.1)),
    map_map, map_map] at hmap
  constructor
  · rw [heq.self_of_nhds, map_congr heq]
    exact hmap
  · have hfi := (scalarCoverMap_tendsto_nhdsNE
      (ne_of_gt (lt_trans zero_lt_one hz.1))).eventually hWfiber
    filter_upwards [hfi, heq.filter_mono nhdsWithin_le_nhds] with y hy hyEq
    intro hsame
    apply hy
    apply T.injective
    change (T ∘ scalarConjugatePair H W ∘ scalarCoverMap) y =
      (T ∘ scalarConjugatePair H W ∘ scalarCoverMap) z
    rw [← hyEq, ← heq.self_of_nhds]
    exact hsame




theorem scalarNormalizedCoverMap_nhds_le_map {H : Plane → ℝ} {V : Cover → ℝ}
    (hHc : Continuous H)
    (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    (hlap : ∀ x ∈ scalarAnnulus, D.laplacian H x = 0)
    (hinner : ∀ x : Plane, ‖x‖ = 1 → H x = 0)
    (houter : ∀ x : Plane, ‖x‖ = 2 → H x = 1)
    (hdV : ∀ z ∈ scalarCoverStrip, HasFDerivAt V (scalarCoverForm D H z) z)
    {P : ℝ} (hP : P ≠ 0) {z : Cover} (hz : z ∈ scalarCoverStrip) :
    𝓝 (scalarNormalizedCoverMap H V P z) ≤ map (scalarNormalizedCoverMap H V P) (𝓝 z) :=
  (scalarNormalizedCoverMap_open_and_discrete D hHc hHs hlap hinner houter hdV hP hz).1





theorem scalarNormalizedCover_isOpenMap {H : Plane → ℝ} {V : Cover → ℝ}
    (hHc : Continuous H)
    (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    (hlap : ∀ x ∈ scalarAnnulus, D.laplacian H x = 0)
    (hinner : ∀ x : Plane, ‖x‖ = 1 → H x = 0)
    (houter : ∀ x : Plane, ‖x‖ = 2 → H x = 1)
    (hdV : ∀ z ∈ scalarCoverStrip, HasFDerivAt V (scalarCoverForm D H z) z)
    {P : ℝ} (hP : P ≠ 0)
    (hrange : ∀ x ∈ scalarAnnulus, H x ∈ Ioo (0 : ℝ) 1) :
    IsOpenMap (scalarNormalizedCover H V P hrange) := by
  apply isOpenMap_iff_nhds_le.mpr
  intro z
  apply (Filter.map_le_map_iff Subtype.val_injective).mp
  have htarget : IsOpen scalarPotentialStrip := isOpen_Ioo.preimage continuous_fst
  rw [map_nhds_subtype_val, htarget.nhdsWithin_eq
    (scalarNormalizedCover H V P hrange z).property, map_map]
  have h := scalarNormalizedCoverMap_nhds_le_map D hHc hHs hlap hinner houter hdV hP z.property
  rw [← scalarCoverStrip_isOpen.nhdsWithin_eq z.property, ← map_nhds_subtype_val,
    map_map] at h
  exact h

end PoincareConjecture.M64Uniformization
