import PoincareConjecture.Proofs.M08.EulerMomentum
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace PoincareConjecture.M08

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

local instance variationCoordinatesDualGroup : NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance variationCoordinatesDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance variationCoordinatesBilinGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance variationCoordinatesBilinSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

theorem coordinateSlice_fst_hasDerivAt (z : ℝ × ℝ → E) {p : ℝ × ℝ}
    (hz : DifferentiableAt ℝ z p) :
    HasDerivAt (fun s ↦ z (s, p.2)) (fderiv ℝ z p (1, 0)) p.1 :=
  hz.hasFDerivAt.comp_hasDerivAt p.1
    ((hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2))

theorem coordinateSlice_snd_hasDerivAt (z : ℝ × ℝ → E) {p : ℝ × ℝ}
    (hz : DifferentiableAt ℝ z p) :
    HasDerivAt (fun u ↦ z (p.1, u)) (fderiv ℝ z p (0, 1)) p.2 :=
  hz.hasFDerivAt.comp_hasDerivAt p.2
    ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2))

theorem coordinate_mixed_hasDerivAt {Ω : Set (ℝ × ℝ)} (hΩ : IsOpen Ω)
    (z : ℝ × ℝ → E) (hz : ContDiffOn ℝ ∞ z Ω) {p : ℝ × ℝ} (hp : p ∈ Ω) :
    ∃ k : E,
      HasDerivAt (fun u ↦ deriv (fun s ↦ z (s, u)) p.1) k p.2 ∧
      HasDerivAt (fun s ↦ deriv (fun u ↦ z (s, u)) p.2) k p.1 := by
  have hza := (hz p hp).contDiffAt (hΩ.mem_nhds hp)
  have hfd : DifferentiableAt ℝ (fderiv ℝ z) p :=
    (hza.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  let k := fderiv ℝ (fderiv ℝ z) p (0, 1) (1, 0)
  refine ⟨k, ?_, ?_⟩
  · have h := (coordinateSlice_snd_hasDerivAt (fderiv ℝ z) hfd).clm_apply
      (hasDerivAt_const p.2 ((1 : ℝ), (0 : ℝ)))
    have hd : HasDerivAt (fun u ↦ fderiv ℝ z (p.1, u) (1, 0)) k p.2 := by
      simpa only [map_zero, add_zero] using h
    apply hd.congr_of_eventuallyEq
    have hnear : ∀ᶠ u in 𝓝 p.2, (p.1, u) ∈ Ω :=
      (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds (hΩ.mem_nhds hp)
    filter_upwards [hnear] with u hu
    exact (coordinateSlice_fst_hasDerivAt z
      (((hz (p.1, u) hu).contDiffAt (hΩ.mem_nhds hu)).differentiableAt (by simp))).deriv
  · have h := (coordinateSlice_fst_hasDerivAt (fderiv ℝ z) hfd).clm_apply
      (hasDerivAt_const p.1 ((0 : ℝ), (1 : ℝ)))
    have htwo : minSmoothness ℝ 2 ≤ (∞ : ℕ∞ω) := by
      rw [minSmoothness_of_isRCLikeNormedField]
      change (↑(2 : ℕ∞) : ℕ∞ω) ≤ ↑(⊤ : ℕ∞)
      exact WithTop.coe_le_coe.mpr le_top
    have hsym := (hza.isSymmSndFDerivAt htwo) (1, 0) (0, 1)
    have hd : HasDerivAt (fun s ↦ fderiv ℝ z (s, p.2) (0, 1)) k p.1 := by
      simpa only [map_zero, add_zero, hsym] using h
    apply hd.congr_of_eventuallyEq
    have hnear : ∀ᶠ s in 𝓝 p.1, (s, p.2) ∈ Ω :=
      (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds (hΩ.mem_nhds hp)
    filter_upwards [hnear] with s hs
    exact (coordinateSlice_snd_hasDerivAt z
      (((hz (s, p.2) hs).contDiffAt (hΩ.mem_nhds hs)).differentiableAt (by simp))).deriv

theorem chart_density_hasDerivAt
    (G : E → E →L[ℝ] E →L[ℝ] ℝ) (V : E → ℝ)
    (DG : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (DV : E →L[ℝ] ℝ)
    {z q : ℝ → E} {u : ℝ} {w k : E}
    (hG : HasFDerivAt G DG (z u)) (hV : HasFDerivAt V DV (z u))
    (hz : HasDerivAt z w u) (hq : HasDerivAt q k u)
    (hsym : ∀ v v' : E, G (z u) v v' = G (z u) v' v) :
    HasDerivAt (fun v ↦ G (z v) (q v) (q v) / 2 + V (z v))
      (DG w (q u) (q u) / 2 + G (z u) (q u) k + DV w) u := by
  have hmetric := ((hG.comp_hasDerivAt u hz).clm_apply hq).clm_apply hq
  have h := (hmetric.div_const 2).add (hV.comp_hasDerivAt u hz)
  convert h using 1 <;> try rfl
  simp only [add_apply, Function.comp_apply]
  rw [hsym k (q u)]
  ring

theorem linear_moving_vector_hasDerivAt {P : ℝ → E →L[ℝ] ℝ}
    {w : ℝ → E} {s d : ℝ} {k : E}
    (hP : DifferentiableAt ℝ P s) (hw : HasDerivAt w k s)
    (hfixed : HasDerivAt (fun r ↦ P r (w s)) d s) :
    HasDerivAt (fun r ↦ P r (w r)) (d + P s k) s := by
  have hconst := hP.hasDerivAt.clm_apply (hasDerivAt_const s (w s))
  have hd : deriv P s (w s) = d := by
    simpa only [map_zero, add_zero] using hconst.unique hfixed
  simpa only [hd] using hP.hasDerivAt.clm_apply hw

end PoincareConjecture.M08


