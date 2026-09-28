import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.AnnulusSliceDifferential

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Bundle
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem m64TwoParameter_second_velocity_contMDiffAt
    {c : ℝ → ℝ → M} {O : Set (ℝ × ℝ)} (hO : IsOpen O)
    (hc : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n) ∞
      (fun q : ℝ × ℝ => c q.1 q.2) O) {p : ℝ × ℝ} (hp : p ∈ O) :
    ContMDiffAt 𝓘(ℝ, ℝ × ℝ) ((𝓡 n).prod (𝓡 n)) ∞
      (fun q : ℝ × ℝ => (⟨c q.1 q.2, curveVelocity (c q.1) q.2⟩ :
        TangentBundle (𝓡 n) M)) p := by
  let f := fun q : ℝ × ℝ => c q.1 q.2
  have hfp : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) (𝓡 n) ∞ f p := hc.contMDiffAt (hO.mem_nhds hp)
  have hv : ContMDiffAt 𝓘(ℝ, ℝ × ℝ)
      ((𝓘(ℝ, ℝ × ℝ)).prod 𝓘(ℝ, ℝ × ℝ)) ∞
      (fun q : ℝ × ℝ => (⟨q, (0, 1)⟩ : TangentBundle 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ))) p := by
    rw [contMDiffAt_totalSpace]
    exact ⟨contMDiffAt_id, by simpa using contMDiffAt_const (c := ((0 : ℝ), (1 : ℝ)))⟩
  have hpush := (hfp.mfderiv_const (m := ∞) (by simp)).clm_apply_of_inCoordinates hv hfp
  apply hpush.congr_of_eventuallyEq
  filter_upwards [hO.mem_nhds hp] with q hq
  have hline := hasFDerivAt_prodMk_right (𝕜 := ℝ) q.1 q.2
  have hlineM : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ)
      (fun r : ℝ => (q.1, r)) q.2 := hline.differentiableAt.mdifferentiableAt
  have hder : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ)
      (fun r : ℝ => (q.1, r)) q.2 1 = (0, 1) := by
    rw [mfderiv_eq_fderiv, hline.fderiv]
    rfl
  have hchain := mfderiv_comp_apply q.2
    ((hc.contMDiffAt (hO.mem_nhds hq)).mdifferentiableAt (by simp)) hlineM (1 : ℝ)
  rw [hder] at hchain
  exact congrArg (fun v : TangentSpace (𝓡 n) (c q.1 q.2) =>
    (⟨c q.1 q.2, v⟩ : TangentBundle (𝓡 n) M)) hchain

theorem m64MovingCurve_half_energy_hasDerivAt
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    {c : ℝ → ℝ → M} {O : Set (ℝ × ℝ)} (hO : IsOpen O)
    (hc : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n) ∞
      (fun q : ℝ × ℝ => c q.1 q.2) O) {t x : ℝ} (hp : (t, x) ∈ O) :
    HasDerivAt
      (fun r => (1 / 2 : ℝ) * g.inner (c r x)
        (curveVelocity (c r) x) (curveVelocity (c r) x))
      (g.inner (c t x)
        (rampHorizontalCovariantDerivative D (c t)
          (fun y => curveVelocity (fun r => c r y) t) x)
        (curveVelocity (c t) x)) t := by
  have hline : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ) ∞
      (fun r : ℝ => (r, x)) t :=
    contMDiffAt_iff_contDiffAt.mpr (contDiffAt_id.prodMk contDiffAt_const)
  have hcurve : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n) (fun r => c r x) t :=
    ((hc.contMDiffAt (hO.mem_nhds hp)).comp t hline).mdifferentiableAt (by simp)
  have hX := ((m64TwoParameter_second_velocity_contMDiffAt hO hc hp).comp t hline).mdifferentiableAt
    (by simp)
  have hpair := (M62.hasDerivAt_metric_pairing D hcurve hX hX).const_mul (1 / 2 : ℝ)
  have htor := M62.pullback_velocity_commute D c hO hc hp
  convert! hpair using 1
  rw [← htor, g.symm (c t x) (curveVelocity (c t) x)]
  ring

theorem m64TwoParameter_first_velocity_contMDiffAt
    {c : ℝ → ℝ → M} {O : Set (ℝ × ℝ)} (hO : IsOpen O)
    (hc : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n) ∞
      (fun q : ℝ × ℝ => c q.1 q.2) O) {p : ℝ × ℝ} (hp : p ∈ O) :
    ContMDiffAt 𝓘(ℝ, ℝ × ℝ) ((𝓡 n).prod (𝓡 n)) ∞
      (fun q : ℝ × ℝ => (⟨c q.1 q.2, curveVelocity (fun r => c r q.2) q.1⟩ :
        TangentBundle (𝓡 n) M)) p := by
  have hswap : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) ∞
      (Prod.swap : ℝ × ℝ → ℝ × ℝ) :=
    contMDiff_iff_contDiff.mpr (contDiff_snd.prodMk contDiff_fst)
  have hswapO : IsOpen (Prod.swap ⁻¹' O) := hO.preimage hswap.continuous
  have hc' : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n) ∞
      (fun q : ℝ × ℝ => c q.2 q.1) (Prod.swap ⁻¹' O) :=
    hc.comp hswap.contMDiffOn (fun _ hq => hq)
  have hp' : p.swap ∈ Prod.swap ⁻¹' O := by simpa only [mem_preimage, Prod.swap_swap] using hp
  have h := (m64TwoParameter_second_velocity_contMDiffAt
    (c := fun r s => c s r) hswapO hc' hp').comp p (hswap p)
  simpa only [Function.comp_def, Prod.swap] using! h

theorem m64MovingCurve_energy_derivative_eq_divergence
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    {c : ℝ → ℝ → M} {O : Set (ℝ × ℝ)} (hO : IsOpen O)
    (hc : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n) ∞
      (fun q : ℝ × ℝ => c q.1 q.2) O) {t x : ℝ} (hp : (t, x) ∈ O) :
    deriv (fun r => (1 / 2 : ℝ) * g.inner (c r x)
        (curveVelocity (c r) x) (curveVelocity (c r) x)) t =
      deriv (fun y => g.inner (c t y) (curveVelocity (fun r => c r y) t)
        (curveVelocity (c t) y)) x -
      g.inner (c t x) (curveVelocity (fun r => c r x) t)
        (rampHorizontalCovariantDerivative D (c t)
          (fun y => curveVelocity (c t) y) x) := by
  have hline : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ) ∞
      (fun y : ℝ => (t, y)) x :=
    contMDiffAt_iff_contDiffAt.mpr (contDiffAt_const.prodMk contDiffAt_id)
  have hcurve : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n) (c t) x :=
    ((hc.contMDiffAt (hO.mem_nhds hp)).comp x hline).mdifferentiableAt (by simp)
  have hV := ((m64TwoParameter_first_velocity_contMDiffAt hO hc hp).comp x hline).mdifferentiableAt
    (by simp)
  have hX := ((m64TwoParameter_second_velocity_contMDiffAt hO hc hp).comp x hline).mdifferentiableAt
    (by simp)
  have hpair := M62.hasDerivAt_metric_pairing D hcurve hV hX
  have htime := m64MovingCurve_half_energy_hasDerivAt D hO hc hp
  rw [htime.deriv, hpair.deriv]
  ring

end PoincareConjecture
