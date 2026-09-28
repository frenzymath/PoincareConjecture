import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Stabilization.ShortBoundaryCollar
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Stabilization.BoundaryTimeJet
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Stabilization.BoundarySpeedBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M64

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem first_order_boundary_collar
    (g : RiemannianMetric n M) {f beta : ℝ × ℝ → M}
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hf : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n) 1 f (Ioo (-epsilon) epsilon ×ˢ univ))
    (hbeta : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n) 1 beta
      (Ioo (-epsilon) epsilon ×ˢ univ))
    (hperiodf : ∀ h ∈ Ioo (-epsilon) epsilon,
      Function.Periodic (fun x => f (h, x)) curvePeriod)
    (hperiodbeta : ∀ h ∈ Ioo (-epsilon) epsilon,
      Function.Periodic (fun x => beta (h, x)) curvePeriod)
    (hbase : ∀ x, f (0, x) = beta (0, x))
    (hvelocity : ∀ x, curveVelocity (n := n) (fun s => f (s, x)) 0 =
      curveVelocity (n := n) (fun s => beta (s, x)) 0) :
    ∀ eta : ℝ, 0 < eta → ∀ᶠ h : ℝ in 𝓝[>] 0,
      ∃ A : M64Annulus g (fun x => f (h, x)) (fun x => beta (h, x)),
        A.area ≤ eta * h := by
  obtain ⟨S0, -, hS0⟩ := boundary_motion_speed_bound g hepsilon hf
  obtain ⟨S1, -, hS1⟩ := boundary_motion_speed_bound g hepsilon hbeta
  obtain ⟨rho, hrho, C, hC, hcollar⟩ :=
    exists_short_boundary_collar g isCompact_univ (max S0 S1)
  intro eta heta
  obtain ⟨delta, hdelta, herror⟩ := uniform_boundary_time_jet_bound g hepsilon hf hbeta
    isCompact_Icc (fun x _ => hbase x) (fun x _ => hvelocity x) (div_pos heta hC)
  have htime : ∀ᶠ h : ℝ in 𝓝[>] 0, h ∈ Ioo (-epsilon / 2) (epsilon / 2) :=
    nhdsWithin_le_nhds (isOpen_Ioo.mem_nhds ⟨by linarith, half_pos hepsilon⟩)
  have hsmall : ∀ᶠ h : ℝ in 𝓝[>] 0, h ∈ Ioo (-delta) delta :=
    nhdsWithin_le_nhds (isOpen_Ioo.mem_nhds ⟨by linarith, hdelta⟩)
  have hshort : ∀ᶠ h : ℝ in 𝓝[>] 0, h < rho * C / eta :=
    nhdsWithin_le_nhds (Iio_mem_nhds (div_pos (mul_pos hrho hC) heta))
  filter_upwards [htime, hsmall, hshort, self_mem_nhdsWithin] with h hh hd hsh hpos
  change 0 < h at hpos
  have hheps : h ∈ Ioo (-epsilon) epsilon := ⟨by linarith [hh.1], by linarith [hh.2]⟩
  have hhalf : h ∈ Icc (-epsilon / 2) (epsilon / 2) := ⟨hh.1.le, hh.2.le⟩
  have hfe : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 (fun x => f (h, x)) :=
    hf.comp_contMDiff (contDiff_const.prodMk contDiff_id).contMDiff
      (fun x => ⟨hheps, mem_univ x⟩)
  have hbe : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 (fun x => beta (h, x)) :=
    hbeta.comp_contMDiff (contDiff_const.prodMk contDiff_id).contMDiff
      (fun x => ⟨hheps, mem_univ x⟩)
  have hpoint (x : ℝ) : g.edist (f (h, x)) (beta (h, x)) ≤
      ENNReal.ofReal (eta / C * h) := by
    have hp : Function.Periodic (fun x => (f (h, x), beta (h, x))) curvePeriod :=
      fun x => Prod.ext (hperiodf h hheps x) (hperiodbeta h hheps x)
    obtain ⟨y, hy, hxy⟩ := hp.exists_mem_Ico₀ (by unfold curvePeriod; positivity) x
    have h0 := congrArg Prod.fst hxy
    have h1 := congrArg Prod.snd hxy
    change f (h, x) = f (h, y) at h0
    change beta (h, x) = beta (h, y) at h1
    rw [h0, h1]
    simpa only [abs_of_pos hpos] using herror h hd y (Ico_subset_Icc_self hy)
  have heps : eta / C * h ≤ rho := by
    have hb := (lt_div_iff₀ heta).mp hsh
    calc
      eta / C * h = eta * h / C := by ring
      _ ≤ rho := (div_le_iff₀ hC).mpr (by nlinarith)
  obtain ⟨A, hA⟩ := hcollar (fun x => f (h, x)) (fun x => beta (h, x)) hfe hbe
    (hperiodf h hheps) (hperiodbeta h hheps)
    (fun x hx => (hS0 h hhalf x hx).trans (le_max_left _ _))
    (fun x hx => (hS1 h hhalf x hx).trans (le_max_right _ _))
    (eta / C * h) (by positivity) heps hpoint
  refine ⟨A, hA.trans_eq ?_⟩
  field_simp

end PoincareConjecture.M64
