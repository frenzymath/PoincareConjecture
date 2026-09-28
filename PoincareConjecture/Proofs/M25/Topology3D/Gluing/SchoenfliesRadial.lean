import PoincareConjecture.Proofs.M25.Mathlib.SmoothLeftInverseChart
import PoincareConjecture.Proofs.M25.Topology3D.Services
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.InnerProductSpace.Calculus











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M25.Topology3D.SchoenfliesData

variable {ψ : UnitTwoSphere × ℝ → E3} {δ : ℝ} (S : SchoenfliesData ψ δ)




theorem isOpen_chart_image : IsOpen (S.chart '' ball 0 S.radius) := by
  obtain ⟨Ψ, hΨ, hleft⟩ := S.chart_inverse
  exact S.chart_smooth.isOpen_image_of_leftInvOn hΨ isOpen_ball hleft (by simp) rfl




theorem exists_chart_openPartialHomeomorph :
    ∃ e : OpenPartialHomeomorph E3 E3,
      e.source = ball 0 S.radius ∧ e.target = S.chart '' ball 0 S.radius ∧
      (e : E3 → E3) = S.chart ∧ ContDiffOn ℝ ∞ e e.source ∧
      ContDiffOn ℝ ∞ e.symm e.target := by
  obtain ⟨Ψ, hΨ, hleft⟩ := S.chart_inverse
  obtain ⟨e, hs, ht, he, _, hf, hi⟩ :=
    S.chart_smooth.exists_openPartialHomeomorph_of_leftInvOn hΨ isOpen_ball hleft
      (by simp) rfl
  exact ⟨e, hs, ht, he, hf, hi⟩



private theorem side_mul_mem_Ioo (hδ : 0 ≤ δ) {s : ℝ} (hs : s ∈ Ioo δ 1) :
    S.side * s ∈ Ioo (-1 : ℝ) 1 := by
  have hpos : 0 < s := hδ.trans_lt hs.1
  rcases mul_self_eq_one_iff.mp S.side_sq with hside | hside
  · simp only [hside, one_mul, mem_Ioo]
    exact ⟨by linarith, hs.2⟩
  · simp only [hside, neg_one_mul, mem_Ioo]
    constructor <;> linarith [hs.2]




theorem contDiffOn_radial (hψ : IsCollarEmbedding ψ) (hδ : 0 ≤ δ) :
    ContDiffOn ℝ ∞ S.radial (Ioo δ 1) := by
  obtain ⟨q, hq⟩ := (NormedSpace.sphere_nonempty (E := E3) (x := 0) (r := 1)).mpr
    (by norm_num)
  let q₀ : UnitTwoSphere := ⟨q, hq⟩
  obtain ⟨e, hsource, htarget, he, _, hi⟩ := S.exists_chart_openPartialHomeomorph
  have hcurve : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E3) ∞
      (fun t : ℝ => ψ (q₀, S.side * t)) (Ioo δ 1) := by
    exact hψ.1.comp
      (contMDiff_const.prodMk (contDiff_const.mul contDiff_id).contMDiff).contMDiffOn
      (fun t ht => ⟨mem_univ q₀, S.side_mul_mem_Ioo hδ ht⟩)
  have hball (t : ℝ) (ht : t ∈ Ioo δ 1) :
      S.radial t • (S.boundary_map q₀).1 ∈ e.source := by
    rw [hsource, mem_ball_zero_iff]
    rw [norm_smul, Real.norm_eq_abs, mem_sphere_zero_iff_norm.mp (S.boundary_map q₀).2,
      mul_one, abs_of_pos (S.radial_pos t ⟨ht.1.le, ht.2⟩)]
    exact S.radial_lt t ⟨ht.1.le, ht.2⟩
  have hforward (t : ℝ) (ht : t ∈ Ioo δ 1) :
      e (S.radial t • (S.boundary_map q₀).1) = ψ (q₀, S.side * t) := by
    rw [he]
    exact S.chart_collar q₀ t ⟨ht.1.le, ht.2⟩
  have himage : MapsTo (fun t : ℝ => ψ (q₀, S.side * t)) (Ioo δ 1) e.target := by
    intro t ht
    change ψ (q₀, S.side * t) ∈ e.target
    rw [← hforward t ht]
    exact e.map_source (hball t ht)
  have hinverse (t : ℝ) (ht : t ∈ Ioo δ 1) :
      e.symm (ψ (q₀, S.side * t)) = S.radial t • (S.boundary_map q₀).1 := by
    rw [← hforward t ht, e.left_inv (hball t ht)]
  have hnorm (t : ℝ) (ht : t ∈ Ioo δ 1) :
      ‖e.symm (ψ (q₀, S.side * t))‖ = S.radial t := by
    rw [hinverse t ht, norm_smul, Real.norm_eq_abs,
      mem_sphere_zero_iff_norm.mp (S.boundary_map q₀).2, mul_one,
      abs_of_pos (S.radial_pos t ⟨ht.1.le, ht.2⟩)]
  have hinv : ContDiffOn ℝ ∞ (fun t : ℝ => e.symm (ψ (q₀, S.side * t))) (Ioo δ 1) :=
    (hi.contMDiffOn.comp hcurve himage).contDiffOn
  have hn : ContDiffOn ℝ ∞ (fun t : ℝ => ‖e.symm (ψ (q₀, S.side * t))‖) (Ioo δ 1) :=
    hinv.norm ℝ (fun t ht => norm_ne_zero_iff.mp ((hnorm t ht).trans_ne
      (S.radial_pos t ⟨ht.1.le, ht.2⟩).ne'))
  exact hn.congr fun t ht => (hnorm t ht).symm




theorem deriv_radial_ne_zero (hψ : IsCollarEmbedding ψ) (hδ : 0 ≤ δ)
    {s : ℝ} (hs : s ∈ Ioo δ 1) : deriv S.radial s ≠ 0 := by
  obtain ⟨q, hq⟩ := (NormedSpace.sphere_nonempty (E := E3) (x := 0) (r := 1)).mpr
    (by norm_num)
  let q₀ : UnitTwoSphere := ⟨q, hq⟩
  let u : E3 := (S.boundary_map q₀).1
  have hball : S.radial s • u ∈ ball 0 S.radius := by
    rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs]
    have hu : ‖u‖ = 1 := mem_sphere_zero_iff_norm.mp (S.boundary_map q₀).2
    rw [hu, mul_one, abs_of_pos (S.radial_pos s ⟨hs.1.le, hs.2⟩)]
    exact S.radial_lt s ⟨hs.1.le, hs.2⟩
  have hr := ((S.contDiffOn_radial hψ hδ).contDiffAt
    (isOpen_Ioo.mem_nhds hs)).differentiableAt (by simp)
  have hC := (S.chart_smooth.contDiffAt (isOpen_ball.mem_nhds hball)).differentiableAt
    (by simp)
  intro hz
  have hrad : HasDerivAt (fun t : ℝ => S.radial t • u) 0 s := by
    simpa only [hz, zero_smul] using hr.hasDerivAt.smul_const u
  have hzero : HasDerivAt (fun t : ℝ => ψ (q₀, S.side * t)) 0 s := by
    have hc : HasDerivAt (fun t : ℝ => S.chart (S.radial t • u)) 0 s := by
      simpa only [Function.comp_def, map_zero] using! hC.hasFDerivAt.comp_hasDerivAt s hrad
    apply hc.congr_of_eventuallyEq
    filter_upwards [isOpen_Ioo.mem_nhds hs] with t ht
    exact (S.chart_collar q₀ t ⟨ht.1.le, ht.2⟩).symm
  have hpoint : (q₀, S.side * s) ∈ (univ ×ˢ Ioo (-1 : ℝ) 1) :=
    ⟨mem_univ _, S.side_mul_mem_Ioo hδ hs⟩
  have hψs := (hψ.1.contMDiffAt ((isOpen_univ.prod isOpen_Ioo).mem_nhds hpoint)).mdifferentiableAt
    (by simp)
  have hmul : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun t : ℝ => S.side * t) :=
    (contDiff_const.mul contDiff_id).contMDiff
  have hj : MDifferentiableAt 𝓘(ℝ, ℝ) ((𝓡 2).prod 𝓘(ℝ, ℝ))
      (fun t : ℝ => (q₀, S.side * t)) s :=
    mdifferentiableAt_const.prodMk ((hmul s).mdifferentiableAt (by simp))
  have hja : mfderiv 𝓘(ℝ, ℝ) ((𝓡 2).prod 𝓘(ℝ, ℝ))
      (fun t : ℝ => (q₀, S.side * t)) s 1 = (0, S.side) := by
    rw [mfderiv_prodMk mdifferentiableAt_const ((hmul s).mdifferentiableAt (by simp))]
    change ((mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (fun _ : ℝ => q₀) s) 1,
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => S.side * t) s) 1) = (0, S.side)
    apply Prod.ext
    · rw [mfderiv_const]
      rfl
    · rw [mfderiv_eq_fderiv]
      change deriv (fun t : ℝ => S.side * t) s = S.side
      simp
  have hchain : mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E3) ψ (q₀, S.side * s)
      (0, S.side) = 0 := by
    have h := mfderiv_comp_apply s hψs hj (1 : ℝ)
    rw [hja, mfderiv_eq_fderiv] at h
    change deriv (fun t : ℝ => ψ (q₀, S.side * t)) s = _ at h
    rw [hzero.deriv] at h
    exact h.symm
  have hvector : (0, S.side) = (0 : EuclideanSpace ℝ (Fin 2) × ℝ) :=
    hψ.2.2 _ hpoint (by simpa only [map_zero] using hchain)
  have hside : S.side = 0 := congrArg Prod.snd hvector
  have := S.side_sq
  simp [hside] at this




theorem deriv_radial_pos (hψ : IsCollarEmbedding ψ) (hδ : 0 ≤ δ)
    {s : ℝ} (hs : s ∈ Ioo δ 1) : 0 < deriv S.radial s := by
  have hmono : MonotoneOn S.radial (Ioo δ 1) :=
    S.radial_strictMono.monotoneOn.mono Ioo_subset_Ico_self
  have hnonneg := hmono.derivWithin_nonneg (x := s)
  rw [derivWithin_of_isOpen isOpen_Ioo hs] at hnonneg
  exact lt_of_le_of_ne hnonneg (S.deriv_radial_ne_zero hψ hδ hs).symm

end PoincareConjecture.M25.Topology3D.SchoenfliesData
