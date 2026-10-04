import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Analysis.Compactness.UniformCompactComposition
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Compact convergence under the differentiated chain rule

Compact C1 convergence is preserved by a smooth outer map on a
neighborhood of the limiting image. This is used for the geodesic
and variational operators in Morgan--Tian, Claim 16.6, pp. 371-372;
see `derivations/17-first-variational-convergence.md`.
-/

set_option autoImplicit false

open Set Filter Metric
open scoped ContDiff Topology

/-- Pairing two uniformly convergent families with the same index
filter preserves uniform convergence. -/
theorem TendstoUniformlyOn.prodMk_same
    {P E F ι : Type*} [UniformSpace E] [UniformSpace F] {l : Filter ι}
    {fseq : ι → P → E} {f : P → E} {gseq : ι → P → F} {g : P → F} {K : Set P}
    (hf : TendstoUniformlyOn fseq f l K) (hg : TendstoUniformlyOn gseq g l K) :
    TendstoUniformlyOn (fun i x => (fseq i x, gseq i x)) (fun x => (f x, g x)) l K := by
  intro u hu
  exact (tendsto_id.prodMk tendsto_id).eventually ((hf.prodMk hg) u hu)

/-- Currying a convergent first multilinear derivative gives convergence
of the ordinary continuous linear derivative. -/
theorem tendstoUniformlyOn_fderiv_of_iteratedFDeriv_one
    {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {l : Filter ι}
    {fseq : ι → E → F} {f : E → F} {K : Set E}
    (h : TendstoUniformlyOn (fun i => iteratedFDeriv ℝ 1 (fseq i))
      (iteratedFDeriv ℝ 1 f) l K) :
    TendstoUniformlyOn (fun i => fderiv ℝ (fseq i)) (fderiv ℝ f) l K := by
  have he (B : E → F) :
      (fun x => continuousMultilinearCurryFin1 ℝ E F (iteratedFDeriv ℝ 1 B x)) =
        fderiv ℝ B := by
    funext x
    apply ContinuousLinearMap.ext
    intro v
    simp [continuousMultilinearCurryFin1_apply, iteratedFDeriv_one_apply]
  simpa only [Function.comp_def, he] using
    (continuousMultilinearCurryFin1 ℝ E F).isometry.uniformContinuous.comp_tendstoUniformlyOn h

/-- The right currying isometry converts convergence of order j+1
into order j convergence of the derivative, without smoothness assumptions
on totalized derivatives outside the set in question. -/
theorem tendstoUniformlyOn_iteratedFDeriv_fderiv
    {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {l : Filter ι}
    {fseq : ι → E → F} {f : E → F} {K : Set E} {j : ℕ}
    (h : TendstoUniformlyOn (fun i => iteratedFDeriv ℝ (j + 1) (fseq i))
      (iteratedFDeriv ℝ (j + 1) f) l K) :
    TendstoUniformlyOn (fun i => iteratedFDeriv ℝ j (fderiv ℝ (fseq i)))
      (iteratedFDeriv ℝ j (fderiv ℝ f)) l K := by
  have he (B : E → F) (x : E) :
      continuousMultilinearCurryRightEquiv' ℝ j E F (iteratedFDeriv ℝ (j + 1) B x) =
        iteratedFDeriv ℝ j (fderiv ℝ B) x := by
    rw [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply,
      LinearIsometryEquiv.apply_symm_apply]
  have hc := (continuousMultilinearCurryRightEquiv' ℝ j E F).isometry.uniformContinuous
  simpa only [Function.comp_def, he] using hc.comp_tendstoUniformlyOn h

/-- Uniform convergence into a compact limiting image eventually puts
all approximate images in any open neighborhood of that image. -/
theorem TendstoUniformlyOn.eventually_mapsTo_of_compact_image
    {P E ι : Type*} [MetricSpace E] {l : Filter ι}
    {fseq : ι → P → E} {f : P → E} {K : Set P} {U : Set E}
    (hconv : TendstoUniformlyOn fseq f l K)
    (hf : IsCompact (f '' K)) (hU : IsOpen U) (hfU : MapsTo f K U) :
    ∀ᶠ i in l, MapsTo (fseq i) K U := by
  obtain ⟨delta, hdelta, hthick⟩ :=
    hf.exists_cthickening_subset_open hU (image_subset_iff.mpr hfU)
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hconv delta hdelta] with i hi
  intro x hx
  exact hthick (mem_cthickening_of_dist_le (fseq i x) (f x) delta (f '' K)
    (mem_image_of_mem f hx) (by simpa only [dist_comm] using (hi x hx).le))

/-- The chain rule preserves compact uniform convergence of first
derivatives when the fixed outer map is C1 near the limiting image. -/
theorem tendstoUniformlyOn_fderiv_comp_of_compact
    {E F G ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {l : Filter ι} {fseq : ι → E → F} {f : E → F} {g : F → G}
    {K : Set E} {U : Set F} (hK : IsCompact K) (hU : IsOpen U)
    (hf : ∀ x ∈ K, ContDiffAt ℝ 1 f x) (hg : ContDiffOn ℝ 1 g U)
    (hfU : MapsTo f K U)
    (hfseq : ∀ᶠ i in l, ∀ x ∈ K, DifferentiableAt ℝ (fseq i) x)
    (hzero : TendstoUniformlyOn fseq f l K)
    (hone : TendstoUniformlyOn (fun i => fderiv ℝ (fseq i)) (fderiv ℝ f) l K) :
    TendstoUniformlyOn (fun i => fderiv ℝ (g ∘ fseq i)) (fderiv ℝ (g ∘ f)) l K := by
  let J (x : E) := (f x, fderiv ℝ f x)
  let Jseq (i : ι) (x : E) := (fseq i x, fderiv ℝ (fseq i) x)
  have hfcont : ContinuousOn f K := fun x hx => (hf x hx).continuousAt.continuousWithinAt
  have hdcont : ContinuousOn (fderiv ℝ f) K := fun x hx =>
    ((hf x hx).fderiv_right (m := 0) (by simp)).continuousAt.continuousWithinAt
  have hJ : TendstoUniformlyOn Jseq J l K := by
    intro u hu
    exact (tendsto_id.prodMk tendsto_id).eventually ((hzero.prodMk hone) u hu)
  let H (z : F × (E →L[ℝ] F)) : E →L[ℝ] G := (fderiv ℝ g z.1).comp z.2
  have hH : ContinuousOn H (U ×ˢ univ) :=
    ((hg.continuousOn_fderiv_of_isOpen hU le_rfl).comp continuousOn_fst
      (fun _ hz => hz.1)).clm_comp continuousOn_snd
  have hlim := hH.comp_tendstoUniformlyOn_of_compact_image (hU.prod isOpen_univ)
    (hK.image_of_continuousOn (hfcont.prodMk hdcont))
    (fun x hx => ⟨hfU hx, mem_univ _⟩) hJ
  have hfit := hzero.eventually_mapsTo_of_compact_image
    (hK.image_of_continuousOn hfcont) hU hfU
  have heq : ∀ᶠ i in l, ∀ x ∈ K, fderiv ℝ (g ∘ fseq i) x = H (Jseq i x) := by
    filter_upwards [hfseq, hfit] with i hi him
    intro x hx
    exact fderiv_comp x ((hg.contDiffAt (hU.mem_nhds (him hx))).differentiableAt one_ne_zero)
      (hi x hx)
  have heqmodel : ∀ x ∈ K, fderiv ℝ (g ∘ f) x = H (J x) := by
    intro x hx
    exact fderiv_comp x ((hg.contDiffAt (hU.mem_nhds (hfU hx))).differentiableAt one_ne_zero)
      ((hf x hx).differentiableAt one_ne_zero)
  rw [Metric.tendstoUniformlyOn_iff] at hlim ⊢
  intro epsilon hepsilon
  filter_upwards [heq, hlim epsilon hepsilon] with i hi hdist
  intro x hx
  rw [hi x hx, heqmodel x hx]
  exact hdist x hx
