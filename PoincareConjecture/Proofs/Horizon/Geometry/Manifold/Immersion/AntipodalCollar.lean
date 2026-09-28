import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.Immersion.Even
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Analysis.Normed.Module.Connected

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Metric
open scoped Manifold ContDiff Topology

noncomputable section

namespace Poincare.Manifold

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev S2 := sphere (0 : E3) 1
private abbrev cylinderModel := (𝓡 2).prod 𝓘(ℝ, ℝ)

private instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨finrank_euclideanSpace_fin⟩

private def radialCoordinates (q₀ : S2) (x : E3) : S2 × ℝ :=
  if hx : x = 0 then (q₀, 0) else
    (⟨‖x‖⁻¹ • x, by simp [norm_smul, norm_ne_zero_iff.mpr hx]⟩, ‖x‖ - 1)

private def radialRealization (z : S2 × ℝ) : E3 := (z.2 + 1) • z.1.val

private theorem radialCoordinates_sphere (q₀ q : S2) :
    radialCoordinates q₀ q.val = (q, 0) := by
  have hq : q.val ≠ 0 := ne_zero_of_mem_unit_sphere q
  have hn : ‖q.val‖ = 1 := by simp
  simp [radialCoordinates, hq, hn]

private theorem radialRealization_coordinates (q₀ : S2) {x : E3} (hx : x ≠ 0) :
    radialRealization (radialCoordinates q₀ x) = x := by
  simp [radialCoordinates, radialRealization, hx, smul_smul, norm_ne_zero_iff.mpr hx]

private theorem radialCoordinates_neg (q₀ : S2) {x : E3} (hx : x ≠ 0) :
    radialCoordinates q₀ (-x) = (-(radialCoordinates q₀ x).1,
      (radialCoordinates q₀ x).2) := by
  simp only [radialCoordinates, hx, neg_ne_zero.mpr hx, dite_false, norm_neg]
  apply Prod.ext
  · apply Subtype.ext
    exact smul_neg _ _
  · rfl

private theorem contMDiffAt_radialCoordinates (q₀ : S2) {x : E3} (hx : x ≠ 0) :
    ContMDiffAt (𝓡 3) cylinderModel ∞ (radialCoordinates q₀) x := by
  let U : TopologicalSpace.Opens E3 := ⟨{0}ᶜ, isOpen_compl_singleton⟩
  let xU : U := ⟨x, hx⟩
  have hn : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (fun y : U => ‖y.val‖) := by
    intro y
    exact (contDiffAt_norm ℝ y.property).contMDiffAt.comp y (contMDiff_subtype_val y)
  have hs : ContMDiff (𝓡 3) (𝓡 2) ∞
      (fun y : U => (⟨‖y.val‖⁻¹ • y.val, by
        simp [norm_smul, norm_ne_zero_iff.mpr y.property]⟩ : S2)) :=
    ((hn.inv₀ (fun y => norm_ne_zero_iff.mpr y.property)).smul
      contMDiff_subtype_val).codRestrict_sphere _
  have h : ContMDiff (𝓡 3) cylinderModel ∞ (fun y : U => radialCoordinates q₀ y.val) := by
    convert hs.prodMk (hn.sub (contMDiff_const (c := (1 : ℝ)))) using 1
    funext y
    exact dif_neg y.property
  exact contMDiffAt_subtype_iff.mp (h xU)

private theorem contMDiff_radialRealization :
    ContMDiff cylinderModel (𝓡 3) ∞ radialRealization :=
  (contMDiff_snd.add contMDiff_const).smul (contMDiff_coe_sphere.comp contMDiff_fst)

private theorem injective_mfderiv_radialCoordinates (q₀ : S2) {x : E3} (hx : x ≠ 0) :
    Function.Injective (mfderiv (𝓡 3) cylinderModel (radialCoordinates q₀) x) := by
  have heq : radialRealization ∘ radialCoordinates q₀ =ᶠ[𝓝 x] id := by
    filter_upwards [isOpen_ne.mem_nhds hx] with y hy
    exact radialRealization_coordinates q₀ hy
  have hd := mfderiv_comp x
    (contMDiff_radialRealization.mdifferentiable (by simp) _)
    ((contMDiffAt_radialCoordinates q₀ hx).mdifferentiableAt (by simp))
  rw [heq.mfderiv_eq, mfderiv_id] at hd
  intro u v huv
  have h := congrArg (mfderiv cylinderModel (𝓡 3) radialRealization
    (radialCoordinates q₀ x)) huv
  rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.comp_apply, ← hd] at h
  exact h

theorem not_forall_injective_mfderiv_of_locally_antipodal
    (F : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ → EuclideanSpace ℝ (Fin 3))
    (hF : ∀ q, ContMDiffAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ F (q, 0))
    (heven : ∀ q, ∀ᶠ z in 𝓝 (q, (0 : ℝ)), F (-z.1, z.2) = F z) :
    ¬ ∀ q, Function.Injective (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) F (q, 0)) := by
  intro hinj
  have hs : IsConnected (sphere (0 : E3) 1) :=
    isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp [E3])) _ zero_le_one
  obtain ⟨q₀, hq₀⟩ := hs.nonempty
  let q₀S : S2 := ⟨q₀, hq₀⟩
  let f : E3 → E3 := F ∘ radialCoordinates q₀S
  have hcoord (x : E3) (hx : x ∈ sphere (0 : E3) 1) :
      radialCoordinates q₀S x = (⟨x, hx⟩, 0) := radialCoordinates_sphere q₀S ⟨x, hx⟩
  have hsmooth : ∀ x ∈ sphere (0 : E3) 1, ContDiffAt ℝ 1 f x := by
    intro x hx
    have hfx : ContMDiffAt cylinderModel (𝓡 3) ∞ F (radialCoordinates q₀S x) := by
      rw [hcoord x hx]
      exact hF ⟨x, hx⟩
    exact (hfx.comp x (contMDiffAt_radialCoordinates q₀S
      (ne_zero_of_mem_unit_sphere ⟨x, hx⟩))).contDiffAt.of_le (by simp)
  have heven' : ∀ x ∈ sphere (0 : E3) 1, ∀ᶠ y in 𝓝 x, f (-y) = f y := by
    intro x hx
    have hx0 := ne_zero_of_mem_unit_sphere (⟨x, hx⟩ : S2)
    have hc := (contMDiffAt_radialCoordinates q₀S hx0).continuousAt
    change Tendsto (radialCoordinates q₀S) (𝓝 x) (𝓝 (radialCoordinates q₀S x)) at hc
    rw [hcoord x hx] at hc
    have hev := hc (heven ⟨x, hx⟩)
    filter_upwards [hev, isOpen_ne.mem_nhds hx0] with y hy hy0
    change F (radialCoordinates q₀S (-y)) = F (radialCoordinates q₀S y)
    rw [radialCoordinates_neg q₀S hy0]
    exact hy
  apply not_forall_isInvertible_fderiv_of_locally_even
    (E := E3) (by rw [finrank_euclideanSpace_fin]; exact ⟨1, rfl⟩) hs
    (fun x hx => by simpa only [mem_sphere_zero_iff_norm, norm_neg] using hx)
    hsmooth heven'
  intro x hx
  have hx0 := ne_zero_of_mem_unit_sphere (⟨x, hx⟩ : S2)
  have hfx : MDifferentiableAt cylinderModel (𝓡 3) F (radialCoordinates q₀S x) := by
    rw [hcoord x hx]
    exact (hF ⟨x, hx⟩).mdifferentiableAt (by simp)
  have hchain : fderiv ℝ f x =
      (mfderiv cylinderModel (𝓡 3) F (radialCoordinates q₀S x)).comp
        (mfderiv (𝓡 3) cylinderModel (radialCoordinates q₀S) x) := by
    exact (mfderiv_eq_fderiv (f := f)).symm.trans
      (mfderiv_comp x hfx ((contMDiffAt_radialCoordinates q₀S hx0).mdifferentiableAt (by simp)))
  have hix : Function.Injective (fderiv ℝ f x) := by
    rw [hchain, hcoord x hx]
    exact (hinj ⟨x, hx⟩).comp (injective_mfderiv_radialCoordinates q₀S hx0)
  let L : E3 ≃L[ℝ] E3 := ContinuousLinearEquiv.ofBijective (fderiv ℝ f x)
    (LinearMap.ker_eq_bot.mpr hix)
    (LinearMap.range_eq_top.mpr (LinearMap.injective_iff_surjective.mp hix))
  exact ⟨L, rfl⟩

theorem not_isLocalDiffeomorphOn_antipodal_collar {a : ℝ} (ha : 0 < a)
    (F : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ → EuclideanSpace ℝ (Fin 3))
    (heven : ∀ q t, t ∈ Ioo (-a) a → F (-q, t) = F (q, t)) :
    ¬ IsLocalDiffeomorphOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ F
      (univ ×ˢ Ioo (-a) a) := by
  intro hlocal
  have hzero : (0 : ℝ) ∈ Ioo (-a) a := ⟨neg_neg_of_pos ha, ha⟩
  have hloc (q : S2) := hlocal ⟨(q, 0), ⟨mem_univ q, hzero⟩⟩
  apply not_forall_injective_mfderiv_of_locally_antipodal F
    (fun q => (hloc q).contMDiffAt)
  · intro q
    filter_upwards [(isOpen_univ.prod isOpen_Ioo).mem_nhds
      (show (q, (0 : ℝ)) ∈ univ ×ˢ Ioo (-a) a from ⟨mem_univ q, hzero⟩)] with z hz
    exact heven z.1 z.2 hz.2
  · intro q
    exact ((hloc q).mfderivToContinuousLinearEquiv (by simp)).injective

end Poincare.Manifold
