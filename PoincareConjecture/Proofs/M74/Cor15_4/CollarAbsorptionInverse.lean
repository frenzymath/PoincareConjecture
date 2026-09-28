import PoincareConjecture.Proofs.M74.ServiceMirror
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

set_option autoImplicit false

open Set Filter Function
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M74

local notation "Track" => ℝ × UnitTwoSphere
local notation "VTrack" => ℝ × EuclideanSpace ℝ (Fin 2)
local notation "ITrack" => ModelWithCorners.prod 𝓘(ℝ, ℝ) (𝓡 2)

private theorem productEquiv_symm_contMDiff (e : Track ≃ Track)
    (he : ContMDiff ITrack ITrack ∞ e)
    (hderiv : ∀ x, Bijective (mfderiv ITrack ITrack e x)) :
    ContMDiff ITrack ITrack ∞ e.symm := by
  intro y
  let x := e.symm y
  suffices h : ContMDiffAt ITrack ITrack ∞ e.symm (e x) by
    simpa only [x, e.apply_symm_apply] using h
  let c := extChartAt ITrack x
  let d := extChartAt ITrack (e x)
  let F := writtenInExtChartAt ITrack ITrack x e
  have hF : ContDiffAt ℝ ∞ F (c x) := by
    simpa [F, c, writtenInExtChartAt, (ITrack).range_eq_univ,
      contDiffWithinAt_univ] using (contMDiffAt_iff.mp (he x)).2
  have hderiv_eq : mfderiv ITrack ITrack e x = fderiv ℝ F (c x) := by
    erw [mfderiv, if_pos ((he x).mdifferentiableAt (by simp))]
    simp only [(ITrack).range_eq_univ, fderivWithin_univ]
    rfl
  have hFbij : Bijective (fderiv ℝ F (c x)) := hderiv_eq ▸ hderiv x
  let L := ContinuousLinearEquiv.ofBijective (fderiv ℝ F (c x))
    (LinearMap.ker_eq_bot.mpr hFbij.1) (LinearMap.range_eq_top.mpr hFbij.2)
  have hdF : HasFDerivAt F (L : VTrack →L[ℝ] VTrack) (c x) :=
    (hF.differentiableAt (by simp)).hasFDerivAt
  let i := hF.localInverse hdF (by simp)
  have hFx : F (c x) = d (e x) := by
    change d (e (c.symm (c x))) = d (e x)
    rw [c.left_inv (mem_extChartAt_source x)]
  have hi : ContDiffAt ℝ ∞ i (d (e x)) := by
    rw [← hFx]
    exact hF.to_localInverse hdF (by simp)
  have hix : i (d (e x)) = c x := by
    rw [← hFx]
    exact hF.localInverse_apply_image hdF (by simp)
  have hc : ContMDiffAt 𝓘(ℝ, VTrack) ITrack ∞ c.symm (i (d (e x))) := by
    rw [hix]
    exact (contMDiffOn_extChartAt_symm x).contMDiffAt
      ((isOpen_extChartAt_target (I := ITrack) x).mem_nhds (mem_extChartAt_target x))
  let J : Track → Track := fun z => c.symm (i (d z))
  have hiM : ContMDiffAt 𝓘(ℝ, VTrack) 𝓘(ℝ, VTrack) ∞ i (d (e x)) :=
    hi.contMDiffAt
  have hdM : ContMDiffAt ITrack 𝓘(ℝ, VTrack) ∞ d (e x) := contMDiffAt_extChartAt
  have hJ : ContMDiffAt ITrack ITrack ∞ J (e x) :=
    hc.comp (e x) (hiM.comp (e x) hdM)
  have hJx : J (e x) = x := by
    change c.symm (i (d (e x))) = x
    rw [hix, c.left_inv (mem_extChartAt_source x)]
  have hright : ∀ᶠ z in 𝓝 (d (e x)), F (i z) = z := by
    rw [← hFx]
    exact (hF.hasStrictFDerivAt' hdF (by simp)).eventually_right_inverse
  have hmap : ContinuousAt (fun z => e (J z)) (e x) :=
    he.continuous.continuousAt.comp hJ.continuousAt
  have hmap_target : ∀ᶠ z in 𝓝 (e x), e (J z) ∈ d.source := by
    apply hmap.tendsto.eventually
    apply (isOpen_extChartAt_source (I := ITrack) (e x)).mem_nhds
    rw [hJx]
    exact mem_extChartAt_source (e x)
  have hsame : e.symm =ᶠ[𝓝 (e x)] J := by
    filter_upwards [hmap_target,
      extChartAt_source_mem_nhds (I := ITrack) (e x),
      (continuousAt_extChartAt (I := ITrack) (e x)).tendsto.eventually hright] with z hz hz' hi'
    apply e.injective
    rw [e.apply_symm_apply]
    apply d.injOn hz' hz
    exact hi'.symm
  exact hJ.congr_of_eventuallyEq hsame

theorem isotopyTrack_bijective {F : ℝ → UnitTwoSphere → UnitTwoSphere}
    (hFt : ∀ t : ℝ, ∃ g : Diffeomorph (𝓡 2) (𝓡 2)
      UnitTwoSphere UnitTwoSphere ∞, ∀ q, g q = F t q) :
    Bijective (fun p : Track => (p.1, F p.1 p.2)) := by
  constructor
  · rintro ⟨t, q⟩ ⟨u, r⟩ h
    have htime : t = u := congrArg Prod.fst h
    subst u
    obtain ⟨g, hg⟩ := hFt t
    refine Prod.ext rfl ?_
    apply g.injective
    change g q = g r
    simpa only [hg q, hg r] using congrArg Prod.snd h
  · rintro ⟨t, q⟩
    obtain ⟨g, hg⟩ := hFt t
    exact ⟨(t, g.symm q), Prod.ext rfl ((hg _).symm.trans (g.apply_symm_apply q))⟩

theorem isotopyTrack_mfderiv_bijective {F : ℝ → UnitTwoSphere → UnitTwoSphere}
    (hF : ContMDiff ITrack (𝓡 2) ∞ (fun p : Track => F p.1 p.2))
    (hFt : ∀ t : ℝ, ∃ g : Diffeomorph (𝓡 2) (𝓡 2)
      UnitTwoSphere UnitTwoSphere ∞, ∀ q, g q = F t q) (p : Track) :
    Bijective (mfderiv ITrack ITrack (fun z : Track => (z.1, F z.1 z.2)) p) := by
  let A : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
    mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (fun t => F t p.2) p.1
  let B : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
    mfderiv (𝓡 2) (𝓡 2) (F p.1) p.2
  have hB : Bijective B := by
    obtain ⟨g, hg⟩ := hFt p.1
    have hfg : F p.1 = g := funext (fun q => (hg q).symm)
    dsimp only [B]
    rw [hfg]
    exact (g.mfderivToContinuousLinearEquiv (by simp) p.2).bijective
  have hformula (a : ℝ) (v : EuclideanSpace ℝ (Fin 2)) :
      mfderiv ITrack ITrack (fun z : Track => (z.1, F z.1 z.2)) p (a, v) =
        (a, A a + B v) := by
    rw [mfderiv_prodMk mdifferentiableAt_fst ((hF.mdifferentiable (by simp)) p),
      mfderiv_fst, mfderiv_prod_eq_add_comp ((hF.mdifferentiable (by simp)) p)]
    rfl
  constructor
  · rintro ⟨a, v⟩ ⟨b, w⟩ h
    rw [hformula, hformula] at h
    have hab : a = b := congrArg Prod.fst h
    subst b
    refine Prod.ext rfl ?_
    apply hB.1
    exact add_left_cancel (congrArg Prod.snd h)
  · rintro ⟨a, w⟩
    obtain ⟨v, hv⟩ := hB.2 (w - A a)
    refine ⟨(a, v), ?_⟩
    rw [hformula, hv]
    simp
    rfl

noncomputable def sphereIsotopyTrackDiffeomorph
    {F : ℝ → UnitTwoSphere → UnitTwoSphere}
    (hF : ContMDiff ITrack (𝓡 2) ∞ (fun p : Track => F p.1 p.2))
    (hFt : ∀ t : ℝ, ∃ g : Diffeomorph (𝓡 2) (𝓡 2)
      UnitTwoSphere UnitTwoSphere ∞, ∀ q, g q = F t q) :
    Diffeomorph ITrack ITrack Track Track ∞ := by
  let e : Track ≃ Track := Equiv.ofBijective (fun p => (p.1, F p.1 p.2))
    (isotopyTrack_bijective hFt)
  have hs : ContMDiff ITrack ITrack ∞ e := contMDiff_fst.prodMk hF
  exact {
    toEquiv := e
    contMDiff_toFun := hs
    contMDiff_invFun := productEquiv_symm_contMDiff e hs
      (isotopyTrack_mfderiv_bijective hF hFt) }

@[simp] theorem sphereIsotopyTrackDiffeomorph_apply
    {F : ℝ → UnitTwoSphere → UnitTwoSphere}
    (hF : ContMDiff ITrack (𝓡 2) ∞ (fun p : Track => F p.1 p.2))
    (hFt : ∀ t : ℝ, ∃ g : Diffeomorph (𝓡 2) (𝓡 2)
      UnitTwoSphere UnitTwoSphere ∞, ∀ q, g q = F t q) (p : Track) :
    sphereIsotopyTrackDiffeomorph hF hFt p = (p.1, F p.1 p.2) := rfl

@[simp] theorem sphereIsotopyTrackDiffeomorph_symm_fst
    {F : ℝ → UnitTwoSphere → UnitTwoSphere}
    (hF : ContMDiff ITrack (𝓡 2) ∞ (fun p : Track => F p.1 p.2))
    (hFt : ∀ t : ℝ, ∃ g : Diffeomorph (𝓡 2) (𝓡 2)
      UnitTwoSphere UnitTwoSphere ∞, ∀ q, g q = F t q) (p : Track) :
    ((sphereIsotopyTrackDiffeomorph hF hFt).symm p).1 = p.1 := by
  have h := congrArg Prod.fst ((sphereIsotopyTrackDiffeomorph hF hFt).apply_symm_apply p)
  simpa only [sphereIsotopyTrackDiffeomorph_apply] using h

end PoincareConjecture.M74
