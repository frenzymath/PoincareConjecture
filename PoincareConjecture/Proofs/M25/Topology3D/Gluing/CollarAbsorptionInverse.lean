import PoincareConjecture.Proofs.M25.Topology3D.Services
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Geometry.Manifold.LocalDiffeomorph

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Function
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M25.Topology3D

section InverseInCharts

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace H M] [ChartedSpace H N]

private theorem collar_map_nhds_eq {f : M → N} {x : M}
    (hf : ContMDiffAt I I ∞ f x)
    (hbij : Bijective (mfderiv I I f x)) :
    map f (𝓝 x) = 𝓝 (f x) := by
  let c := extChartAt I x
  let d := extChartAt I (f x)
  let F := writtenInExtChartAt I I x f
  have hF : ContDiffAt ℝ ∞ F (c x) := by
    simpa [F, c, writtenInExtChartAt, I.range_eq_univ, contDiffWithinAt_univ] using
      (contMDiffAt_iff.mp hf).2
  have hderiv : mfderiv I I f x = fderiv ℝ F (c x) := by
    rw [mfderiv, if_pos (hf.mdifferentiableAt (by simp))]
    simp [F, c, I.range_eq_univ]
  have hFbij : Bijective (fderiv ℝ F (c x)) := by
    rwa [hderiv] at hbij
  let e := ContinuousLinearEquiv.ofBijective (fderiv ℝ F (c x))
    (LinearMap.ker_eq_bot.mpr hFbij.1) (LinearMap.range_eq_top.mpr hFbij.2)
  have hstrict : HasStrictFDerivAt F (e : E →L[ℝ] E) (c x) :=
    hF.hasStrictFDerivAt' (hF.differentiableAt (by simp)).hasFDerivAt (by simp)
  have hcmap : map c.symm (𝓝 (c x)) = 𝓝 x := by
    simpa [c, I.range_eq_univ] using map_extChartAt_symm_nhdsWithin_range (I := I) x
  have hdmap : map d.symm (𝓝 (d (f x))) = 𝓝 (f x) := by
    simpa [d, I.range_eq_univ] using map_extChartAt_symm_nhdsWithin_range (I := I) (f x)
  have hfc : Tendsto (f ∘ c.symm) (𝓝 (c x)) (𝓝 (f x)) :=
    hf.continuousAt.tendsto.comp hcmap.le
  have heq : d.symm ∘ F =ᶠ[𝓝 (c x)] f ∘ c.symm := by
    filter_upwards [hfc.eventually
      ((isOpen_extChartAt_source (I := I) (f x)).mem_nhds
        (mem_extChartAt_source (I := I) (f x)))] with y hy
    exact d.left_inv hy
  have hFx : F (c x) = d (f x) := by simp [F, c, d, writtenInExtChartAt]
  calc
    map f (𝓝 x) = map (f ∘ c.symm) (𝓝 (c x)) := by rw [← map_map, hcmap]
    _ = map (d.symm ∘ F) (𝓝 (c x)) := map_congr heq.symm
    _ = map d.symm (map F (𝓝 (c x))) := (map_map ..).symm
    _ = map d.symm (𝓝 (F (c x))) := by rw [hstrict.map_nhds_eq_of_equiv]
    _ = 𝓝 (f x) := by rw [hFx, hdmap]

private theorem collar_contMDiffAt_left_inverse
    [IsManifold I ∞ M] [IsManifold I ∞ N]
    {f : M → N} {g : N → M} {x : M}
    (hf : ContMDiffAt I I ∞ f x)
    (hbij : Bijective (mfderiv I I f x))
    (hleft : ∀ᶠ z in 𝓝 x, g (f z) = z) :
    ContMDiffAt I I ∞ g (f x) := by
  let c := extChartAt I x
  let d := extChartAt I (f x)
  let F := writtenInExtChartAt I I x f
  have hF : ContDiffAt ℝ ∞ F (c x) := by
    simpa [F, c, writtenInExtChartAt, I.range_eq_univ, contDiffWithinAt_univ] using
      (contMDiffAt_iff.mp hf).2
  have hderiv : mfderiv I I f x = fderiv ℝ F (c x) := by
    rw [mfderiv, if_pos (hf.mdifferentiableAt (by simp))]
    simp [F, c, I.range_eq_univ]
  have hFbij : Bijective (fderiv ℝ F (c x)) := by
    rwa [hderiv] at hbij
  let e := ContinuousLinearEquiv.ofBijective (fderiv ℝ F (c x))
    (LinearMap.ker_eq_bot.mpr hFbij.1) (LinearMap.range_eq_top.mpr hFbij.2)
  have hdF : HasFDerivAt F (e : E →L[ℝ] E) (c x) :=
    (hF.differentiableAt (by simp)).hasFDerivAt
  let i := hF.localInverse hdF (by simp)
  have hi : ContDiffAt ℝ ∞ i (F (c x)) := hF.to_localInverse hdF (by simp)
  have hix : i (F (c x)) = c x := hF.localInverse_apply_image hdF (by simp)
  have hFx : F (c x) = d (f x) := by simp [F, c, d, writtenInExtChartAt]
  have hil : ∀ᶠ z in 𝓝 (c x), i (F z) = z :=
    (hF.hasStrictFDerivAt' hdF (by simp)).eventually_left_inverse
  have hc : ContinuousAt c x := continuousAt_extChartAt x
  have heq : g =ᶠ[𝓝 (f x)] fun y => c.symm (i (d y)) := by
    rw [← collar_map_nhds_eq hf hbij]
    change ∀ᶠ z in 𝓝 x, g (f z) = c.symm (i (d (f z)))
    filter_upwards [hleft, hc.tendsto.eventually hil,
      (isOpen_extChartAt_source (I := I) x).mem_nhds
        (mem_extChartAt_source x)] with z hz hzi hzc
    have hFz : F (c z) = d (f z) := by
      simp only [F, writtenInExtChartAt, Function.comp_apply]
      rw [c.left_inv hzc]
    rw [hz, ← hFz, hzi, c.left_inv hzc]
  have hd : ContMDiffAt I 𝓘(ℝ, E) ∞ d (f x) := contMDiffAt_extChartAt
  have hi' : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ i (d (f x)) := by
    rw [← hFx]
    exact hi.contMDiffAt
  have hcs : ContMDiffAt 𝓘(ℝ, E) I ∞ c.symm (i (d (f x))) := by
    rw [← hFx, hix]
    exact (contMDiffOn_extChartAt_symm x).contMDiffAt
      ((isOpen_extChartAt_target (I := I) x).mem_nhds (mem_extChartAt_target x))
  exact (hcs.comp (f x) (hi'.comp (f x) hd)).congr_of_eventuallyEq heq

end InverseInCharts

noncomputable def sphereIsotopyTrackDiffeomorph
    {F : ℝ → UnitTwoSphere → UnitTwoSphere}
    (hF : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 2) ∞
      (fun p : ℝ × UnitTwoSphere => F p.1 p.2))
    (hFt : ∀ t : ℝ, ∃ g : Diffeomorph (𝓡 2) (𝓡 2)
      UnitTwoSphere UnitTwoSphere ∞, ∀ q, g q = F t q) :
    Diffeomorph (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓘(ℝ, ℝ).prod (𝓡 2))
      (ℝ × UnitTwoSphere) (ℝ × UnitTwoSphere) ∞ := by
  let T : ℝ × UnitTwoSphere → ℝ × UnitTwoSphere := fun p => (p.1, F p.1 p.2)
  have hT : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2))
      (𝓘(ℝ, ℝ).prod (𝓡 2)) ∞ T := contMDiff_fst.prodMk hF
  have hbij : Bijective T := by
    constructor
    · rintro ⟨t, q⟩ ⟨u, r⟩ h
      have htu : t = u := congrArg Prod.fst h
      subst u
      obtain ⟨g, hg⟩ := hFt t
      have hqr : q = r := by
        apply g.injective
        change g q = g r
        rw [hg q, hg r]
        exact congrArg Prod.snd h
      exact Prod.ext rfl hqr
    · rintro ⟨t, q⟩
      obtain ⟨g, hg⟩ := hFt t
      exact ⟨(t, g.symm q), Prod.ext rfl ((hg _).symm.trans (g.apply_symm_apply q))⟩
  have hderiv : ∀ p, Bijective (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2))
      (𝓘(ℝ, ℝ).prod (𝓡 2)) T p) := by
    intro p
    let D : (ℝ × EuclideanSpace ℝ (Fin 2)) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
      mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 2) (fun p => F p.1 p.2) p
    let B : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
      mfderiv (𝓡 2) (𝓡 2) (F p.1) p.2
    have hB : Bijective B := by
      obtain ⟨g, hg⟩ := hFt p.1
      have hfg : F p.1 = g := funext fun q => (hg q).symm
      dsimp [B]
      rw [hfg]
      exact (g.mfderivToContinuousLinearEquiv (by simp) p.2).bijective
    have hD (a : ℝ) (v : EuclideanSpace ℝ (Fin 2)) :
        D (a, v) = D (a, 0) + B v := by
      have hDv : D (0, v) = B v := by
        have heq := mfderiv_comp p.2 ((hF.mdifferentiable (by simp)) p)
          (mdifferentiableAt_const.prodMk mdifferentiableAt_id :
            MDifferentiableAt (𝓡 2) (𝓘(ℝ, ℝ).prod (𝓡 2))
              (fun q : UnitTwoSphere => (p.1, q)) p.2)
        rw [mfderiv_prod_right] at heq
        exact (congrArg (fun L => L v) heq).symm
      rw [← hDv, ← map_add]
      congr 1
      simp
    have hTD : mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2))
        (𝓘(ℝ, ℝ).prod (𝓡 2)) T p =
        (ContinuousLinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin 2))).prod D := by
      rw [show T = (fun p : ℝ × UnitTwoSphere => (p.1, F p.1 p.2)) from rfl,
        mfderiv_prodMk mdifferentiableAt_fst ((hF.mdifferentiable (by simp)) p),
        mfderiv_fst]
      rfl
    rw [hTD]
    constructor
    · rintro ⟨a, v⟩ ⟨b, w⟩ h
      have hab : a = b := congrArg Prod.fst h
      subst b
      have hvw : B v = B w := by
        have hDw : D (a, v) = D (a, w) := congrArg Prod.snd h
        rw [hD a v, hD a w] at hDw
        exact add_left_cancel hDw
      exact Prod.ext rfl (hB.1 hvw)
    · rintro ⟨a, w⟩
      obtain ⟨v, hv⟩ := hB.2 (w - D (a, 0))
      refine ⟨(a, v), Prod.ext rfl ?_⟩
      change D (a, v) = w
      rw [hD, hv]
      abel
  let e : (ℝ × UnitTwoSphere) ≃ (ℝ × UnitTwoSphere) := Equiv.ofBijective T hbij
  have hTi : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2))
      (𝓘(ℝ, ℝ).prod (𝓡 2)) ∞ e.symm := by
    intro p
    have hinv := collar_contMDiffAt_left_inverse (hT (e.symm p)) (hderiv (e.symm p))
      (Filter.Eventually.of_forall e.symm_apply_apply)
    change ContMDiffAt _ _ ∞ e.symm (e (e.symm p)) at hinv
    simpa only [e.apply_symm_apply] using hinv
  exact { toEquiv := e, contMDiff_toFun := hT, contMDiff_invFun := hTi }

@[simp] theorem sphereIsotopyTrackDiffeomorph_apply
    {F : ℝ → UnitTwoSphere → UnitTwoSphere}
    (hF : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 2) ∞
      (fun p : ℝ × UnitTwoSphere => F p.1 p.2))
    (hFt : ∀ t : ℝ, ∃ g : Diffeomorph (𝓡 2) (𝓡 2)
      UnitTwoSphere UnitTwoSphere ∞, ∀ q, g q = F t q) (p : ℝ × UnitTwoSphere) :
    sphereIsotopyTrackDiffeomorph hF hFt p = (p.1, F p.1 p.2) := rfl

@[simp] theorem sphereIsotopyTrackDiffeomorph_symm_fst
    {F : ℝ → UnitTwoSphere → UnitTwoSphere}
    (hF : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 2) ∞
      (fun p : ℝ × UnitTwoSphere => F p.1 p.2))
    (hFt : ∀ t : ℝ, ∃ g : Diffeomorph (𝓡 2) (𝓡 2)
      UnitTwoSphere UnitTwoSphere ∞, ∀ q, g q = F t q) (p : ℝ × UnitTwoSphere) :
    ((sphereIsotopyTrackDiffeomorph hF hFt).symm p).1 = p.1 := by
  have h := congrArg Prod.fst ((sphereIsotopyTrackDiffeomorph hF hFt).apply_symm_apply p)
  simpa only [sphereIsotopyTrackDiffeomorph_apply] using h

end PoincareConjecture.M25.Topology3D
