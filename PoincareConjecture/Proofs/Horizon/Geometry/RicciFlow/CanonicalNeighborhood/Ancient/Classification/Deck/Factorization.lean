import PoincareConjecture.Definitions.M27ProductModels
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.SpaceForm.RoundSphere
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.MFDeriv.Zero
import Mathlib.Analysis.Normed.Module.Connected









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Poincare.Geometry.Riemannian.SpaceForm
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M27RoundSphereFamily

variable (F : M27RoundSphereFamily) {c : ℝ}
  (hscale : ∀ t ≤ 0, ∀ x (v w : TangentSpace (𝓡 2) x),
    (F.metric t).inner x v w = (c - 2 * t) * (roundSphereMetric 2).inner x v w)
  {f : UnitTwoSphere × ℝ → UnitTwoSphere × ℝ}
  (hmetric : ∀ t ≤ 0, ∀ p (v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) p),
    F.productInner t (f p)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) f p v)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) f p w) =
        F.productInner t p v w)

include F hscale hmetric



theorem preserves_tangent_forms_of_calibrated_product
    (p : UnitTwoSphere × ℝ) (v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) p) :
    let v' := mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) f p v
    let w' := mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) f p w
    (roundSphereMetric 2).inner (f p).1 v'.1 w'.1 =
        (roundSphereMetric 2).inner p.1 v.1 w.1 ∧
      v'.2 * w'.2 = v.2 * w.2 := by
  have h0 := hmetric 0 le_rfl p v w
  have h1 := hmetric (-1) (by norm_num) p v w
  simp only [productInner, hscale 0 le_rfl, hscale (-1) (by norm_num)] at h0 h1
  dsimp only
  have hs : (roundSphereMetric 2).inner (f p).1
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) f p v).1
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) f p w).1 =
        (roundSphereMetric 2).inner p.1 v.1 w.1 := by nlinarith
  refine ⟨hs, ?_⟩
  rw [hs] at h0
  linarith

theorem preserves_tangent_kernels_of_calibrated_product
    (p : UnitTwoSphere × ℝ) (v : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) p) :
    (v.1 = 0 →
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) f p v).1 = 0) ∧
    (v.2 = 0 →
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) f p v).2 = 0) := by
  obtain ⟨hs, hl⟩ := F.preserves_tangent_forms_of_calibrated_product hscale hmetric p v v
  constructor
  · intro hv
    rw [hv] at hs
    simp only [map_zero] at hs
    by_contra hn
    exact ((roundSphereMetric 2).pos _ _ hn).ne' hs
  · intro hv
    rw [hv, zero_mul] at hl
    exact mul_self_eq_zero.mp hl

theorem cross_mfderiv_eq_zero_of_calibrated_product
    (hf : ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ f) :
    (∀ s : UnitTwoSphere, ∀ z : ℝ,
      mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (fun a => (f (s, a)).1) z = 0) ∧
    (∀ z : ℝ, ∀ s : UnitTwoSphere,
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun a => (f (a, z)).2) s = 0) := by
  constructor
  · intro s z
    have hi : ContMDiff 𝓘(ℝ, ℝ) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞
        (fun a : ℝ => (s, a)) := contMDiff_const.prodMk contMDiff_id
    change mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (Prod.fst ∘ (f ∘ fun a : ℝ => (s, a))) z = 0
    rw [mfderiv_comp z mdifferentiableAt_fst ((hf.comp hi).mdifferentiable (by simp) z),
      mfderiv_comp z (hf.mdifferentiable (by simp) _) (hi.mdifferentiable (by simp) z),
      mfderiv_fst, mfderiv_prod_right]
    apply ContinuousLinearMap.ext
    intro a
    exact (F.preserves_tangent_kernels_of_calibrated_product hscale hmetric (s, z) (0, a)).1 rfl
  · intro z s
    have hi : ContMDiff (𝓡 2) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞
        (fun a : UnitTwoSphere => (a, z)) := contMDiff_id.prodMk contMDiff_const
    change mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (Prod.snd ∘ (f ∘ fun a : UnitTwoSphere => (a, z))) s = 0
    rw [mfderiv_comp s mdifferentiableAt_snd ((hf.comp hi).mdifferentiable (by simp) s),
      mfderiv_comp s (hf.mdifferentiable (by simp) _) (hi.mdifferentiable (by simp) s),
      mfderiv_snd, mfderiv_prod_left]
    apply ContinuousLinearMap.ext
    intro a
    exact (F.preserves_tangent_kernels_of_calibrated_product hscale hmetric (s, z) (a, 0)).2 rfl



theorem exists_smooth_factors_of_calibrated_product
    (hf : ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ f) :
    ∃ a : UnitTwoSphere → UnitTwoSphere, ∃ b : ℝ → ℝ,
      ContMDiff (𝓡 2) (𝓡 2) ∞ a ∧ ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ b ∧
      ∀ s z, f (s, z) = (a s, b z) := by
  classical
  let : ConnectedSpace UnitTwoSphere := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp)) _ zero_le_one)
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
  let s0 : UnitTwoSphere := Classical.arbitrary _
  have he : ContMDiff (𝓡 2) (𝓡 3) ∞
      (fun s : UnitTwoSphere => (s : EuclideanSpace ℝ (Fin 3))) := contMDiff_coe_sphere
  have hfirst (s : UnitTwoSphere) (z : ℝ) : (f (s, z)).1 = (f (s, 0)).1 := by
    apply Subtype.ext
    have hh : ContMDiff 𝓘(ℝ, ℝ) (𝓡 2) ∞ (fun a : ℝ => (f (s, a)).1) :=
      (hf.comp (contMDiff_const.prodMk contMDiff_id)).fst
    apply eq_of_mfderiv_eq_zero ((he.comp hh).mdifferentiable (by simp)) _ z 0
    intro a
    change mfderiv 𝓘(ℝ, ℝ) (𝓡 3)
      ((fun b : UnitTwoSphere => (b : EuclideanSpace ℝ (Fin 3))) ∘
        (fun b : ℝ => (f (s, b)).1)) a = 0
    rw [mfderiv_comp a (he.mdifferentiable (by simp) _) (hh.mdifferentiable (by simp) a),
      (F.cross_mfderiv_eq_zero_of_calibrated_product hscale hmetric hf).1]
    exact ContinuousLinearMap.comp_zero _
  have hsecond (s : UnitTwoSphere) (z : ℝ) : (f (s, z)).2 = (f (s0, z)).2 := by
    apply eq_of_mfderiv_eq_zero
      (((hf.comp (contMDiff_id.prodMk contMDiff_const)).snd).mdifferentiable (by simp))
      ((F.cross_mfderiv_eq_zero_of_calibrated_product hscale hmetric hf).2 z) s s0
  exact ⟨fun s => (f (s, 0)).1, fun z => (f (s0, z)).2,
    (hf.comp (contMDiff_id.prodMk contMDiff_const)).fst,
    (hf.comp (contMDiff_const.prodMk contMDiff_id)).snd,
    fun s z => Prod.ext (hfirst s z) (hsecond s z)⟩

theorem factor_surface_metric_of_calibrated_product
    (a : UnitTwoSphere → UnitTwoSphere) (b : ℝ → ℝ)
    (ha : ContMDiff (𝓡 2) (𝓡 2) ∞ a) (hb : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ b)
    (hfactor : ∀ s z, f (s, z) = (a s, b z))
    (s : UnitTwoSphere) (v w : TangentSpace (𝓡 2) s) :
    (roundSphereMetric 2).inner (a s) (mfderiv (𝓡 2) (𝓡 2) a s v)
      (mfderiv (𝓡 2) (𝓡 2) a s w) = (roundSphereMetric 2).inner s v w := by
  have hfun : f = Prod.map a b := funext fun ⟨s, z⟩ => hfactor s z
  have h := (F.preserves_tangent_forms_of_calibrated_product hscale hmetric
    (s, 0) (v, 0) (w, 0)).1
  rw [hfun, mfderiv_prodMap (ha.mdifferentiable (by simp) s)
    (hb.mdifferentiable (by simp) 0)] at h
  exact h

theorem factor_line_deriv_sq_of_calibrated_product
    (a : UnitTwoSphere → UnitTwoSphere) (b : ℝ → ℝ)
    (ha : ContMDiff (𝓡 2) (𝓡 2) ∞ a) (hb : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ b)
    (hfactor : ∀ s z, f (s, z) = (a s, b z)) (z : ℝ) : deriv b z ^ 2 = 1 := by
  let s : UnitTwoSphere := ⟨EuclideanSpace.single 0 1, by simp⟩
  have hfun : f = Prod.map a b := funext fun ⟨s, z⟩ => hfactor s z
  have h := (F.preserves_tangent_forms_of_calibrated_product hscale hmetric
    (s, z) (0, 1) (0, 1)).2
  rw [hfun, mfderiv_prodMap (ha.mdifferentiable (by simp) s)
    (hb.mdifferentiable (by simp) z)] at h
  let db : ℝ →L[ℝ] ℝ := mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) b z
  have hdb : db 1 = deriv b z := by
    dsimp only [db]
    rw [mfderiv_eq_fderiv]
    rfl
  change db 1 * db 1 = 1 * 1 at h
  rw [hdb] at h
  nlinarith

end PoincareConjecture.M27RoundSphereFamily
