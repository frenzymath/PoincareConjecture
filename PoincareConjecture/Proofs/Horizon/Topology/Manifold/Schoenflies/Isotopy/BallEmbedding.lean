import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.CodimensionZero
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.Linearization
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.CompactExtension

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]

theorem exists_supported_embedded_ball_shrinking
    {r c : Real} (hc : 0 < c) (hc1 : c ≤ 1)
    (f : E -> E) (hf : ContDiff Real ∞ f)
    (hinj : InjOn f (closedBall 0 r))
    (hder : ∀ x ∈ closedBall (0 : E) r,
      Function.Bijective (fderiv Real f x)) :
    ∃ F : Diffeomorph 𝓘(Real, E) 𝓘(Real, E) E E ∞,
      (∃ K : Set E, IsCompact K ∧ ∀ x ∉ K, F x = x) ∧
      ∀ x ∈ closedBall (0 : E) r, F (f x) = f (c • x) := by
  let d : Real -> Real := fun t => 1 - t + t * c
  let G : Real × E -> E := fun p => f (d p.1 • p.2)
  have hd (t : Real) (ht : t ∈ Icc (0 : Real) 1) : 0 < d t ∧ d t ≤ 1 := by
    dsimp [d]
    constructor <;> nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr hc1),
      mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hc1)]
  have hball (t : Real) (ht : t ∈ Icc (0 : Real) 1)
      (x : E) (hx : x ∈ closedBall (0 : E) r) : d t • x ∈ closedBall (0 : E) r := by
    rw [mem_closedBall, dist_zero_right] at hx ⊢
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (hd t ht).1]
    exact (mul_le_mul_of_nonneg_right (hd t ht).2 (norm_nonneg x)).trans (by simpa using hx)
  have hG : ContDiff Real ∞ G := hf.comp
    (((contDiff_const.sub contDiff_fst).add (contDiff_fst.mul contDiff_const)).smul
      contDiff_snd)
  have hGi (t : Real) (ht : t ∈ Icc (0 : Real) 1) :
      InjOn (fun x => G (t, x)) (closedBall 0 r) := by
    intro x hx y hy hxy
    exact (LinearEquiv.smulOfNeZero Real E (d t) (hd t ht).1.ne').injective
      (hinj (hball t ht x hx) (hball t ht y hy) hxy)
  have hGd (t : Real) (ht : t ∈ Icc (0 : Real) 1)
      (x : E) (hx : x ∈ closedBall (0 : E) r) :
      Function.Bijective (fderiv Real (fun y => G (t, y)) x) := by
    have heq : fderiv Real (fun y => G (t, y)) x =
        (fderiv Real f (d t • x)).comp (d t • ContinuousLinearMap.id Real E) :=
      ((hf.differentiable (by simp) _).hasFDerivAt.comp x
        ((hasFDerivAt_id x).const_smul (d t))).fderiv
    rw [heq]
    exact (hder _ (hball t ht x hx)).comp
      (LinearEquiv.smulOfNeZero Real E (d t) (hd t ht).1.ne').bijective
  obtain ⟨Phi, _, _, ⟨K, hK, hfix⟩, hmotion⟩ :=
    exists_ambient_isotopy_of_codimZero_isotopy (isCompact_closedBall 0 r) G hG hGi hGd
  refine ⟨Phi 1, ⟨K, hK, hfix 1⟩, ?_⟩
  intro x hx
  simpa [G, d] using hmotion 1 (show (1 : Real) ∈ Icc 0 1 by simp) x hx

theorem exists_global_extension_of_ball_embedding
    {r : Real} (hr : 0 < r)
    (f : E -> E) (hf : ContDiff Real ∞ f)
    (hinj : InjOn f (closedBall 0 r))
    (hder : ∀ x ∈ closedBall (0 : E) r,
      Function.Bijective (fderiv Real f x)) :
    ∃ F : Diffeomorph 𝓘(Real, E) 𝓘(Real, E) E E ∞,
      ∀ x ∈ closedBall (0 : E) r, F x = f x := by
  have h0 : (0 : E) ∈ closedBall (0 : E) r := mem_closedBall_self hr.le
  obtain ⟨delta, hdelta, Psi, _, _, _, hPsi⟩ :=
    exists_supported_linearization_isotopy f hf (hder 0 h0)
  let c : Real := min 1 (delta / r)
  have hc : 0 < c := lt_min zero_lt_one (div_pos hdelta hr)
  have hc1 : c ≤ 1 := min_le_left _ _
  have hcr : c * r ≤ delta := (le_div_iff₀ hr).mp (min_le_right _ _)
  obtain ⟨P, _, hP⟩ := exists_supported_embedded_ball_shrinking hc hc1 f hf hinj hder
  let A : E ≃L[Real] E := ContinuousLinearEquiv.ofBijective (fderiv Real f 0)
    (LinearMap.ker_eq_bot.mpr (hder 0 h0).1) (LinearMap.range_eq_top.mpr (hder 0 h0).2)
  let B : E ≃L[Real] E := (LinearEquiv.smulOfNeZero Real E c hc.ne').toContinuousLinearEquiv
  let T : Diffeomorph 𝓘(Real, E) 𝓘(Real, E) E E ∞ := {
    toEquiv := Equiv.addRight (-f 0)
    contMDiff_toFun := (contDiff_id.add contDiff_const).contMDiff
    contMDiff_invFun := (contDiff_id.add contDiff_const).contMDiff }
  let Q := (((P.trans T).trans (Psi 1)).trans A.symm.toDiffeomorph).trans B.symm.toDiffeomorph
  have hQ (x : E) (hx : x ∈ closedBall (0 : E) r) : Q (f x) = x := by
    have hcx : c • x ∈ closedBall (0 : E) delta := by
      rw [mem_closedBall, dist_zero_right] at hx ⊢
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc]
      exact (mul_le_mul_of_nonneg_left hx hc.le).trans hcr
    change B.symm (A.symm (Psi 1 (P (f x) + -f 0))) = x
    rw [hP x hx, ← sub_eq_add_neg, hPsi 1 (by simp) _ hcx]
    simp only [sub_self, zero_smul, one_smul, zero_add]
    change B.symm (A.symm (A (c • x))) = x
    rw [A.symm_apply_apply]
    exact B.symm_apply_apply x
  refine ⟨Q.symm, ?_⟩
  intro x hx
  apply Q.injective
  change Q (Q.symm x) = Q (f x)
  rw [Q.apply_symm_apply, hQ x hx]

theorem exists_global_extension_of_local_ball_embedding
    {r : Real} (hr : 0 < r) (f : E -> E)
    (hinj : InjOn f (closedBall 0 r))
    (hloc : ∀ x ∈ closedBall (0 : E) r,
      IsLocalDiffeomorphAt 𝓘(Real, E) 𝓘(Real, E) ∞ f x) :
    ∃ F : Diffeomorph 𝓘(Real, E) 𝓘(Real, E) E E ∞,
      ∀ x ∈ closedBall (0 : E) r, F x = f x := by
  let U := {x | IsLocalDiffeomorphAt 𝓘(Real, E) 𝓘(Real, E) ∞ f x}
  obtain ⟨g, V, hg, hV, hball, _, hgf⟩ :=
    Poincare.Analysis.exists_contDiff_extension_near_compact (isCompact_closedBall 0 r)
      (Poincare.isOpen_isLocalDiffeomorphAt (f := f)) hloc f
      (fun x (hx : x ∈ U) => hx.contMDiffAt.contDiffAt.contDiffWithinAt)
  have hder (x : E) (hx : x ∈ closedBall 0 r) :
      Function.Bijective (fderiv Real g x) := by
    have heq : g =ᶠ[𝓝 x] f := Filter.eventuallyEq_of_mem (hV.mem_nhds (hball hx)) hgf
    rw [heq.fderiv_eq]
    have h := ((hloc x hx).mfderivToContinuousLinearEquiv (by simp)).bijective
    change Function.Bijective (mfderiv 𝓘(Real, E) 𝓘(Real, E) f x) at h
    simpa only [mfderiv_eq_fderiv, TangentSpace] using h
  obtain ⟨F, hF⟩ := exists_global_extension_of_ball_embedding hr g hg
    (fun x hx y hy hxy => hinj hx hy
      ((hgf (hball hx)).symm.trans (hxy.trans (hgf (hball hy))))) hder
  exact ⟨F, fun x hx => (hF x hx).trans (hgf (hball hx))⟩

end Poincare.Manifold.Schoenflies
