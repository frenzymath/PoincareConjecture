import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.AmbientLabelVelocity
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.UniquenessAmbientAcceleration
import PoincareConjecture.Proofs.M63.Mathlib.RetractionTangentContinuity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u v

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {ι : Type v} [Fintype ι] {a b : ℝ}

local notation "W" => EuclideanSpace ℝ ι

theorem ambientCurve_embeddedCurvature_eq (F : RicciFlow n M (Icc a b))
    {e : M → W} (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e)
    {U : Set W} (hU : IsOpen U) (_heU : range e ⊆ U) {ρ : W → M}
    (hρ : ContMDiffOn 𝓘(ℝ, W) (𝓡 n) ∞ ρ U) (_hρe : ∀ p, ρ (e p) = p)
    (t : ℝ) {f : ℝ → W} (hf : ContDiff ℝ 2 f)
    (hguard : ∀ x, f x ∈ U ∧ mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (f x) (deriv f x) ≠ 0)
    (hfixed : ∀ x, f x = e (ρ (f x))) :
    let c := fun x (_ : ℝ) => ρ (f x)
    let A := fun x => ambientCurvePrincipal F ρ t (f x) (deriv f x)
    let B := fun x => ambientCurveLower F e ρ t (f x) (deriv f x)
    ∀ x, mfderiv (𝓡 n) 𝓘(ℝ, W) e (c x t) (m62CurvatureVector F c t x) =
      A x • deriv (deriv f) x + B x + (deriv A x / 2) • deriv f x := by
  let c := fun x (_ : ℝ) => ρ (f x)
  let A := fun x => ambientCurvePrincipal F ρ t (f x) (deriv f x)
  let B := fun x => ambientCurveLower F e ρ t (f x) (deriv f x)
  change ∀ x, mfderiv (𝓡 n) 𝓘(ℝ, W) e (c x t) (m62CurvatureVector F c t x) =
    A x • deriv (deriv f) x + B x + (deriv A x / 2) • deriv f x
  have hspace : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 2 (fun y => c y t) :=
    (hρ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).comp_contMDiff
      hf.contMDiff (fun x => (hguard x).1)
  have hvel (x : ℝ) : curveVelocity (n := n) (fun y => c y t) x =
      mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (f x) (deriv f x) := by
    change (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (ρ ∘ f) x) 1 = _
    erw [mfderiv_comp x
      ((hρ.contMDiffAt (hU.mem_nhds (hguard x).1)).mdifferentiableAt (by simp))
      ((hf.contMDiff x).mdifferentiableAt (by norm_num)),
      ContinuousLinearMap.comp_apply, mfderiv_eq_fderiv]
    rfl
  have himm (x : ℝ) : curveVelocity (n := n) (fun y => c y t) x ≠ 0 := by
    rw [hvel]
    exact (hguard x).2
  have heq : (fun y => e (c y t)) = f := funext fun y => (hfixed y).symm
  have hA (x : ℝ) : A x = (curveSpeed F c t x ^ 2)⁻¹ := by
    dsimp only [A, ambientCurvePrincipal]
    rw [← hvel x]
    exact congrArg (fun z : ℝ => z⁻¹) (M62.speed_sq F c t x).symm
  have hB (x : ℝ) : B x = -(A x • coordinateHessian (F.connection t) e (c x t)
      (curveVelocity (fun y => c y t) x) (curveVelocity (fun y => c y t) x)) := by
    dsimp only [B, ambientCurveLower, A]
    rw [hvel x]
  intro x
  have hcurv := embedded_curvature_eq_acceleration_sub_tangent F he c (t := t) hspace himm x
  rw [heq, ← hA x] at hcurv
  have hlabel := ambientCurve_labelVelocity_eq F hU hρ t hf hguard x
  change deriv A x / 2 = -(deriv (curveSpeed F c t) x / curveSpeed F c t x ^ 3)
    at hlabel
  change mfderiv (𝓡 n) 𝓘(ℝ, W) e (c x t) (m62CurvatureVector F c t x) =
    A x • deriv (deriv f) x + B x + (deriv A x / 2) • deriv f x
  rw [hcurv, hB, hlabel, smul_sub, neg_smul]
  abel

theorem ambientCurve_closed_fields (F : RicciFlow n M (Icc a b))
    {e : M → W} (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e)
    {U : Set W} (hU : IsOpen U) (heU : range e ⊆ U) {ρ : W → M}
    (hρ : ContMDiffOn 𝓘(ℝ, W) (𝓡 n) ∞ ρ U) (hρe : ∀ p, ρ (e p) = p)
    {T : ℝ} (haT : a < T) (hTb : T ≤ b) {q : ℝ → ℝ → W}
    (hq : ContDiffOn ℝ ∞ (Function.uncurry q) (Icc a T ×ˢ univ))
    (hguard : ∀ t ∈ Icc a T, ∀ x, q t x ∈ U ∧
      mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (q t x) (deriv (q t) x) ≠ 0)
    (hfixed : ∀ t ∈ Icc a T, ∀ x, q t x = e (ρ (q t x))) :
    let c := fun x t => ρ (q t x)
    ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n) ∞
        (fun z : ℝ × ℝ => c z.1 z.2) (univ ×ˢ Icc a T) ∧
      (∀ t ∈ Icc a T, ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) ∞ (fun x => c x t)) ∧
      (∀ t ∈ Icc a T, ∀ x, curveVelocity (n := n) (fun y => c y t) x ≠ 0) ∧
      ContinuousOn (fun z : ℝ × ℝ =>
        (⟨c z.1 z.2, curveVelocity (n := n) (fun y => c y z.2) z.1⟩ :
          TangentBundle (𝓡 n) M)) (univ ×ˢ Icc a T) ∧
      ContinuousOn (fun z : ℝ × ℝ =>
        (⟨c z.1 z.2, m62CurvatureVector F c z.2 z.1⟩ :
          TangentBundle (𝓡 n) M)) (univ ×ˢ Icc a T) := by
  let S : Set (ℝ × ℝ) := Icc a T ×ˢ univ
  let c := fun x t => ρ (q t x)
  let A := fun t x => ambientCurvePrincipal F ρ t (q t x) (deriv (q t) x)
  let B := fun t x => ambientCurveLower F e ρ t (q t x) (deriv (q t) x)
  have hqx := contDiffOn_spatial_deriv_of_uniqueDiffOn (uniqueDiffOn_Icc haT)
    (m := ∞) (by simp) hq
  have hqxx := contDiffOn_spatial_deriv_of_uniqueDiffOn (uniqueDiffOn_Icc haT)
    (q := fun t => deriv (q t)) (m := ∞) (n := ∞) (by simp) hqx
  have hspace (t : ℝ) (ht : t ∈ Icc a T) : ContDiff ℝ ∞ (q t) :=
    contDiffOn_univ.mp (hq.comp (contDiffOn_const.prodMk contDiffOn_id)
      (fun _ _ => ⟨ht, mem_univ _⟩))
  have hcspace (t : ℝ) (ht : t ∈ Icc a T) :
      ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) ∞ (fun x => c x t) :=
    hρ.comp_contMDiff (hspace t ht).contMDiff (fun x => (hguard t ht x).1)
  have hc : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n) ∞
      (fun z : ℝ × ℝ => c z.2 z.1) S :=
    hρ.comp hq.contMDiffOn (fun z hz => (hguard z.1 hz.1 z.2).1)
  have hswap : ContDiff ℝ ∞ (Prod.swap : ℝ × ℝ → ℝ × ℝ) :=
    contDiff_snd.prodMk contDiff_fst
  have hswapmem : MapsTo (Prod.swap : ℝ × ℝ → ℝ × ℝ) (univ ×ˢ Icc a T) S :=
    fun _ hz => ⟨hz.2, hz.1⟩
  have hcjoint : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n) ∞
      (fun z : ℝ × ℝ => c z.1 z.2) (univ ×ˢ Icc a T) :=
    hc.comp hswap.contMDiff.contMDiffOn hswapmem
  have hvel (t : ℝ) (ht : t ∈ Icc a T) (x : ℝ) :
      curveVelocity (n := n) (fun y => c y t) x =
        mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (q t x) (deriv (q t) x) := by
    change (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (ρ ∘ q t) x) 1 = _
    erw [mfderiv_comp x
      ((hρ.contMDiffAt (hU.mem_nhds (hguard t ht x).1)).mdifferentiableAt (by simp))
      (((hspace t ht).contMDiff x).mdifferentiableAt (by simp)),
      ContinuousLinearMap.comp_apply, mfderiv_eq_fderiv]
    rfl
  have himm (t : ℝ) (ht : t ∈ Icc a T) (x : ℝ) :
      curveVelocity (n := n) (fun y => c y t) x ≠ 0 := by
    rw [hvel t ht x]
    exact (hguard t ht x).2
  have hparam : ContDiffOn ℝ ∞ (fun z : ℝ × ℝ =>
      ((z.1, q z.1 z.2), deriv (q z.1) z.2)) S :=
    (contDiffOn_fst.prodMk hq).prodMk hqx
  have hmap : MapsTo (fun z : ℝ × ℝ =>
      ((z.1, q z.1 z.2), deriv (q z.1) z.2)) S
      {z : (ℝ × W) × W | z.1.1 ∈ Icc a b ∧ z.1.2 ∈ U ∧
        mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z.1.2 z.2 ≠ 0} := by
    intro z hz
    exact ⟨⟨hz.1.1, hz.1.2.trans hTb⟩, hguard z.1 hz.1 z.2⟩
  obtain ⟨hA0, hB0, _⟩ := ambientCurveCoefficients_contDiffOn F he hU hρ
  have hA : ContDiffOn ℝ ∞ (Function.uncurry A) S := by
    simpa only [Function.comp_def, Function.uncurry_def, A] using hA0.comp hparam hmap
  have hB : ContDiffOn ℝ ∞ (Function.uncurry B) S := by
    simpa only [Function.comp_def, Function.uncurry_def, B] using hB0.comp hparam hmap
  have hAx := contDiffOn_spatial_deriv_of_uniqueDiffOn (uniqueDiffOn_Icc haT)
    (q := A) (m := ∞) (n := ∞) (by simp) hA
  have hpushH : ContinuousOn (fun z : ℝ × ℝ =>
      mfderiv (𝓡 n) 𝓘(ℝ, W) e (c z.2 z.1) (m62CurvatureVector F c z.1 z.2)) S := by
    apply (((hA.continuousOn.smul hqxx.continuousOn).add hB.continuousOn).add
      ((hAx.div_const 2).continuousOn.smul hqx.continuousOn)).congr
    intro z hz
    exact ambientCurve_embeddedCurvature_eq F he hU heU hρ hρe z.1
      ((hspace z.1 hz.1).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
      (hguard z.1 hz.1) (hfixed z.1 hz.1) z.2
  have hpushX : ContinuousOn (fun z : ℝ × ℝ =>
      mfderiv (𝓡 n) 𝓘(ℝ, W) e (c z.2 z.1)
        (curveVelocity (n := n) (fun y => c y z.1) z.2)) S := by
    apply hqx.continuousOn.congr
    intro z hz
    have heq : (fun y => e (c y z.1)) = q z.1 :=
      funext fun y => (hfixed z.1 hz.1 y).symm
    have hd : fderiv ℝ (fun y => e (c y z.1)) z.2 =
        (mfderiv (𝓡 n) 𝓘(ℝ, W) e (c z.2 z.1)).comp
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun y => c y z.1) z.2) := by
      rw [← mfderiv_eq_fderiv]
      exact mfderiv_comp z.2 (he.mdifferentiable (by simp)).mdifferentiableAt
        (((hcspace z.1 hz.1) z.2).mdifferentiableAt (by simp))
    rw [heq] at hd
    exact (congrArg (fun D : ℝ →L[ℝ] W => D 1) hd).symm
  refine ⟨hcjoint, hcspace, himm, ?_, ?_⟩
  · exact continuousOn_tangentSection_of_retraction_pushforward he hU heU hρ hρe
      (fun z : ℝ × ℝ => c z.1 z.2)
      (fun z => curveVelocity (n := n) (fun y => c y z.2) z.1)
      hcjoint.continuousOn (hpushX.comp hswap.continuous.continuousOn hswapmem)
  · exact continuousOn_tangentSection_of_retraction_pushforward he hU heU hρ hρe
      (fun z : ℝ × ℝ => c z.1 z.2) (fun z => m62CurvatureVector F c z.2 z.1)
      hcjoint.continuousOn (hpushH.comp hswap.continuous.continuousOn hswapmem)

end PoincareConjecture.M63
