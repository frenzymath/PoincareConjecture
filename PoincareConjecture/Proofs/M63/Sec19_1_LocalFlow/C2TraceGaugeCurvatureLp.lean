import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.AmbientClosedCurveFields
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.AmbientCompactJetBounds
import PoincareConjecture.Proofs.M63.Mathlib.ContinuousL2Product
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.UniformSpace.CompactConvergence










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory AddCircle
open scoped Manifold ContDiff Bundle Topology

universe u v

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {ι : Type v} [Fintype ι] {a b : ℝ}

local notation "W" => EuclideanSpace ℝ ι





theorem ambientCurve_curvature_label_affine (F : RicciFlow n M (Icc a b))
    {e : M → W} (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e)
    {U : Set W} (hU : IsOpen U) (heU : range e ⊆ U) {ρ : W → M}
    (hρ : ContMDiffOn 𝓘(ℝ, W) (𝓡 n) ∞ ρ U) (hρe : ∀ p, ρ (e p) = p)
    {t : ℝ} (ht : t ∈ Icc a b) :
    let Ω : Set (W × W) := {z | z.1 ∈ U ∧ mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z.1 z.2 ≠ 0}
    let α := fun z : W × W => ambientCurvePrincipal F ρ t z.1 z.2
    let β := fun z : W × W => ambientCurveLower F e ρ t z.1 z.2
    let lam : W × W → W →L[ℝ] ℝ := fun z => (1 / 2 : ℝ) •
      (fderiv ℝ α z).comp (ContinuousLinearMap.inr ℝ W W)
    let η := fun z : W × W => fderiv ℝ α z (z.2, 0) / 2
    let C : W × W → W →L[ℝ] W :=
      fun z => α z • ContinuousLinearMap.id ℝ W + (lam z).smulRight z.2
    let d : W × W → W := fun z => β z + η z • z.2
    ContinuousOn lam Ω ∧ ContinuousOn η Ω ∧ ContinuousOn C Ω ∧ ContinuousOn d Ω ∧
      ∀ (f : ℝ → W), ContDiff ℝ 2 f →
        (∀ y, (f y, deriv f y) ∈ Ω) → (∀ y, f y = e (ρ (f y))) →
        ∀ x : ℝ,
          deriv (fun y => α (f y, deriv f y)) x / 2 =
            lam (f x, deriv f x) (deriv (deriv f) x) + η (f x, deriv f x) ∧
          mfderiv (𝓡 n) 𝓘(ℝ, W) e (ρ (f x))
              (m62CurvatureVector F (fun y (_ : ℝ) => ρ (f y)) t x) =
            C (f x, deriv f x) (deriv (deriv f) x) + d (f x, deriv f x) := by
  dsimp only
  let Ω : Set (W × W) := {z | z.1 ∈ U ∧ mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z.1 z.2 ≠ 0}
  let α := fun z : W × W => ambientCurvePrincipal F ρ t z.1 z.2
  let β := fun z : W × W => ambientCurveLower F e ρ t z.1 z.2
  let lam : W × W → W →L[ℝ] ℝ := fun z => (1 / 2 : ℝ) •
    (fderiv ℝ α z).comp (ContinuousLinearMap.inr ℝ W W)
  let η := fun z : W × W => fderiv ℝ α z (z.2, 0) / 2
  let C : W × W → W →L[ℝ] W :=
    fun z => α z • ContinuousLinearMap.id ℝ W + (lam z).smulRight z.2
  let d : W × W → W := fun z => β z + η z • z.2
  have hΩ : IsOpen Ω := isOpen_ambientCurveJetDomain F hU hρ
  obtain ⟨hα0, hβ0, _⟩ := ambientCurveCoefficients_contDiffOn F he hU hρ
  have hparam : ContDiff ℝ ∞ (fun z : W × W => ((t, z.1), z.2)) := by fun_prop
  have hαcomp := hα0.comp (s := Ω) hparam.contDiffOn (fun _ hz => ⟨ht, hz⟩)
  have hα : ContDiffOn ℝ ∞ α Ω := hαcomp
  have hβcomp := hβ0.comp (s := Ω) hparam.contDiffOn (fun _ hz => ⟨ht, hz⟩)
  have hβ : ContDiffOn ℝ ∞ β Ω := hβcomp
  have hD : ContinuousOn (fderiv ℝ α) Ω := hα.continuousOn_fderiv_of_isOpen hΩ (by simp)
  have hhalf : ContinuousOn (fun _ : W × W => (1 / 2 : ℝ)) Ω := continuousOn_const
  have hinr : ContinuousOn (fun _ : W × W => ContinuousLinearMap.inr ℝ W W) Ω :=
    continuousOn_const
  have hLam : ContinuousOn lam Ω := hhalf.smul (hD.clm_comp hinr)
  have hη : ContinuousOn η Ω :=
    (hD.clm_apply (continuousOn_snd.prodMk continuousOn_const)).div_const 2
  have hC : ContinuousOn C Ω :=
    (hα.continuousOn.smul continuousOn_const).add
      (((ContinuousLinearMap.smulRightL ℝ W W).continuous.comp_continuousOn hLam).clm_apply
        continuousOn_snd)
  have hd : ContinuousOn d Ω := hβ.continuousOn.add (hη.smul continuousOn_snd)
  refine ⟨hLam, hη, hC, hd, ?_⟩
  intro f hf hguard hfixed x
  have hf1 : ContDiff ℝ 1 (deriv f) := hf.deriv' (n := 1)
  have hpair := ((hf.differentiable (by norm_num) x).hasDerivAt).prodMk
    (hf1.differentiable (by norm_num) x).hasDerivAt
  have hchain := ((hα.contDiffAt (hΩ.mem_nhds (hguard x))).differentiableAt
    (by simp)).hasFDerivAt.comp_hasDerivAt x hpair
  have hder : deriv (fun y => α (f y, deriv f y)) x =
      fderiv ℝ α (f x, deriv f x) (deriv f x, deriv (deriv f) x) := by
    simpa only [Function.comp_def] using hchain.deriv
  have hsplit : fderiv ℝ α (f x, deriv f x) (deriv f x, deriv (deriv f) x) =
      fderiv ℝ α (f x, deriv f x) (deriv f x, 0) +
        fderiv ℝ α (f x, deriv f x) (0, deriv (deriv f) x) := by
    rw [← map_add]
    simp only [Prod.mk_add_mk, add_zero, zero_add]
  have hlabel : deriv (fun y => α (f y, deriv f y)) x / 2 =
      lam (f x, deriv f x) (deriv (deriv f) x) + η (f x, deriv f x) := by
    rw [hder, hsplit]
    dsimp only [lam, η]
    simp only [smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inr_apply, smul_eq_mul]
    ring
  refine ⟨hlabel, ?_⟩
  have hcurv := ambientCurve_embeddedCurvature_eq F he hU heU hρ hρe t hf hguard hfixed x
  change (mfderiv (𝓡 n) 𝓘(ℝ, W) e (ρ (f x))
      (m62CurvatureVector F (fun y (_ : ℝ) => ρ (f y)) t x) : W) =
    α (f x, deriv f x) • deriv (deriv f) x + β (f x, deriv f x) +
      (deriv (fun y => α (f y, deriv f y)) x / 2) • deriv f x at hcurv
  change (mfderiv (𝓡 n) 𝓘(ℝ, W) e (ρ (f x))
      (m62CurvatureVector F (fun y (_ : ℝ) => ρ (f y)) t x) : W) =
    C (f x, deriv f x) (deriv (deriv f) x) + d (f x, deriv f x)
  rw [hcurv, hlabel]
  dsimp only [C, d]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply, add_smul]
  abel





theorem exists_cauchySeq_ambientCurvature_labelVelocity_L2
    (F : RicciFlow n M (Icc a b))
    {e : M → W} (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e)
    {U : Set W} (hU : IsOpen U) (heU : range e ⊆ U) {ρ : W → M}
    (hρ : ContMDiffOn 𝓘(ℝ, W) (𝓡 n) ∞ ρ U) (hρe : ∀ p, ρ (e p) = p)
    {t L : ℝ} (ht : t ∈ Icc a b) [Fact (0 < L)]
    (q p r : ℕ → C(AddCircle L, W)) (q0 p0 : C(AddCircle L, W))
    (hqder : ∀ j (x : ℝ), HasDerivAt (fun y : ℝ => q j (y : AddCircle L))
      (p j (x : AddCircle L)) x)
    (hpder : ∀ j (x : ℝ), HasDerivAt (fun y : ℝ => p j (y : AddCircle L))
      (r j (x : AddCircle L)) x)
    (hguard : ∀ j z, q j z ∈ U ∧ mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (q j z) (p j z) ≠ 0)
    (hfixed : ∀ j z, q j z = e (ρ (q j z)))
    (hguard0 : ∀ z, q0 z ∈ U ∧ mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (q0 z) (p0 z) ≠ 0)
    (hq : Tendsto q atTop (𝓝 q0)) (hp : Tendsto p atTop (𝓝 p0))
    (hr : CauchySeq (fun j => ContinuousMap.toLp 2 haarAddCircle ℝ (r j))) :
    ∃ (H : ℕ → C(AddCircle L, W)) (w : ℕ → C(AddCircle L, ℝ)),
      (∀ j (x : ℝ), H j (x : AddCircle L) =
        mfderiv (𝓡 n) 𝓘(ℝ, W) e (ρ (q j (x : AddCircle L)))
          (m62CurvatureVector F (fun y (_ : ℝ) => ρ (q j (y : AddCircle L))) t x)) ∧
      (∀ j (x : ℝ), w j (x : AddCircle L) =
        deriv (fun y : ℝ => ambientCurvePrincipal F ρ t
          (q j (y : AddCircle L)) (deriv (fun z : ℝ => q j (z : AddCircle L)) y)) x / 2) ∧
      CauchySeq (fun j => ContinuousMap.toLp 2 haarAddCircle ℝ (H j)) ∧
      CauchySeq (fun j => ContinuousMap.toLp 2 haarAddCircle ℝ (w j)) := by
  classical
  let Ω : Set (W × W) := {z | z.1 ∈ U ∧ mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z.1 z.2 ≠ 0}
  let α := fun z : W × W => ambientCurvePrincipal F ρ t z.1 z.2
  let β := fun z : W × W => ambientCurveLower F e ρ t z.1 z.2
  let lam : W × W → W →L[ℝ] ℝ := fun z => (1 / 2 : ℝ) •
    (fderiv ℝ α z).comp (ContinuousLinearMap.inr ℝ W W)
  let η := fun z : W × W => fderiv ℝ α z (z.2, 0) / 2
  let C : W × W → W →L[ℝ] W :=
    fun z => α z • ContinuousLinearMap.id ℝ W + (lam z).smulRight z.2
  let d : W × W → W := fun z => β z + η z • z.2
  obtain ⟨hLam, hη, hC, hd, hformula⟩ :=
    ambientCurve_curvature_label_affine F he hU heU hρ hρe ht
  let LC : C(Ω, W →L[ℝ] W) := ⟨fun z => C z, continuousOn_iff_continuous_domRestrict.mp hC⟩
  let Ld : C(Ω, W) := ⟨fun z => d z, continuousOn_iff_continuous_domRestrict.mp hd⟩
  let Llam : C(Ω, W →L[ℝ] ℝ) := ⟨fun z => lam z, continuousOn_iff_continuous_domRestrict.mp hLam⟩
  let Lη : C(Ω, ℝ) := ⟨fun z => η z, continuousOn_iff_continuous_domRestrict.mp hη⟩
  let J (j : ℕ) : C(AddCircle L, Ω) :=
    ⟨fun z => ⟨(q j z, p j z), hguard j z⟩,
      ((q j).continuous.prodMk (p j).continuous).subtype_mk _⟩
  let J0 : C(AddCircle L, Ω) :=
    ⟨fun z => ⟨(q0 z, p0 z), hguard0 z⟩,
      (q0.continuous.prodMk p0.continuous).subtype_mk _⟩
  let inc : C(Ω, W × W) := ⟨Subtype.val, continuous_subtype_val⟩
  have hJ : Tendsto J atTop (𝓝 J0) := by
    apply (inc.isEmbedding_postcomp Topology.IsEmbedding.subtypeVal).tendsto_nhds_iff.mpr
    change Tendsto (fun j => (q j).prodMk (p j)) atTop (𝓝 (q0.prodMk p0))
    apply ContinuousMap.tendsto_iff_tendstoUniformly.mpr
    have hprod := (ContinuousMap.tendsto_iff_tendstoUniformly.mp hq).prodMk
      (ContinuousMap.tendsto_iff_tendstoUniformly.mp hp)
    exact fun u hu => (hprod u hu).diag_of_prod
  have hLC := (LC.continuous_postcomp.tendsto J0).comp hJ
  have hLd := (Ld.continuous_postcomp.tendsto J0).comp hJ
  have hLlam := (Llam.continuous_postcomp.tendsto J0).comp hJ
  have hLη := (Lη.continuous_postcomp.tendsto J0).comp hJ
  let H (j : ℕ) : C(AddCircle L, W) :=
    ⟨fun z => LC (J j z) (r j z) + Ld (J j z),
      (((LC.comp (J j)).continuous).clm_apply (r j).continuous).add
        (Ld.comp (J j)).continuous⟩
  let w (j : ℕ) : C(AddCircle L, ℝ) :=
    ⟨fun z => Llam (J j z) (r j z) + Lη (J j z),
      (((Llam.comp (J j)).continuous).clm_apply (r j).continuous).add
        (Lη.comp (J j)).continuous⟩
  have hder0 (j : ℕ) : deriv (fun y : ℝ => q j (y : AddCircle L)) =
      fun y : ℝ => p j (y : AddCircle L) := funext fun x => (hqder j x).deriv
  have hder1 (j : ℕ) : deriv (fun y : ℝ => p j (y : AddCircle L)) =
      fun y : ℝ => r j (y : AddCircle L) := funext fun x => (hpder j x).deriv
  have hc2 (j : ℕ) : ContDiff ℝ 2 (fun y : ℝ => q j (y : AddCircle L)) := by
    rw [show (2 : ℕ∞ω) = 1 + 1 from rfl, contDiff_succ_iff_deriv]
    refine ⟨fun x => (hqder j x).differentiableAt, by simp, ?_⟩
    rw [hder0 j, contDiff_one_iff_deriv]
    refine ⟨fun x => (hpder j x).differentiableAt, ?_⟩
    rw [hder1 j]
    exact (r j).continuous.comp (AddCircle.continuous_mk' L)
  have hgeom (j : ℕ) (x : ℝ) := hformula
    (fun y : ℝ => q j (y : AddCircle L)) (hc2 j)
    (by
      intro y
      change q j (y : AddCircle L) ∈ U ∧
        mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (q j (y : AddCircle L))
          (deriv (fun z : ℝ => q j (z : AddCircle L)) y) ≠ 0
      rw [hder0 j]
      exact hguard j (y : AddCircle L))
    (fun y => hfixed j (y : AddCircle L)) x
  refine ⟨H, w, ?_, ?_, ?_, ?_⟩
  · intro j x
    change C (q j (x : AddCircle L), p j (x : AddCircle L))
      (r j (x : AddCircle L)) + d (q j (x : AddCircle L), p j (x : AddCircle L)) = _
    simpa only [hder0 j, hder1 j] using! (hgeom j x).2.symm
  · intro j x
    change lam (q j (x : AddCircle L), p j (x : AddCircle L))
      (r j (x : AddCircle L)) + η (q j (x : AddCircle L), p j (x : AddCircle L)) = _
    simpa only [hder0 j, hder1 j] using (hgeom j x).1.symm
  all_goals
    obtain ⟨R0, hR0⟩ := cauchySeq_tendsto_of_complete hr
  · obtain ⟨MW, _hMWnorm, hMW⟩ := exists_continuousL2_product
      (haarAddCircle : Measure (AddCircle L))
      (ContinuousLinearMap.id ℝ (W →L[ℝ] W))
    have hprod : Continuous (fun z : C(AddCircle L, W →L[ℝ] W) × Lp W 2 haarAddCircle =>
        MW z.1 z.2) := (MW.continuous.comp continuous_fst).clm_apply continuous_snd
    have hlim := ((hprod.tendsto (LC.comp J0, R0)).comp (hLC.prodMk_nhds hR0)).add
      (((ContinuousMap.toLp 2 haarAddCircle ℝ).continuous.tendsto (Ld.comp J0)).comp hLd)
    have heq (j : ℕ) : MW (LC.comp (J j)) (ContinuousMap.toLp 2 haarAddCircle ℝ (r j)) +
        ContinuousMap.toLp 2 haarAddCircle ℝ (Ld.comp (J j)) =
          ContinuousMap.toLp 2 haarAddCircle ℝ (H j) := by
      apply Lp.ext
      filter_upwards [hMW (LC.comp (J j)) (ContinuousMap.toLp 2 haarAddCircle ℝ (r j)),
        ContinuousMap.coeFn_toLp (p := 2) haarAddCircle (𝕜 := ℝ) (r j),
        ContinuousMap.coeFn_toLp (p := 2) haarAddCircle (𝕜 := ℝ) (Ld.comp (J j)),
        ContinuousMap.coeFn_toLp (p := 2) haarAddCircle (𝕜 := ℝ) (H j),
        Lp.coeFn_add (MW (LC.comp (J j)) (ContinuousMap.toLp 2 haarAddCircle ℝ (r j)))
          (ContinuousMap.toLp 2 haarAddCircle ℝ (Ld.comp (J j)))]
          with z hM hrz hdz hHz hout
      rw [hout, Pi.add_apply, hM, hrz, hdz, hHz]
      rfl
    simpa only [Function.comp_def, heq] using hlim.cauchySeq
  · obtain ⟨MR, _hMRnorm, hMR⟩ := exists_continuousL2_product
      (haarAddCircle : Measure (AddCircle L))
      (ContinuousLinearMap.id ℝ (W →L[ℝ] ℝ))
    have hprod : Continuous (fun z : C(AddCircle L, W →L[ℝ] ℝ) × Lp W 2 haarAddCircle =>
        MR z.1 z.2) := (MR.continuous.comp continuous_fst).clm_apply continuous_snd
    have hlim := ((hprod.tendsto (Llam.comp J0, R0)).comp (hLlam.prodMk_nhds hR0)).add
      (((ContinuousMap.toLp 2 haarAddCircle ℝ).continuous.tendsto (Lη.comp J0)).comp hLη)
    have heq (j : ℕ) : MR (Llam.comp (J j)) (ContinuousMap.toLp 2 haarAddCircle ℝ (r j)) +
        ContinuousMap.toLp 2 haarAddCircle ℝ (Lη.comp (J j)) =
          ContinuousMap.toLp 2 haarAddCircle ℝ (w j) := by
      apply Lp.ext
      filter_upwards [hMR (Llam.comp (J j)) (ContinuousMap.toLp 2 haarAddCircle ℝ (r j)),
        ContinuousMap.coeFn_toLp (p := 2) haarAddCircle (𝕜 := ℝ) (r j),
        ContinuousMap.coeFn_toLp (p := 2) haarAddCircle (𝕜 := ℝ) (Lη.comp (J j)),
        ContinuousMap.coeFn_toLp (p := 2) haarAddCircle (𝕜 := ℝ) (w j),
        Lp.coeFn_add (MR (Llam.comp (J j)) (ContinuousMap.toLp 2 haarAddCircle ℝ (r j)))
          (ContinuousMap.toLp 2 haarAddCircle ℝ (Lη.comp (J j)))]
          with z hM hrz hdz hwz hout
      rw [hout, Pi.add_apply, hM, hrz, hdz, hwz]
      rfl
    simpa only [Function.comp_def, heq] using hlim.cauchySeq

end PoincareConjecture.M63
