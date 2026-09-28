import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.AlphaCriticalJetData
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.AlphaCriticalJetWeakCalculus
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.AlphaCriticalFluxExtension
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.AlphaCriticalWeakEquation















set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter Metric
open scoped ContDiff Topology ENNReal Manifold
open Poincare.Analysis.Sobolev.Weak

noncomputable section

namespace PoincareConjecture.M60

attribute [local instance] affineJetPrincipalNormedGroup affineJetPrincipalNormedSpace
  affineJetSourceNormedGroup affineJetSourceNormedSpace



theorem suAffineCoefficient_supported_extension {p q : ℕ}
    {O K : Set (EuclideanSpace ℝ (Fin p))} (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    (A : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin q) →L[ℝ] ℝ)
    (c : EuclideanSpace ℝ (Fin p) → ℝ)
    (hA : ContDiffOn ℝ 1 A O) (hc : ContDiffOn ℝ 1 c O) :
    ∃ (F : EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin q) → ℝ) (C : ℝ),
      ContDiff ℝ 1 F ∧ 0 < C ∧
      (∀ z, ‖fderiv ℝ F z‖ ≤ C * (1 + ‖z‖ ^ 2)) ∧
      ∀ x ∈ K, ∀ v : EuclideanSpace ℝ (Fin q),
        F =ᶠ[𝓝 (x, v)] fun z => A z.1 z.2 + c z.1 := by
  let N : EuclideanSpace ℝ (Fin p) × (ℝ × EuclideanSpace ℝ (Fin q)) → ℝ :=
    fun z => A z.1 z.2.2 + z.2.1 * c z.1
  apply suHomogeneous_base_extension hO hK hKO (fun z => A z.1 z.2 + c z.1) N
    (show (-2 : ℝ) ≤ -1 by norm_num)
  · exact ((hA.comp contDiff_fst.contDiffOn (fun _ hx => hx.1)).clm_apply
      contDiff_snd.contDiffOn).add
        (hc.comp contDiff_fst.contDiffOn (fun _ hx => hx.1))
  · intro x hx t v _ _
    have hAc := (hA.contDiffAt (hO.mem_nhds hx)).comp (x, t, v) contDiffAt_fst
    have hcc := (hc.contDiffAt (hO.mem_nhds hx)).comp (x, t, v) contDiffAt_fst
    exact (hAc.clm_apply contDiffAt_snd.snd).add (contDiffAt_snd.fst.mul hcc)
  · intro x _ t ht v
    dsimp only [N]
    simp only [map_smul, smul_eq_mul, Real.rpow_neg_one]
    field_simp



theorem suJetCoefficient_derivative_memLp {m : ℕ}
    {u V : LoopPlane → EuclideanSpace ℝ (Fin m)} {a : LoopPlane} {R : ℝ} {p : ℝ≥0∞}
    (hu : ContinuousOn u (closedBall a R))
    (hV : MemLp V p (volume.restrict (ball a R)))
    {O : Set (LoopPlane × EuclideanSpace ℝ (Fin m))} (hO : IsOpen O)
    (hmap : MapsTo (fun x => (x, u x)) (closedBall a R) O)
    {F : (LoopPlane × EuclideanSpace ℝ (Fin m)) → ℝ} (hF : ContDiffOn ℝ 1 F O)
    (i : Fin 2) : MemLp
      (fun x => fderiv ℝ F (x, u x) (EuclideanSpace.single i 1, V x))
        p (volume.restrict (ball a R)) := by
  let : IsFiniteMeasure (volume.restrict (ball a R)) := ⟨by
    simpa only [Measure.restrict_apply_univ] using
      (measure_ball_lt_top : volume (ball a R) < ⊤)⟩
  have hD : ContinuousOn (fun x => fderiv ℝ F (x, u x)) (closedBall a R) :=
    (hF.continuousOn_fderiv_of_isOpen hO (by norm_num)).comp
      (continuousOn_id.prodMk hu) hmap
  obtain ⟨C, hC⟩ := (isCompact_closedBall a R).exists_bound_of_continuousOn hD
  have hQ : MemLp (fun x => (EuclideanSpace.single i (1 : ℝ), V x))
      p (volume.restrict (ball a R)) := memLp_prod_iff.mpr ⟨memLp_const _, hV⟩
  have hm : Continuous (fun z :
      ((LoopPlane × EuclideanSpace ℝ (Fin m)) →L[ℝ] ℝ) ×
        (LoopPlane × EuclideanSpace ℝ (Fin m)) => z.1 z.2) :=
    continuous_fst.clm_apply continuous_snd
  apply (hQ.norm.const_mul (max C 0)).of_le
    (hm.comp_aestronglyMeasurable
      (((hD.mono ball_subset_closedBall).aestronglyMeasurable measurableSet_ball).prodMk
        hQ.aestronglyMeasurable))
  filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
  calc
    _ ≤ ‖fderiv ℝ F (x, u x)‖ * ‖(EuclideanSpace.single i (1 : ℝ), V x)‖ :=
      (fderiv ℝ F (x, u x)).le_opNorm _
    _ ≤ max C 0 * ‖(EuclideanSpace.single i (1 : ℝ), V x)‖ :=
      mul_le_mul_of_nonneg_right ((hC x (ball_subset_closedBall hx)).trans
        (le_max_left C 0)) (norm_nonneg _)
    _ = _ := by rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]



theorem suWeakPartial_jet_coefficient_mul {m : ℕ}
    {u : LoopPlane → EuclideanSpace ℝ (Fin m)}
    {V : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin m)}
    {g : LoopPlane → ℝ} {Dg : Fin 2 → LoopPlane → ℝ}
    {a : LoopPlane} {R r : ℝ} (hr : 0 < r) (hrR : r < R)
    (hu : ContinuousOn u (closedBall a R))
    (hV : ∀ i, MemLp (V i) 2 (volume.restrict (ball a R)))
    (hwu : ∀ i c, HasWeakPartialDeriv i (fun x => V i x c) (fun x => u x c) (ball a R))
    (hg : MemLp g 4 (volume.restrict (ball a R)))
    (hDg : ∀ i, MemLp (Dg i) 2 (volume.restrict (ball a R)))
    (hwg : ∀ i, HasWeakPartialDeriv i (Dg i) g (ball a R))
    {O : Set (LoopPlane × EuclideanSpace ℝ (Fin m))} (hO : IsOpen O)
    (hmap : MapsTo (fun x => (x, u x)) (closedBall a R) O)
    {F : (LoopPlane × EuclideanSpace ℝ (Fin m)) → ℝ} (hF : ContDiffOn ℝ 1 F O)
    (i : Fin 2) :
    HasWeakPartialDeriv i
      (fun x => fderiv ℝ F (x, u x) (EuclideanSpace.single i 1, V i x) * g x +
        F (x, u x) * Dg i x) (fun x => F (x, u x) * g x) (ball a r) := by
  let s := (R + r) / 2
  have hs : 0 < s := by dsimp [s]; linarith
  have hrs : r < s := by dsimp [s]; linarith
  have hsR : s < R := by dsimp [s]; linarith
  have hsub : ball a s ⊆ ball a R := ball_subset_ball hsR.le
  let K := (fun x => (x, u x)) '' closedBall a R
  have hK : IsCompact K := (isCompact_closedBall a R).image_of_continuousOn
    (continuousOn_id.prodMk hu)
  have hKO : K ⊆ O := by rintro _ ⟨x, hx, rfl⟩; exact hmap hx
  have hchain (j : Fin 2) := suWeakPartial_source_comp_on_compact hs hsR
    (suContinuous_memLp_ball hu : MemLp u 4 (volume.restrict (ball a R))) hV hwu
    hO hK hKO (fun x hx => mem_image_of_mem _ hx) hF j
  have hfc : ContinuousOn (fun x => F (x, u x)) (closedBall a R) :=
    hF.continuousOn.comp (continuousOn_id.prodMk hu) hmap
  apply suWeakPartial_mul hr hrs
    ((suContinuous_memLp_ball hfc).mono_measure (Measure.restrict_mono hsub le_rfl))
    (hg.mono_measure (Measure.restrict_mono hsub le_rfl))
    (fun j => (suJetCoefficient_derivative_memLp hu (hV j) hO hmap hF j).mono_measure
      (Measure.restrict_mono hsub le_rfl))
    (fun j => (hDg j).mono_measure (Measure.restrict_mono hsub le_rfl))
    hchain (fun j => (hwg j).restrict isOpen_ball hsub) i


def suAffineJetFlux {m : ℕ} (C : SUAffineJetCoefficients m) (a : Fin m) (i : Fin 2)
    (z : EuclideanSpace ℝ (Fin ((2 + m) + (m + m)))) : ℝ :=
  C.flux (suAlphaJetEquiv z).1 (suAlphaJetEquiv z).2 (suColumnBasis a i)



theorem suAffineJetFlux_extension {m : ℕ} (C : SUAffineJetCoefficients m)
    {O K : Set (LoopPlane × EuclideanSpace ℝ (Fin m))}
    (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    (hA : ContDiffOn ℝ 1 C.principal O) (hc : ContDiffOn ℝ 1 C.fluxOffset O)
    (a : Fin m) (i : Fin 2) :
    ∃ (F : EuclideanSpace ℝ (Fin ((2 + m) + (m + m))) → ℝ) (D : ℝ),
      ContDiff ℝ 1 F ∧ 0 < D ∧
      (∀ z, ‖fderiv ℝ F z‖ ≤ D * (1 + ‖z‖ ^ 2)) ∧
      ∀ x ∈ K, ∀ q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m),
        F =ᶠ[𝓝 (suAlphaJetEquiv.symm (x, q))] suAffineJetFlux C a i := by
  let P := EuclideanSpace ℝ (Fin (2 + m))
  let Q := EuclideanSpace ℝ (Fin (m + m))
  let ep : P ≃L[ℝ] LoopPlane × EuclideanSpace ℝ (Fin m) := EuclideanSpace.finAddEquivProd
  let eq : Q ≃L[ℝ] EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) :=
    EuclideanSpace.finAddEquivProd
  let ee : EuclideanSpace ℝ (Fin ((2 + m) + (m + m))) ≃L[ℝ] P × Q :=
    EuclideanSpace.finAddEquivProd
  let A : P → Q →L[ℝ] ℝ := fun z =>
    ((C.principal (ep z)).flip (suColumnBasis a i)).comp eq.toContinuousLinearMap
  let c : P → ℝ := fun z => C.fluxOffset (ep z) (suColumnBasis a i)
  have hAc : ContDiffOn ℝ 1 A (ep ⁻¹' O) := by
    apply contDiffOn_clm_apply.mpr
    intro q
    change ContDiffOn ℝ 1 (fun z => C.principal (ep z) (eq q) (suColumnBasis a i)) _
    exact ((hA.comp ep.contDiff.contDiffOn (fun _ hx => hx)).clm_apply
      contDiffOn_const).clm_apply contDiffOn_const
  have hcc : ContDiffOn ℝ 1 c (ep ⁻¹' O) :=
    (hc.comp ep.contDiff.contDiffOn (fun _ hx => hx)).clm_apply contDiffOn_const
  obtain ⟨B, D, hB, hD, hDB, he⟩ := suAffineCoefficient_supported_extension
    (hO.preimage ep.continuous) (hK.image ep.symm.continuous)
    (by rintro _ ⟨z, hz, rfl⟩; simpa only [mem_preimage, ep.apply_symm_apply] using hKO hz)
    A c hAc hcc
  obtain ⟨D', hD', hbound⟩ := suQuadraticDerivative_comp_linear hB hD hDB ee.toContinuousLinearMap
  refine ⟨B ∘ ee, D', hB.comp ee.contDiff, hD', hbound, ?_⟩
  intro x hx q
  have hpoint : ee (suAlphaJetEquiv.symm (x, q)) = (ep.symm x, eq.symm q) :=
    ee.apply_symm_apply _
  have ht : Tendsto ee (𝓝 (suAlphaJetEquiv.symm (x, q))) (𝓝 (ep.symm x, eq.symm q)) := by
    simpa only [hpoint] using
      (ee.continuous.continuousAt.tendsto (x := suAlphaJetEquiv.symm (x, q)))
  have heq := (he (ep.symm x) (mem_image_of_mem _ hx) (eq.symm q)).comp_tendsto ht
  filter_upwards [heq] with z hz
  simp only [Function.comp_apply] at hz
  change B (ee z) = _
  rw [hz]
  rfl



theorem SUInitialGain.affine_flux_weak_derivative {m : ℕ}
    {u : LoopPlane → EuclideanSpace ℝ (Fin m)}
    {V : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin m)} {center : LoopPlane} {R : ℝ}
    (G : SUInitialGain u V center R) (C : SUAffineJetCoefficients m)
    {O : Set (LoopPlane × EuclideanSpace ℝ (Fin m))} (hO : IsOpen O)
    (hmap : MapsTo (fun x => (x, u x)) (closedBall center G.radius) O)
    (hA : ContDiffOn ℝ 1 C.principal O) (hc : ContDiffOn ℝ 1 C.fluxOffset O)
    (a : Fin m) (k i : Fin 2) :
    IntegrableOn (fun x => fderiv ℝ (suAffineJetFlux C a k) (suWeakAlphaJet u V x)
      (suWeakAlphaJetColumn V G.hessian i x)) (ball center (G.radius / 2)) ∧
      HasWeakPartialDeriv i
        (fun x => fderiv ℝ (suAffineJetFlux C a k) (suWeakAlphaJet u V x)
          (suWeakAlphaJetColumn V G.hessian i x))
        (fun x => C.flux (x, u x) (V 0 x, V 1 x) (suColumnBasis a k))
        (ball center (G.radius / 2)) := by
  let K := (fun x => (x, u x)) '' closedBall center G.radius
  have hK : IsCompact K := (isCompact_closedBall _ _).image_of_continuousOn
    (continuousOn_id.prodMk G.coordinate_continuous)
  have hKO : K ⊆ O := by rintro _ ⟨x, hx, rfl⟩; exact hmap hx
  obtain ⟨F, D, hF, hD, hb, he⟩ := suAffineJetFlux_extension C hO hK hKO hA hc a k
  have heq (x : LoopPlane) (hx : x ∈ closedBall center G.radius) :
      F =ᶠ[𝓝 (suWeakAlphaJet u V x)] suAffineJetFlux C a k :=
    he (x, u x) (mem_image_of_mem _ hx) (V 0 x, V 1 x)
  obtain ⟨hJ, hW, hw⟩ := G.weak_jet_data
  have hr : 0 < G.radius / 2 := half_pos G.radius_pos
  have hrR : G.radius / 2 < G.radius := half_lt_self G.radius_pos
  have hsub := ball_subset_ball (x := center) hrR.le
  let : IsFiniteMeasure (volume.restrict (ball center G.radius)) := ⟨by
    simpa only [Measure.restrict_apply_univ] using
      (measure_ball_lt_top : volume (ball center G.radius) < ⊤)⟩
  have hi := (suQuadraticDerivative_integrable hJ (hW i) hF hD hb).mono_measure
    (Measure.restrict_mono hsub le_rfl)
  have hd := suWeakPartial_comp_quadratic hr hrR hJ hW hw hF hD hb i
  have hderiv : (fun x => fderiv ℝ F (suWeakAlphaJet u V x)
      (suWeakAlphaJetColumn V G.hessian i x)) =ᵐ[volume.restrict (ball center (G.radius / 2))]
        fun x => fderiv ℝ (suAffineJetFlux C a k) (suWeakAlphaJet u V x)
          (suWeakAlphaJetColumn V G.hessian i x) := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    rw [(heq x (ball_subset_closedBall (hsub hx))).fderiv_eq]
  refine ⟨hi.congr hderiv, suWeakPartial_congr_ae hd ?_ hderiv.symm⟩
  filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
  have ht := (heq x (ball_subset_closedBall (hsub hx))).self_of_nhds.symm
  simpa only [suAffineJetFlux, suWeakAlphaJet, suAlphaJetEquiv.apply_symm_apply] using ht



theorem suAffineJetFlux_fderiv {m : ℕ} (C : SUAffineJetCoefficients m)
    (z : LoopPlane × EuclideanSpace ℝ (Fin m))
    (q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
    (v : LoopPlane × EuclideanSpace ℝ (Fin m))
    (H : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
    (hA : DifferentiableAt ℝ C.principal z) (hc : DifferentiableAt ℝ C.fluxOffset z)
    (a : Fin m) (i : Fin 2) :
    fderiv ℝ (suAffineJetFlux C a i) (suAlphaJetEquiv.symm (z, q))
      (suAlphaJetEquiv.symm (v, H)) =
        (C.principal z H + fderiv ℝ C.principal z v q + fderiv ℝ C.fluxOffset z v)
          (suColumnBasis a i) := by
  let B := fun p : (LoopPlane × EuclideanSpace ℝ (Fin m)) ×
    (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) => C.flux p.1 p.2
  have hB : DifferentiableAt ℝ B (z, q) :=
    ((hA.comp (z, q) differentiableAt_fst).clm_apply differentiableAt_snd).add
      (hc.comp (z, q) differentiableAt_fst)
  change fderiv ℝ ((fun p => B p (suColumnBasis a i)) ∘ suAlphaJetEquiv)
    (suAlphaJetEquiv.symm (z, q)) (suAlphaJetEquiv.symm (v, H)) = _
  rw [suAlphaJetEquiv.comp_right_fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    suAlphaJetEquiv.apply_symm_apply]
  rw [fderiv_clm_apply hB (differentiableAt_const _)]
  simp only [fderiv_fun_const, add_apply, ContinuousLinearMap.comp_apply,
    Pi.zero_apply, zero_apply, map_zero, zero_add, ContinuousLinearMap.flip_apply]
  change (fderiv ℝ (fun p => C.flux p.1 p.2) (z, q) (v, H)) (suColumnBasis a i) = _
  rw [C.flux_fderiv z q hA hc v H]
  rfl




theorem suAffineWeakEquation_trace {m : ℕ}
    {u : LoopPlane → EuclideanSpace ℝ (Fin m)}
    {V : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin m)} {center : LoopPlane} {R : ℝ}
    (S : SUQuadraticWeakSystem u V center R) (C : SUAffineJetCoefficients m)
    (hflux : S.flux = C.flux) (hsource : S.source = C.source)
    (G : SUInitialGain u V center R)
    {O : Set (LoopPlane × EuclideanSpace ℝ (Fin m))} (hO : IsOpen O)
    (hmap : MapsTo (fun x => (x, u x)) (closedBall center G.radius) O)
    (hA : ContDiffOn ℝ 1 C.principal O) (hc : ContDiffOn ℝ 1 C.fluxOffset O) :
    ∀ᵐ x ∂volume.restrict (ball center (G.radius / 2)),
      C.principalTrace (x, u x) (fun i j => G.hessian i j x) +
        C.lowerTrace (x, u x) (fun i => V i x) = 0 := by
  let r := G.radius / 2
  have hrG : r < G.radius := half_lt_self G.radius_pos
  have hrR : r ≤ R := hrG.le.trans G.radius_lt.le
  have hsub := ball_subset_ball (x := center) hrR
  let : IsFiniteMeasure (volume.restrict (ball center R)) := ⟨by
    simpa only [Measure.restrict_apply_univ] using
      (measure_ball_lt_top : volume (ball center R) < ⊤)⟩
  have hF (a : Fin m) (i : Fin 2) : IntegrableOn
      (fun x => C.flux (x, u x) (V 0 x, V 1 x) (suColumnBasis a i)) (ball center R) := by
    have ht : IntegrableOn (S.componentFlux a i) (ball center R) :=
      (S.component_memLp.1 a i).integrable (by norm_num)
    change IntegrableOn (fun x => S.flux (x, u x) (V 0 x, V 1 x)
      (suColumnBasis a i)) (ball center R) at ht
    rwa [hflux] at ht
  have hb (a : Fin m) : IntegrableOn
      (fun x => C.source (x, u x) (V 0 x, V 1 x) (EuclideanSpace.single a 1))
      (ball center R) := by
    have ht : IntegrableOn (S.componentSource a) (ball center R) := S.component_memLp.2 a
    change IntegrableOn (fun x => S.source (x, u x) (V 0 x, V 1 x)
      (EuclideanSpace.single a 1)) (ball center R) at ht
    rwa [hsource] at ht
  have hae : ∀ᵐ x ∂volume.restrict (ball center r), ∀ a : Fin m,
      (∑ i : Fin 2, fderiv ℝ (suAffineJetFlux C a i) (suWeakAlphaJet u V x)
        (suWeakAlphaJetColumn V G.hessian i x)) +
          C.source (x, u x) (V 0 x, V 1 x) (EuclideanSpace.single a 1) = 0 := by
    rw [ae_all_iff]
    intro a
    apply suWeakDivergence_eq_ae isOpen_ball
      (fun i => (hF a i).mono_set hsub)
      (fun i => (G.affine_flux_weak_derivative C hO hmap hA hc a i i).1)
      ((hb a).mono_set hsub)
      (fun i => (G.affine_flux_weak_derivative C hO hmap hA hc a i i).2)
    intro phi hp hpc hps
    have heq := S.scalar_equation a hp hpc (hps.trans hsub)
    simp only [SUQuadraticWeakSystem.componentFlux, SUQuadraticWeakSystem.componentSource,
      hflux, hsource] at heq
    have hD (x : LoopPlane) (hx : x ∉ ball center r) (i : Fin 2) :
        fderiv ℝ phi x (EuclideanSpace.single i 1) = 0 :=
      image_eq_zero_of_notMem_tsupport
        (f := fun y => fderiv ℝ phi y (EuclideanSpace.single i 1))
        (fun ht => hx (hps (tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1) ht)))
    have hp0 (x : LoopPlane) (hx : x ∉ ball center r) : phi x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun ht => hx (hps ht))
    rwa [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_ball hsub
        (fun x hx => by simp only [hD x hx.2, mul_zero, Finset.sum_const_zero]),
      setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_ball hsub
        (fun x hx => by rw [hp0 x hx.2, mul_zero])] at heq
  filter_upwards [hae, ae_restrict_mem measurableSet_ball] with x hx hxr
  have hxO : (x, u x) ∈ O := hmap
    (closedBall_subset_closedBall hrG.le (ball_subset_closedBall hxr))
  have hAc := (hA.contDiffAt (hO.mem_nhds hxO)).differentiableAt (by norm_num)
  have hcc := (hc.contDiffAt (hO.mem_nhds hxO)).differentiableAt (by norm_num)
  have hsplit (a : Fin m) (i : Fin 2) :
      fderiv ℝ (suAffineJetFlux C a i) (suWeakAlphaJet u V x)
        (suWeakAlphaJetColumn V G.hessian i x) =
          C.principal (x, u x) (G.hessian 0 i x, G.hessian 1 i x) (suColumnBasis a i) +
            (fderiv ℝ C.principal (x, u x) (EuclideanSpace.single i 1, V i x) (V 0 x, V 1 x) +
              fderiv ℝ C.fluxOffset (x, u x) (EuclideanSpace.single i 1, V i x))
                (suColumnBasis a i) := by
    rw [suWeakAlphaJet, suWeakAlphaJetColumn, suAffineJetFlux_fderiv C _ _ _ _ hAc hcc]
    simp only [add_apply, add_assoc]
  ext a
  have he := hx a
  simp_rw [hsplit, Finset.sum_add_distrib] at he
  change (∑ i : Fin 2, C.principal (x, u x)
    (G.hessian 0 i x, G.hessian 1 i x) (suColumnBasis a i)) +
      (C.source (x, u x) (V 0 x, V 1 x) (EuclideanSpace.single a 1) +
        ∑ i : Fin 2, (fderiv ℝ C.principal (x, u x) (EuclideanSpace.single i 1, V i x)
          (V 0 x, V 1 x) + fderiv ℝ C.fluxOffset (x, u x)
            (EuclideanSpace.single i 1, V i x)) (suColumnBasis a i)) = 0
  linarith only [he]


end PoincareConjecture.M60
