import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.AlphaCriticalAffineEquation
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.AlphaCriticalJetSystem
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.AlphaCriticalJetNormalization
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.AlphaCriticalAffineHolder














set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter Metric
open scoped ContDiff Topology ENNReal Manifold
open Poincare.Analysis.Sobolev.Weak

noncomputable section

namespace PoincareConjecture.M60

attribute [local instance] affineJetPrincipalNormedGroup affineJetPrincipalNormedSpace
  affineJetSourceNormedGroup affineJetSourceNormedSpace



theorem suFirstJet_affine_coefficient_chain {m : ℕ}
    {u : LoopPlane → EuclideanSpace ℝ (Fin m)}
    {V : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin m)} {center : LoopPlane} {R : ℝ}
    (G : SUInitialGain u V center R) (H : SUC1HolderGain u V center G.radius)
    {r : ℝ} (hr : 0 < r) (hrH : r < H.radius / 2)
    {O : Set (LoopPlane × EuclideanSpace ℝ (Fin (3 * m)))} (hO : IsOpen O)
    (hmap : MapsTo (fun x => (x, suFirstJet u x)) (closedBall center (H.radius / 2)) O)
    {F : (LoopPlane × EuclideanSpace ℝ (Fin (3 * m))) → ℝ}
    (hF : ContDiffOn ℝ 1 F O) :
    MemLp (fun x => F (x, suFirstJet u x)) 2
        (volume.restrict (ball center (H.radius / 2))) ∧
      ∀ k : Fin 2,
        MemLp (fun x => fderiv ℝ F (x, suFirstJet u x)
          (EuclideanSpace.single k 1, suFirstJetWeakColumn V G.hessian k x)) 2
          (volume.restrict (ball center (H.radius / 2))) ∧
        HasWeakPartialDeriv k
          (fun x => fderiv ℝ F (x, suFirstJet u x)
            (EuclideanSpace.single k 1, suFirstJetWeakColumn V G.hessian k x))
          (fun x => F (x, suFirstJet u x)) (ball center r) := by
  let rho := H.radius / 2
  let : IsFiniteMeasure (volume.restrict (ball center rho)) := ⟨by
    simpa only [Measure.restrict_apply_univ] using
      (measure_ball_lt_top : volume (ball center rho) < ⊤)⟩
  let U (x : LoopPlane) := (x, suFirstJet u x)
  let K := U '' closedBall center rho
  obtain ⟨hJ, _, hW, hw⟩ := suFirstJet_weak_data G H
  have hU : ContinuousOn U (closedBall center rho) := continuousOn_id.prodMk hJ
  have hK : IsCompact K := (isCompact_closedBall center rho).image_of_continuousOn hU
  have hKO : K ⊆ O := by rintro _ ⟨x, hx, rfl⟩; exact hmap hx
  have hfc : ContinuousOn (fun x => F (U x)) (closedBall center rho) :=
    hF.continuousOn.comp hU hmap
  have hdfc : ContinuousOn (fun x => fderiv ℝ F (U x)) (closedBall center rho) :=
    (hF.continuousOn_fderiv_of_isOpen hO (by norm_num)).comp hU hmap
  refine ⟨suContinuous_memLp_ball hfc, fun k => ⟨?_, ?_⟩⟩
  · exact (ContinuousLinearMap.apply ℝ ℝ
      (E := LoopPlane × EuclideanSpace ℝ (Fin (3 * m)))).memLp_of_bilin
        (p := 2) (q := ⊤) 2 (memLp_prod_iff.mpr ⟨memLp_const _, hW k⟩)
          (suContinuous_memLp_ball hdfc)
  · exact suWeakPartial_source_comp_on_compact hr hrH (suContinuous_memLp_ball hJ) hW hw
      hO hK hKO (fun x hx => mem_image_of_mem U hx) hF k

namespace SUAffineJetCoefficients


theorem prolong_flux_zero {m : ℕ} (C : SUAffineJetCoefficients m)
    (z : LoopPlane × EuclideanSpace ℝ (Fin (3 * m)))
    (q : EuclideanSpace ℝ (Fin (3 * m)) × EuclideanSpace ℝ (Fin (3 * m)))
    (a : Fin m) (i : Fin 2) :
    C.prolong.flux z q (suColumnBasis (finProdFinEquiv ((0 : Fin 3), a)) i) =
      C.flux (z.1, suJetBlock (0 : Fin 3) z.2)
        (((suJetBlock (0 : Fin 3)).prodMap (suJetBlock (0 : Fin 3))) q)
        (suColumnBasis a i) := by
  classical
  simp [prolong, flux, suJetBlockPrincipal, suJetBlock_columnBasis,
    ContinuousLinearMap.bilinearComp_apply, Fin.sum_univ_succ]


theorem prolong_source_zero {m : ℕ} (C : SUAffineJetCoefficients m)
    (z : LoopPlane × EuclideanSpace ℝ (Fin (3 * m)))
    (q : EuclideanSpace ℝ (Fin (3 * m)) × EuclideanSpace ℝ (Fin (3 * m))) (a : Fin m) :
    C.prolong.source z q (EuclideanSpace.single (finProdFinEquiv ((0 : Fin 3), a)) 1) =
      C.source (z.1, suJetBlock (0 : Fin 3) z.2)
        (((suJetBlock (0 : Fin 3)).prodMap (suJetBlock (0 : Fin 3))) q)
        (EuclideanSpace.single a 1) := by
  classical
  simp [prolong, source, suJetBlock_single, ContinuousLinearMap.compL_apply,
    Fin.sum_univ_succ]


theorem prolong_flux_succ {m : ℕ} (C : SUAffineJetCoefficients m)
    (z : LoopPlane × EuclideanSpace ℝ (Fin (3 * m)))
    (q : EuclideanSpace ℝ (Fin (3 * m)) × EuclideanSpace ℝ (Fin (3 * m)))
    (hA : DifferentiableAt ℝ C.principal (suAlphaFirstJetPoint z).1)
    (hc : DifferentiableAt ℝ C.fluxOffset (suAlphaFirstJetPoint z).1)
    (k : Fin 2) (a : Fin m) (i : Fin 2) :
    C.prolong.flux z q (suColumnBasis (finProdFinEquiv (k.succ, a)) i) =
      fderiv ℝ (fun p => C.flux p.1 p.2) (suAlphaFirstJetPoint z)
        ((EuclideanSpace.single k 1, suJetBlock k.succ z.2),
          ((suJetBlock k.succ).prodMap (suJetBlock k.succ)) q) (suColumnBasis a i) := by
  classical
  rw [C.flux_fderiv _ _ hA hc]
  fin_cases k <;> simp [prolong, flux, suJetBlockPrincipal, suJetBlock_columnBasis,
    ContinuousLinearMap.bilinearComp_apply, Fin.sum_univ_succ, suAlphaFirstJetPoint, add_assoc]


theorem prolong_source_succ {m : ℕ} (C : SUAffineJetCoefficients m)
    (z : LoopPlane × EuclideanSpace ℝ (Fin (3 * m)))
    (q : EuclideanSpace ℝ (Fin (3 * m)) × EuclideanSpace ℝ (Fin (3 * m)))
    (hB : DifferentiableAt ℝ C.sourceLinear (suAlphaFirstJetPoint z).1)
    (hd : DifferentiableAt ℝ C.sourceOffset (suAlphaFirstJetPoint z).1)
    (k : Fin 2) (a : Fin m) :
    C.prolong.source z q (EuclideanSpace.single (finProdFinEquiv (k.succ, a)) 1) =
      fderiv ℝ (fun p => C.source p.1 p.2) (suAlphaFirstJetPoint z)
        ((EuclideanSpace.single k 1, suJetBlock k.succ z.2),
          ((suJetBlock k.succ).prodMap (suJetBlock k.succ)) q) (EuclideanSpace.single a 1) := by
  classical
  rw [C.source_fderiv _ _ hB hd]
  fin_cases k <;> simp [prolong, source, suJetBlock_single,
    ContinuousLinearMap.compL_apply, Fin.sum_univ_succ, suAlphaFirstJetPoint, add_assoc]

end SUAffineJetCoefficients




theorem suAffineWeakSystem_prolong_equation {m : ℕ}
    {u : LoopPlane → EuclideanSpace ℝ (Fin m)}
    {V : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin m)} {center : LoopPlane} {R : ℝ}
    (S : SUQuadraticWeakSystem u V center R) (C : SUAffineJetCoefficients m)
    (hflux : S.flux = C.flux) (hsource : S.source = C.source)
    (G : SUInitialGain u V center R) (H : SUC1HolderGain u V center G.radius)
    {O : Set (LoopPlane × EuclideanSpace ℝ (Fin m))} (hO : IsOpen O)
    (hmap : MapsTo (fun x => (x, u x)) (closedBall center G.radius) O)
    (hA : ContDiffOn ℝ 1 C.principal O) (hc : ContDiffOn ℝ 1 C.fluxOffset O)
    (hB : ContDiffOn ℝ 1 C.sourceLinear O) (hd : ContDiffOn ℝ 1 C.sourceOffset O)
    {r : ℝ} (hr : 0 < r) (hrH : r < H.radius / 2)
    (a : Fin (3 * m)) {phi : LoopPlane → ℝ} (hp : ContDiff ℝ ∞ phi)
    (hpc : HasCompactSupport phi) (hps : tsupport phi ⊆ ball center r) :
    (∫ x in ball center r, ∑ i : Fin 2,
      C.prolong.flux (x, suFirstJet u x)
        (suFirstJetWeakColumn V G.hessian 0 x, suFirstJetWeakColumn V G.hessian 1 x)
        (suColumnBasis a i) * fderiv ℝ phi x (EuclideanSpace.single i 1)) =
      ∫ x in ball center r, C.prolong.source (x, suFirstJet u x)
        (suFirstJetWeakColumn V G.hessian 0 x, suFirstJetWeakColumn V G.hessian 1 x)
        (EuclideanSpace.single a 1) * phi x := by
  classical
  let J := suFirstJet u
  let W := suFirstJetWeakColumn V G.hessian
  let U (x : LoopPlane) := (x, J x)
  let F (a : Fin m) (i : Fin 2) (z : LoopPlane × EuclideanSpace ℝ (Fin (3 * m))) :=
    C.flux (suAlphaFirstJetPoint z).1 (suAlphaFirstJetPoint z).2 (suColumnBasis a i)
  let B (a : Fin m) (z : LoopPlane × EuclideanSpace ℝ (Fin (3 * m))) :=
    C.source (suAlphaFirstJetPoint z).1 (suAlphaFirstJetPoint z).2
      (EuclideanSpace.single a 1)
  let DF (a : Fin m) (k i : Fin 2) (x : LoopPlane) :=
    fderiv ℝ (F a i) (U x) (EuclideanSpace.single k 1, W k x)
  let DB (a : Fin m) (k : Fin 2) (x : LoopPlane) :=
    fderiv ℝ (B a) (U x) (EuclideanSpace.single k 1, W k x)
  let OJ := {z : LoopPlane × EuclideanSpace ℝ (Fin (3 * m)) |
    (suAlphaFirstJetPoint z).1 ∈ O}
  have hOJ : IsOpen OJ := hO.preimage suAlphaFirstJetPoint_contDiff.continuous.fst
  have hJG : H.radius / 2 < G.radius :=
    (half_lt_self H.radius_pos).trans H.radius_lt
  have hJmap : MapsTo U (closedBall center (H.radius / 2)) OJ := by
    intro x hx
    change (x, suJetBlock (0 : Fin 3) (suFirstJet u x)) ∈ O
    rw [suJetBlock_firstJet_zero]
    exact hmap (closedBall_subset_closedBall hJG.le hx)
  have hFs (a : Fin m) (i : Fin 2) : ContDiffOn ℝ 1 (F a i) OJ := by
    intro z hz
    have hP : ContDiffAt ℝ 1 suAlphaFirstJetPoint z :=
      (@suAlphaFirstJetPoint_contDiff m).contDiffAt.of_le (by simp)
    have hAc := (hA.contDiffAt (hO.mem_nhds hz)).comp z hP.fst
    have hcc := (hc.contDiffAt (hO.mem_nhds hz)).comp z hP.fst
    exact (((hAc.clm_apply hP.snd).add hcc).clm_apply contDiffAt_const).contDiffWithinAt
  have hBs (a : Fin m) : ContDiffOn ℝ 1 (B a) OJ := by
    intro z hz
    have hP : ContDiffAt ℝ 1 suAlphaFirstJetPoint z :=
      (@suAlphaFirstJetPoint_contDiff m).contDiffAt.of_le (by simp)
    have hBc := (hB.contDiffAt (hO.mem_nhds hz)).comp z hP.fst
    have hdc := (hd.contDiffAt (hO.mem_nhds hz)).comp z hP.fst
    exact (((hBc.clm_apply hP.snd).add hdc).clm_apply contDiffAt_const).contDiffWithinAt
  have hFd (a : Fin m) (i : Fin 2) :=
    suFirstJet_affine_coefficient_chain G H hr hrH hOJ hJmap (hFs a i)
  have hBd (a : Fin m) :=
    suFirstJet_affine_coefficient_chain G H hr hrH hOJ hJmap (hBs a)
  have hrH' : r < H.radius := hrH.trans (half_lt_self H.radius_pos)
  have hrG : r < G.radius := hrH'.trans H.radius_lt
  have hrR : r < R := hrG.trans G.radius_lt
  have hsub : ball center r ⊆ ball center R := ball_subset_ball hrR.le
  let mu := volume.restrict (ball center r)
  let : IsFiniteMeasure mu := ⟨by
    simpa only [mu, Measure.restrict_apply_univ] using
      (measure_ball_lt_top : volume (ball center r) < ⊤)⟩
  have hmu : mu ≤ volume.restrict (ball center (H.radius / 2)) :=
    Measure.restrict_mono (ball_subset_ball hrH.le) le_rfl
  have hcol (i : Fin 2) : ∀ᵐ x ∂mu, fderiv ℝ u x (EuclideanSpace.single i 1) = V i x :=
    ae_restrict_of_ae_restrict_of_subset (ball_subset_ball hrH'.le) (H.column_ae i)
  have hsym (i j : Fin 2) : ∀ᵐ x ∂mu, G.hessian i j x = G.hessian j i x :=
    ae_restrict_of_ae_restrict_of_subset (ball_subset_ball hrG.le) (G.hessian_symm_ae i j)
  have hpoint : ∀ᵐ x ∂mu,
      suAlphaFirstJetPoint (U x) = ((x, u x), (V 0 x, V 1 x)) := by
    filter_upwards [hcol 0, hcol 1] with x h0 h1
    dsimp only [U, J, suAlphaFirstJetPoint]
    have hd0 : suJetBlock (1 : Fin 3) (suFirstJet u x) =
        fderiv ℝ u x (EuclideanSpace.single 0 1) := by
      simpa using suJetBlock_firstJet_succ u (0 : Fin 2) x
    have hd1 : suJetBlock (2 : Fin 3) (suFirstJet u x) =
        fderiv ℝ u x (EuclideanSpace.single 1 1) := by
      simpa using suJetBlock_firstJet_succ u (1 : Fin 2) x
    rw [suJetBlock_firstJet_zero, hd0, hd1, h0, h1]
  have hFae (a : Fin m) (i : Fin 2) : ∀ᵐ x ∂mu,
      F a i (U x) = C.flux (x, u x) (V 0 x, V 1 x) (suColumnBasis a i) := by
    filter_upwards [hpoint] with x hx
    dsimp only [F]
    rw [hx]
  have hBae (a : Fin m) : ∀ᵐ x ∂mu, B a (U x) =
      C.source (x, u x) (V 0 x, V 1 x) (EuclideanSpace.single a 1) := by
    filter_upwards [hpoint] with x hx
    dsimp only [B]
    rw [hx]
  have heq (a : Fin m) (psi : LoopPlane → ℝ) (hpsi : ContDiff ℝ ∞ psi)
      (hpc : HasCompactSupport psi) (hps : tsupport psi ⊆ ball center r) :
      (∫ x in ball center r, ∑ i : Fin 2,
        F a i (U x) * fderiv ℝ psi x (EuclideanSpace.single i 1)) =
        ∫ x in ball center r, B a (U x) * psi x := by
    have he := S.scalar_equation a hpsi hpc (hps.trans hsub)
    simp only [SUQuadraticWeakSystem.componentFlux, SUQuadraticWeakSystem.componentSource,
      hflux, hsource] at he
    have hD (x : LoopPlane) (hx : x ∉ ball center r) (i : Fin 2) :
        fderiv ℝ psi x (EuclideanSpace.single i 1) = 0 :=
      image_eq_zero_of_notMem_tsupport
        (f := fun y => fderiv ℝ psi y (EuclideanSpace.single i 1))
        (fun ht => hx (hps (tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1) ht)))
    have hp0 (x : LoopPlane) (hx : x ∉ ball center r) : psi x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun ht => hx (hps ht))
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_ball hsub
        (fun x hx => by simp only [hD x hx.2, mul_zero, Finset.sum_const_zero]),
      setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_ball hsub
        (fun x hx => by rw [hp0 x hx.2, mul_zero])] at he
    calc
      _ = ∫ x in ball center r, ∑ i : Fin 2,
          C.flux (x, u x) (V 0 x, V 1 x) (suColumnBasis a i) *
            fderiv ℝ psi x (EuclideanSpace.single i 1) := by
        apply integral_congr_ae
        filter_upwards [ae_all_iff.mpr (hFae a)] with x hx
        simp only [hx]
      _ = _ := he
      _ = _ := integral_congr_ae ((hBae a).mono fun x hx => by rw [hx])
  have hFint (a : Fin m) (i : Fin 2) : IntegrableOn (fun x => F a i (U x)) (ball center r) :=
    ((hFd a i).1.mono_measure hmu).integrable (by norm_num)
  have hDFint (a : Fin m) (k i : Fin 2) : IntegrableOn (DF a k i) (ball center r) :=
    (((hFd a i).2 k).1.mono_measure hmu).integrable (by norm_num)
  obtain ⟨⟨j, a⟩, rfl⟩ := (finProdFinEquiv : Fin 3 × Fin m ≃ Fin (3 * m)).surjective a
  cases j using Fin.cases with
  | zero =>
    have hleft : ∀ᵐ x ∂mu, ∀ i : Fin 2,
        C.prolong.flux (U x) (W 0 x, W 1 x)
          (suColumnBasis (finProdFinEquiv ((0 : Fin 3), a)) i) = F a i (U x) := by
      filter_upwards [ae_all_iff.mpr (hFae a)] with x hx i
      rw [hx i, C.prolong_flux_zero]
      change C.flux (x, suJetBlock (0 : Fin 3) (suFirstJet u x))
        (suJetBlock (0 : Fin 3) (W 0 x), suJetBlock (0 : Fin 3) (W 1 x)) _ = _
      rw [suJetBlock_firstJet_zero, suJetBlock_firstJetWeakColumn_zero,
        suJetBlock_firstJetWeakColumn_zero]
    have hright : ∀ᵐ x ∂mu,
        C.prolong.source (U x) (W 0 x, W 1 x)
          (EuclideanSpace.single (finProdFinEquiv ((0 : Fin 3), a)) 1) = B a (U x) := by
      filter_upwards [hBae a] with x hx
      rw [hx, C.prolong_source_zero]
      change C.source (x, suJetBlock (0 : Fin 3) (suFirstJet u x))
        (suJetBlock (0 : Fin 3) (W 0 x), suJetBlock (0 : Fin 3) (W 1 x)) _ = _
      rw [suJetBlock_firstJet_zero, suJetBlock_firstJetWeakColumn_zero,
        suJetBlock_firstJetWeakColumn_zero]
    calc
      _ = ∫ x in ball center r, ∑ i : Fin 2,
          F a i (U x) * fderiv ℝ phi x (EuclideanSpace.single i 1) := by
        apply integral_congr_ae
        filter_upwards [hleft] with x hx
        simp only [U, J, W] at hx
        simp only [U, J, hx]
      _ = _ := heq a phi hp hpc hps
      _ = _ := integral_congr_ae (hright.mono fun x hx => by rw [hx])
  | succ k =>
    have hdir : ∀ᵐ x ∂mu,
        suAlphaFirstJetPoint (EuclideanSpace.single k 1, W k x) =
          ((EuclideanSpace.single k 1, suJetBlock k.succ (J x)),
            ((suJetBlock k.succ).prodMap (suJetBlock k.succ)) (W 0 x, W 1 x)) := by
      filter_upwards [hcol k, hsym 0 k, hsym 1 k] with x hk h0 h1
      dsimp only [suAlphaFirstJetPoint, W, J]
      have hd0 : suJetBlock (1 : Fin 3) (suFirstJetWeakColumn V G.hessian k x) =
          G.hessian 0 k x := by
        simpa using suJetBlock_firstJetWeakColumn_succ V G.hessian k (0 : Fin 2) x
      have hd1 : suJetBlock (2 : Fin 3) (suFirstJetWeakColumn V G.hessian k x) =
          G.hessian 1 k x := by
        simpa using suJetBlock_firstJetWeakColumn_succ V G.hessian k (1 : Fin 2) x
      rw [suJetBlock_firstJetWeakColumn_zero, hd0, hd1, suJetBlock_firstJet_succ]
      change ((EuclideanSpace.single k (1 : ℝ), V k x), (G.hessian 0 k x, G.hessian 1 k x)) =
        ((EuclideanSpace.single k 1, fderiv ℝ u x (EuclideanSpace.single k 1)),
          (suJetBlock k.succ (suFirstJetWeakColumn V G.hessian 0 x),
            suJetBlock k.succ (suFirstJetWeakColumn V G.hessian 1 x)))
      rw [suJetBlock_firstJetWeakColumn_succ, suJetBlock_firstJetWeakColumn_succ, hk, h0, h1]
    have hbase (x : LoopPlane) (hx : x ∈ ball center r) :
        (suAlphaFirstJetPoint (U x)).1 ∈ O := by
      change (x, suJetBlock (0 : Fin 3) (suFirstJet u x)) ∈ O
      rw [suJetBlock_firstJet_zero]
      exact hmap (ball_subset_closedBall (ball_subset_ball hrG.le hx))
    have hleft (i : Fin 2) : ∀ᵐ x ∂mu,
        C.prolong.flux (U x) (W 0 x, W 1 x)
          (suColumnBasis (finProdFinEquiv (k.succ, a)) i) = DF a k i x := by
      filter_upwards [hdir, ae_restrict_mem measurableSet_ball] with x hx hxr
      have hAc := (hA.contDiffAt (hO.mem_nhds (hbase x hxr))).differentiableAt (by simp)
      have hcc := (hc.contDiffAt (hO.mem_nhds (hbase x hxr))).differentiableAt (by simp)
      rw [C.prolong_flux_succ _ _ hAc hcc]
      dsimp only [DF, F]
      have hf : DifferentiableAt ℝ (fun p => C.flux p.1 p.2) (suAlphaFirstJetPoint (U x)) :=
        ((hAc.comp _ differentiableAt_fst).clm_apply differentiableAt_snd).add
          (hcc.comp _ differentiableAt_fst)
      rw [suFirstJet_scalar_fderiv hf, hx]
    have hright : ∀ᵐ x ∂mu,
        C.prolong.source (U x) (W 0 x, W 1 x)
          (EuclideanSpace.single (finProdFinEquiv (k.succ, a)) 1) = DB a k x := by
      filter_upwards [hdir, ae_restrict_mem measurableSet_ball] with x hx hxr
      have hBc := (hB.contDiffAt (hO.mem_nhds (hbase x hxr))).differentiableAt (by simp)
      have hdc := (hd.contDiffAt (hO.mem_nhds (hbase x hxr))).differentiableAt (by simp)
      rw [C.prolong_source_succ _ _ hBc hdc]
      dsimp only [DB, B]
      have hf : DifferentiableAt ℝ (fun p => C.source p.1 p.2) (suAlphaFirstJetPoint (U x)) :=
        ((hBc.comp _ differentiableAt_fst).clm_apply differentiableAt_snd).add
          (hdc.comp _ differentiableAt_fst)
      rw [suFirstJet_scalar_fderiv hf, hx]
    calc
      _ = ∫ x in ball center r, ∑ i : Fin 2,
          DF a k i x * fderiv ℝ phi x (EuclideanSpace.single i 1) := by
        apply integral_congr_ae
        filter_upwards [ae_all_iff.mpr hleft] with x hx
        dsimp only [U, J, W] at hx
        simp only [hx]
      _ = _ := suWeakDivergence_prolong k (hFint a) (hDFint a k)
          (fun i => ((hFd a i).2 k).2) ((hBd a).2 k).2 (heq a) hp hpc hps
      _ = _ := integral_congr_ae (hright.mono fun x hx => by rw [hx])




theorem suAffineWeakSystem_prolong_system {m : ℕ}
    {u : LoopPlane → EuclideanSpace ℝ (Fin m)}
    {V : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin m)} {center : LoopPlane} {R : ℝ}
    (S : SUQuadraticWeakSystem u V center R) (C : SUAffineJetCoefficients m)
    (hflux : S.flux = C.flux) (hsource : S.source = C.source)
    (G : SUInitialGain u V center R) (H : SUC1HolderGain u V center G.radius)
    {O : Set (LoopPlane × EuclideanSpace ℝ (Fin m))} (hO : IsOpen O)
    (hmap : MapsTo (fun x => (x, u x)) (closedBall center G.radius) O)
    (hA : ContDiffOn ℝ ∞ C.principal O) (hc : ContDiffOn ℝ ∞ C.fluxOffset O)
    (hB : ContDiffOn ℝ ∞ C.sourceLinear O) (hd : ContDiffOn ℝ ∞ C.sourceOffset O)
    {nu : ℝ} (hnu : 0 < nu)
    (hcoercive : ∀ z ∈ O, ∀ q, nu * ‖q‖ ^ 2 ≤ C.principal z q q) :
    ∃ r, 0 < r ∧ r < H.radius / 2 ∧
      MapsTo (fun x => (x, suFirstJet u x)) (closedBall center r)
        {z | (z.1, suJetBlock (0 : Fin 3) z.2) ∈ O} ∧
      ∃ T : SUQuadraticWeakSystem
          (suFirstJet u) (suFirstJetWeakColumn V G.hessian) center r,
        T.flux = C.prolong.flux ∧ T.source = C.prolong.source := by
  let J := suFirstJet u
  let W := suFirstJetWeakColumn V G.hessian
  let rho := H.radius / 2
  have hrho : 0 < rho := half_pos H.radius_pos
  obtain ⟨hJ, _, hW, hw⟩ := suFirstJet_weak_data G H
  let P := {z : LoopPlane × EuclideanSpace ℝ (Fin (3 * m)) |
    (z.1, suJetBlock (0 : Fin 3) z.2) ∈ O}
  have hP : IsOpen P := hO.preimage
    (continuous_fst.prodMk ((suJetBlock (0 : Fin 3)).continuous.comp continuous_snd))
  have hcenter : (center, J center) ∈ P := by
    change (center, suJetBlock (0 : Fin 3) (suFirstJet u center)) ∈ O
    rw [suJetBlock_firstJet_zero]
    exact hmap (mem_closedBall_self G.radius_pos.le)
  obtain ⟨d, hdpos, hball⟩ := Metric.isOpen_iff.mp hP (center, J center) hcenter
  let delta := d / 2
  have hdelta : 0 < delta := half_pos hdpos
  have hJat : ContinuousAt J center := hJ.continuousAt (closedBall_mem_nhds center hrho)
  obtain ⟨s, hs, hJs⟩ := Metric.continuousAt_iff.mp hJat (delta / 2) (half_pos hdelta)
  let r := min (rho / 2) (min (d / 2) (s / 2))
  have hr : 0 < r := lt_min (half_pos hrho) (lt_min (half_pos hdpos) (half_pos hs))
  have hrrho : r < rho := (min_le_left _ _).trans_lt (half_lt_self hrho)
  have hrd : r < d := ((min_le_right _ _).trans (min_le_left _ _)).trans_lt
    (half_lt_self hdpos)
  have hrs : r < s := ((min_le_right _ _).trans (min_le_right _ _)).trans_lt
    (half_lt_self hs)
  have hsubset : closedBall center r ×ˢ closedBall (J center) delta ⊆ P := by
    intro z hz
    apply hball
    rw [mem_ball, Prod.dist_eq, max_lt_iff]
    exact ⟨(mem_closedBall.mp hz.1).trans_lt hrd,
      (mem_closedBall.mp hz.2).trans_lt (half_lt_self hdpos)⟩
  have hrange : MapsTo J (closedBall center r) (ball (J center) (delta / 2)) := by
    intro x hx
    exact mem_ball.mpr (hJs ((mem_closedBall.mp hx).trans_lt hrs))
  have hJmap : MapsTo (fun x => (x, J x)) (closedBall center r) P := by
    intro x hx
    exact hsubset ⟨hx, mem_closedBall.mpr ((mem_ball.mp (hrange hx)).le.trans
      (half_le_self hdelta.le))⟩
  have hcols (i : Fin 2) : MemLp (W i) 2 (volume.restrict (ball center r)) :=
    (hW i).mono_measure (Measure.restrict_mono (ball_subset_ball hrrho.le) le_rfl)
  have hweak (i : Fin 2) (a : Fin (3 * m)) :
      HasWeakPartialDeriv i (fun x => W i x a) (fun x => J x a) (ball center r) :=
    (hw i a).restrict isOpen_ball (ball_subset_ball hrrho.le)
  have hsm := C.prolong_smooth hO hA hc hB hd
  obtain ⟨T, htF, htB⟩ := suAffineQuadraticSystem C.prolong hr hdelta hnu
    (hJ.mono (closedBall_subset_closedBall hrrho.le)) hcols hweak hrange
    (fun z hz => (hsm.1.contDiffAt (hP.mem_nhds (hsubset hz))).of_le (by simp))
    (fun z hz => (hsm.2.1.contDiffAt (hP.mem_nhds (hsubset hz))).of_le (by simp))
    (fun z hz => (hsm.2.2.1.contDiffAt (hP.mem_nhds (hsubset hz))).of_le (by simp))
    (fun z hz => (hsm.2.2.2.contDiffAt (hP.mem_nhds (hsubset hz))).of_le (by simp))
    (fun z hz q => C.prolong_coercive z hnu.le (hcoercive _ (hsubset hz)) q)
    (fun a phi hp hpc hps => suAffineWeakSystem_prolong_equation S C hflux hsource G H
      hO hmap (hA.of_le (by simp)) (hc.of_le (by simp)) (hB.of_le (by simp))
      (hd.of_le (by simp)) hr hrrho a hp hpc hps)
  exact ⟨r, hr, hrrho, hJmap, T, htF, htB⟩



theorem suContDiffAt_succ_of_firstJet {m k : ℕ}
    {u : LoopPlane → EuclideanSpace ℝ (Fin m)} {center : LoopPlane} {r : ℝ}
    (hr : 0 < r) (hu : ContDiffOn ℝ 1 u (ball center r))
    (hJ : ContDiffAt ℝ k (suFirstJet u) center) : ContDiffAt ℝ (k + 1) u center := by
  let A (z : EuclideanSpace ℝ (Fin (3 * m))) : LoopPlane →L[ℝ] EuclideanSpace ℝ (Fin m) :=
    ∑ i : Fin 2, (EuclideanSpace.proj i).smulRight (suJetBlock i.succ z)
  have hA : ContDiff ℝ ∞ A := by
    apply contDiff_clm_apply_iff.mpr
    intro v
    change ContDiff ℝ ∞ (fun z => ∑ i : Fin 2, v i • suJetBlock i.succ z)
    apply ContDiff.sum
    intro i _
    exact (suJetBlock (m := m) i.succ).contDiff.const_smul (v i)
  have he : fderiv ℝ u = A ∘ suFirstJet u := by
    funext x
    apply ContinuousLinearMap.ext
    intro v
    change fderiv ℝ u x v = ∑ i : Fin 2, v i • suJetBlock i.succ (suFirstJet u x)
    simp_rw [suJetBlock_firstJet_succ, ← map_smul]
    rw [← map_sum]
    congr 1
    simpa only [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr] using
      ((EuclideanSpace.basisFun (Fin 2) ℝ).sum_repr v).symm
  apply contDiffAt_succ_iff_hasFDerivAt.mpr
  refine ⟨fderiv ℝ u, ⟨ball center r, ball_mem_nhds center hr, ?_⟩, ?_⟩
  · intro x hx
    exact ((hu.contDiffAt (isOpen_ball.mem_nhds hx)).differentiableAt (by norm_num)).hasFDerivAt
  · rw [he]
    exact (hA.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt.comp center hJ





theorem suAffineWeakSystem_contDiff_finite :
    ∃ delta : ℝ, 0 < delta ∧ ∀ (k m : ℕ)
      {u : LoopPlane → EuclideanSpace ℝ (Fin m)}
      {V : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin m)} {center : LoopPlane} {R : ℝ}
      (S : SUQuadraticWeakSystem u V center R) (C : SUAffineJetCoefficients m),
      S.flux = C.flux → S.source = C.source →
      ∀ {O : Set (LoopPlane × EuclideanSpace ℝ (Fin m))}, IsOpen O →
      MapsTo (fun x => (x, u x)) (closedBall center R) O →
      ContDiffOn ℝ ∞ C.principal O → ContDiffOn ℝ ∞ C.fluxOffset O →
      ContDiffOn ℝ ∞ C.sourceLinear O → ContDiffOn ℝ ∞ C.sourceOffset O →
      ∀ {nu : ℝ}, 0 < nu →
      (∀ z ∈ O, ∀ q, nu * ‖q‖ ^ 2 ≤ C.principal z q q) →
      SUAffineJetNormalization C O delta → ContDiffAt ℝ k u center := by
  obtain ⟨delta, hdelta, hholder⟩ := suAffineQuadraticSystem_holder
  refine ⟨delta, hdelta, ?_⟩
  intro k
  induction k with
  | zero =>
    intro m u V center R S C _ _ O _ _ _ _ _ _ nu _ _ _
    exact contDiffAt_zero.mpr ⟨closedBall center R,
      closedBall_mem_nhds center S.radius_pos, S.coordinate_continuous⟩
  | succ k ih =>
    intro m u V center R S C hflux hsource O hO hmap hA hc hB hd nu hnu hcoercive N
    obtain ⟨G⟩ := suQuadraticWeakSystem_initial_gain S
    have hmapG : MapsTo (fun x => (x, u x)) (closedBall center G.radius) O :=
      hmap.mono_left (closedBall_subset_closedBall G.radius_lt.le)
    obtain ⟨H⟩ := hholder m S C hflux hsource G hO hmapG (hA.of_le (by simp))
      (hc.of_le (by simp)) hB.continuousOn hd.continuousOn N
    obtain ⟨r, _, _, hmapJ, T, htF, htB⟩ := suAffineWeakSystem_prolong_system
      S C hflux hsource G H hO hmapG hA hc hB hd hnu hcoercive
    let P := {z : LoopPlane × EuclideanSpace ℝ (Fin (3 * m)) |
      (z.1, suJetBlock (0 : Fin 3) z.2) ∈ O}
    have hP : IsOpen P := hO.preimage
      (continuous_fst.prodMk ((suJetBlock (0 : Fin 3)).continuous.comp continuous_snd))
    have hsm := C.prolong_smooth hO hA hc hB hd
    have hJ := ih (3 * m) T C.prolong htF htB hP hmapJ
      hsm.1 hsm.2.1 hsm.2.2.1 hsm.2.2.2 hnu
      (fun z hz q => C.prolong_coercive z hnu.le (hcoercive _ hz) q) (N.prolong hdelta.le)
    exact suContDiffAt_succ_of_firstJet H.radius_pos H.coordinate_contDiff hJ

end PoincareConjecture.M60
