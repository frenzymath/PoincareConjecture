import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundarySourceRescaling
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusWeakMinimizerInteriorSmooth












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Metric Topology
open scoped Manifold ContDiff

namespace PoincareConjecture

open Poincare.Analysis.Sobolev.Weak

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {e : M → EuclideanSpace ℝ (Fin m)} {c0 c1 : ℝ → M}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "S" => interior m64AnnulusDomain




theorem m64SourceScale_alphaOne_variation
    (g : RiemannianMetric n M) (b : M) (s : ℝ) (hs : s ≠ 0)
    (u : LoopPlane → E) (W : Fin 2 → LoopPlane → E)
    (phi : LoopPlane → E) (hp : ContDiff ℝ ∞ phi) (p : LoopPlane) :
    let D := m64SourceScale s hs
    let G := g.pullbackCoefficients (extChartAt (𝓡 n) b).symm
    let psi := phi ∘ D.symm
    M60.suAlphaChartVariation g b 1 (u ∘ D)
      (fun i z => m64SourceScaleFactor s i • W i (D z)) phi p =
      s ^ 2 * (fderiv ℝ G (u (D p)) (psi (D p)) (W 0 (D p)) (W 0 (D p)) +
          2 * G (u (D p)) (W 0 (D p)) (fderiv ℝ psi (D p) (EuclideanSpace.single 0 1))) +
      (s ^ 2)⁻¹ * (fderiv ℝ G (u (D p)) (psi (D p)) (W 1 (D p)) (W 1 (D p)) +
          2 * G (u (D p)) (W 1 (D p)) (fderiv ℝ psi (D p) (EuclideanSpace.single 1 1))) := by
  let D := m64SourceScale s hs
  let psi := phi ∘ D.symm
  have hpsi : ContDiff ℝ ∞ psi := hp.comp D.symm.contDiff
  have hcomp : psi ∘ D = phi := by funext z; simp [psi]
  have hd (i : Fin 2) : fderiv ℝ phi p (EuclideanSpace.single i 1) =
      m64SourceScaleFactor s i •
        fderiv ℝ psi (D p) (EuclideanSpace.single i 1) := by
    have h := m64SourceScale_fderiv_comp s hs (hpsi.differentiable (by simp)) p i
    rw [hcomp] at h
    exact h
  have hpD : psi (D p) = phi p := congrFun hcomp p
  dsimp only
  simp only [M60.suAlphaChartVariation, sub_self, Real.rpow_zero, one_mul,
    Fin.sum_univ_two, Function.comp_apply]
  change _ = s ^ 2 * (_ + 2 * _) + (s ^ 2)⁻¹ * (_ + 2 * _)
  rw [← hpD, hd 0, hd 1]
  simp only [m64SourceScaleFactor, show (1 : Fin 2) ≠ 0 from by decide,
    ↓reduceIte, map_smul, smul_apply, smul_eq_mul]
  dsimp only [psi, D]
  simp only [extChartAt_coe_symm, modelWithCornersSelf_coe_symm, Function.comp_id,
    Function.comp_apply]
  ring

set_option maxHeartbeats 1600000 in



theorem M64ObservedWeakAnnulus.weighted_coordinates_rescaled_critical
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (g : RiemannianMetric n M) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (hei : IsEmbedding e)
    (Q : M → EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ)
    (hQ : Continuous Q) {C : ℝ} (hb : ∀ q, ‖Q q‖ ≤ C)
    (hdiag : ∀ (q : M) (v : TangentSpace (𝓡 n) q),
      Q q (mfderiv (𝓡 n) (𝓡 m) e q v) (mfderiv (𝓡 n) (𝓡 m) e q v) =
        g.inner q v v)
    {modulus : ℝ} (hmodulus : 0 < modulus)
    (hmin : ∀ B : M64ObservedWeakAnnulus (n := n) e c0 c1,
      A.weightedEnergy Q modulus ≤ B.weightedEnergy Q modulus)
    (b : M) {u : LoopPlane → E} {W : Fin 2 → LoopPlane → E}
    {a : LoopPlane} {R : ℝ} (hR : 0 < R) (hRS : closedBall a R ⊆ S)
    (hu : Continuous u)
    (huT : MapsTo u (closedBall a R) (extChartAt (𝓡 n) b).target)
    (hW : ∀ i, MemLp (W i) 2 (volume.restrict (ball a R)))
    (hw : ∀ i j, HasWeakPartialDeriv i (fun p => W i p j) (fun p => u p j) (ball a R))
    (hmap : EqOn ((extChartAt (𝓡 n) b).symm ∘ u) A.map (closedBall a R)) :
    let s := Real.sqrt modulus
    let D := m64SourceScale s (Real.sqrt_pos.mpr hmodulus).ne'
    ∃ radius : ℝ, M60.SUWeakAlphaCoordinate g b 1 (u ∘ D)
      (fun i p => m64SourceScaleFactor s i • W i (D p)) (D.symm a) radius := by
  let s := Real.sqrt modulus
  have hs : s ≠ 0 := (Real.sqrt_pos.mpr hmodulus).ne'
  have hs2 : s ^ 2 = modulus := Real.sq_sqrt hmodulus.le
  let D := m64SourceScale s hs
  let a' := D.symm a
  let small := (R / 4) * Real.exp (-1)
  have hsmall : 0 < small := mul_pos (div_pos hR (by norm_num)) (Real.exp_pos _)
  have hsmallR : small < R / 2 := by
    have hh := mul_lt_of_lt_one_right (div_pos hR (by norm_num : (0 : ℝ) < 4))
      (Real.exp_lt_one_iff.mpr (by norm_num : (-1 : ℝ) < 0))
    dsimp only [small]
    linarith
  have hopen : IsOpen (D ⁻¹' ball a small) := isOpen_ball.preimage D.continuous
  have ha' : a' ∈ D ⁻¹' ball a small := by
    change D (D.symm a) ∈ ball a small
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using
      (mem_ball_self hsmall : a ∈ ball a small)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen a' ha'
  let radius := r / 2
  have hradius : 0 < radius := half_pos hr
  have hclosed : closedBall a' radius ⊆ D ⁻¹' ball a small :=
    (closedBall_subset_ball (half_lt_self hr)).trans hball
  have hsource : closedBall a' radius ⊆ D ⁻¹' ball a R := by
    intro p hp
    change D p ∈ ball a R
    exact (ball_subset_ball (hsmallR.trans (half_lt_self hR)).le :
      ball a small ⊆ ball a R) (hclosed hp)
  have hsourceHalf : ball a' radius ⊆ D ⁻¹' ball a (R / 2) := by
    intro p hp
    change D p ∈ ball a (R / 2)
    exact (ball_subset_ball hsmallR.le : ball a small ⊆ ball a (R / 2))
      (hclosed (ball_subset_closedBall hp))
  let v := u ∘ D
  let V := fun i p => m64SourceScaleFactor s i • W i (D p)
  have hv : Continuous v := hu.comp D.continuous
  have hV (i : Fin 2) : MemLp (V i) 2 (volume.restrict (ball a' radius)) :=
    (((hW i).comp_measurePreserving (m64SourceScale_restrict_measurePreserving s hs
      (ball a R))).const_smul (m64SourceScaleFactor s i)).mono_measure
        (Measure.restrict_mono (ball_subset_closedBall.trans hsource) le_rfl)
  have hweak (i : Fin 2) (j : Fin n) :
      HasWeakPartialDeriv i (fun p => V i p j) (fun p => v p j) (ball a' radius) := by
    have h := (m64SourceScale_weakPartial (hw i j) s hs).restrict isOpen_ball
      (ball_subset_closedBall.trans hsource)
    exact h
  have htest (phi : LoopPlane → E) (hp : ContDiff ℝ ∞ phi)
      (hps : tsupport phi ⊆ ball a' radius) :
      IntegrableOn (M60.suAlphaChartVariation g b 1 v V phi) (ball a' radius) ∧
        (∫ p in ball a' radius, M60.suAlphaChartVariation g b 1 v V phi p) = 0 := by
    let psi := phi ∘ D.symm
    have hpsi : ContDiff ℝ ∞ psi := hp.comp D.symm.contDiff
    have hpsis : tsupport psi ⊆ ball a small := by
      change tsupport (phi ∘ D.toHomeomorph.symm) ⊆ ball a small
      rw [tsupport_comp_eq_preimage]
      intro p hp'
      have hm := hclosed (ball_subset_closedBall (hps hp'))
      change D (D.symm p) ∈ ball a small at hm
      simpa only [ContinuousLinearEquiv.apply_symm_apply] using hm
    let G := g.pullbackCoefficients (extChartAt (𝓡 n) b).symm
    let rate := fun p =>
      (modulus * (fderiv ℝ G (u p) (psi p) (W 0 p) (W 0 p) +
          2 * G (u p) (W 0 p) (fderiv ℝ psi p (EuclideanSpace.single 0 1))) +
        modulus⁻¹ * (fderiv ℝ G (u p) (psi p) (W 1 p) (W 1 p) +
          2 * G (u p) (W 1 p) (fderiv ℝ psi p (EuclideanSpace.single 1 1)))) / 2
    obtain ⟨hint, hzero⟩ := A.weighted_interior_coordinate_variation_eq_zero g he hei
      Q hQ hb hdiag modulus hmin b hR hRS hu huT hW hw hmap psi hpsi hpsis
    change IntegrableOn rate (ball a (R / 2)) at hint
    change (∫ p in ball a (R / 2), rate p) = 0 at hzero
    have heq (p : LoopPlane) : M60.suAlphaChartVariation g b 1 v V phi p =
        2 * rate (D p) := by
      have h := m64SourceScale_alphaOne_variation g b s hs u W phi hp p
      dsimp only at h
      rw [hs2] at h
      rw [h]
      dsimp only [rate, G, psi, D]
      ring
    have hint' : IntegrableOn (M60.suAlphaChartVariation g b 1 v V phi)
        (D ⁻¹' ball a (R / 2)) := by
      have hmp := m64SourceScale_restrict_measurePreserving s hs (ball a (R / 2))
      apply (hmp.integrable_comp_of_integrable (hint.const_mul 2)).congr
      exact Eventually.of_forall fun p => (heq p).symm
    have hzero' : (∫ p in D ⁻¹' ball a (R / 2),
        M60.suAlphaChartVariation g b 1 v V phi p) = 0 := by
      simp_rw [heq]
      rw [m64SourceScale_integral s hs (ball a (R / 2)) (fun p => 2 * rate p),
        integral_const_mul, hzero, mul_zero]
    refine ⟨hint'.mono_set hsourceHalf, ?_⟩
    rw [← hzero']
    symm
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      (isOpen_ball.preimage D.continuous).measurableSet hsourceHalf
    intro p hp'
    have hnot : p ∉ tsupport phi := fun ht => hp'.2 (hps ht)
    simp only [M60.suAlphaChartVariation, image_eq_zero_of_notMem_tsupport hnot,
      fderiv_of_notMem_tsupport ℝ hnot, map_zero, zero_apply, mul_zero,
      Finset.sum_const_zero, add_zero]
  have hcritical : M60.SUWeakAlphaCoordinate g b 1 v V a' radius := by
    refine ⟨hradius, ?_, hv.continuousOn, ?_, ?_, hweak, ?_, ?_⟩
    · intro p hp
      exact huT (ball_subset_closedBall (hsource hp))
    · simpa using m64MemLp_on_ball_of_continuous_closedBall hv.continuousOn 2
        (a := a') (R := radius)
    · intro i; simpa using hV i
    · intro phi hp _ hps; exact (htest phi hp hps).1
    · intro phi hp _ hps; exact (htest phi hp hps).2
  exact ⟨radius, hcritical⟩



theorem M64ObservedWeakAnnulus.weighted_coordinates_contDiffAt
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (g : RiemannianMetric n M) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (hei : IsEmbedding e)
    (Q : M → EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ)
    (hQ : Continuous Q) {C : ℝ} (hb : ∀ q, ‖Q q‖ ≤ C)
    (hdiag : ∀ (q : M) (v : TangentSpace (𝓡 n) q),
      Q q (mfderiv (𝓡 n) (𝓡 m) e q v) (mfderiv (𝓡 n) (𝓡 m) e q v) =
        g.inner q v v)
    {modulus : ℝ} (hmodulus : 0 < modulus)
    (hmin : ∀ B : M64ObservedWeakAnnulus (n := n) e c0 c1,
      A.weightedEnergy Q modulus ≤ B.weightedEnergy Q modulus)
    (b : M) {u : LoopPlane → E} {W : Fin 2 → LoopPlane → E}
    {a : LoopPlane} {R : ℝ} (hR : 0 < R) (hRS : closedBall a R ⊆ S)
    (hu : Continuous u)
    (huT : MapsTo u (closedBall a R) (extChartAt (𝓡 n) b).target)
    (hW : ∀ i, MemLp (W i) 2 (volume.restrict (ball a R)))
    (hw : ∀ i j, HasWeakPartialDeriv i (fun p => W i p j) (fun p => u p j) (ball a R))
    (hmap : EqOn ((extChartAt (𝓡 n) b).symm ∘ u) A.map (closedBall a R)) :
    ContDiffAt ℝ ∞ u a := by
  let s := Real.sqrt modulus
  let D := m64SourceScale s (Real.sqrt_pos.mpr hmodulus).ne'
  obtain ⟨radius, hcritical⟩ := A.weighted_coordinates_rescaled_critical g he hei
    Q hQ hb hdiag hmodulus hmin b hR hRS hu huT hW hw hmap
  have hsm := M60.suWeakAlphaCoordinate_smooth_alpha_one g b (u ∘ D)
    (fun i p => m64SourceScaleFactor s i • W i (D p)) (D.symm a) radius hcritical
  have hcomp : (u ∘ D) ∘ D.symm = u := by funext p; simp
  have hsm' := hsm.comp a D.symm.contDiff.contDiffAt
  rwa [hcomp] at hsm'




theorem M64ObservedWeakAnnulus.contMDiffOn_of_weightedEnergy_minimum
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (g : RiemannianMetric n M) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (hei : IsEmbedding e) (hread : M60.SUChartReadable (n := n) e)
    (Q : M → EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ)
    (hQ : Continuous Q) {C : ℝ} (hb : ∀ q, ‖Q q‖ ≤ C)
    (hdiag : ∀ (q : M) (v : TangentSpace (𝓡 n) q),
      Q q (mfderiv (𝓡 n) (𝓡 m) e q v) (mfderiv (𝓡 n) (𝓡 m) e q v) =
        g.inner q v v)
    {modulus : ℝ} (hmodulus : 0 < modulus)
    (hmin : ∀ B : M64ObservedWeakAnnulus (n := n) e c0 c1,
      A.weightedEnergy Q modulus ≤ B.weightedEnergy Q modulus)
    (hA : ContinuousOn A.map S) : ContMDiffOn (𝓡 2) (𝓡 n) ∞ A.map S := by
  intro a ha
  obtain ⟨b, L, R, hR, hRS, hchart, hu0, -, hW, hw⟩ :=
    A.exists_local_chart_columns he.continuous hread hA ha
  obtain ⟨u, hu, heq⟩ := m64_exists_continuous_extension isClosed_closedBall hu0
  have hcoord (p : LoopPlane) (hp : p ∈ closedBall a R) :
      u p = extChartAt (𝓡 n) b (A.map p) := (heq hp).trans (hchart p hp).2
  have huT : MapsTo u (closedBall a R) (extChartAt (𝓡 n) b).target := by
    intro p hp
    rw [hcoord p hp]
    exact (extChartAt (𝓡 n) b).map_source (hchart p hp).1
  have hmap : EqOn ((extChartAt (𝓡 n) b).symm ∘ u) A.map (closedBall a R) := by
    intro p hp
    change (extChartAt (𝓡 n) b).symm (u p) = A.map p
    rw [hcoord p hp, (extChartAt (𝓡 n) b).left_inv (hchart p hp).1]
  have hwu (i : Fin 2) (j : Fin n) : HasWeakPartialDeriv i
      (fun p => L (A.column i p) j) (fun p => u p j) (ball a R) := by
    apply m64WeakPartialDeriv_ae_congr ?_ (Eventually.of_forall fun _ => rfl) (hw i j)
    filter_upwards [ae_restrict_mem isOpen_ball.measurableSet] with p hp
    exact congrArg (fun v : E => v j) (heq (ball_subset_closedBall hp)).symm
  have hsm := A.weighted_coordinates_contDiffAt g he hei Q hQ hb hdiag hmodulus hmin
    b hR hRS hu huT hW hwu hmap
  have haR : a ∈ closedBall a R := mem_closedBall_self hR.le
  have hi := (contMDiffOn_extChartAt_symm (n := ∞) b _ (huT haR)).contMDiffAt
    ((isOpen_extChartAt_target b).mem_nhds (huT haR))
  have hlocal : ContMDiffAt (𝓡 2) (𝓡 n) ∞ A.map a := by
    apply (hi.comp a (contMDiffAt_iff_contDiffAt.mpr hsm)).congr_of_eventuallyEq
    filter_upwards [closedBall_mem_nhds a hR] with p hp
    exact (hmap hp).symm
  exact hlocal.contMDiffWithinAt

end PoincareConjecture
