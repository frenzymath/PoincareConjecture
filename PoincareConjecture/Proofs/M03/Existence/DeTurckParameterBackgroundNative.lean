import PoincareConjecture.Proofs.M03.Existence.DeTurckCompletedOutputNative
import PoincareConjecture.Proofs.M03.Existence.DeTurckJetAffineNative
import PoincareConjecture.Proofs.M03.Existence.DeTurckPullbackSourceNative
import PoincareConjecture.Proofs.M03.Existence.ContinuousPathCompositionNative

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.DeTurckParameterBackgroundNative

open ContinuousPathCompositionNative TensorProbeNative TensorHilbertNative ParsevalTensorNative
  DeTurckJetAffineNative DeTurckJetCoordinatesNative DeTurckCompletedOutputNative
  DeTurckPullbackSourceNative SpectralHeatNative

universe u v

section CompactCurrying

variable {P F : Type v} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {K : Type u} [TopologicalSpace K] [CompactSpace K]

set_option synthInstance.maxHeartbeats 100000 in

theorem hasFDerivAt_compact_curry {U : Set P} (hU : IsOpen U)
    (f : P → C(K, F)) (A : P → C(K, P →L[ℝ] F)) {p : P} (hp : p ∈ U)
    (hA : ContinuousAt A p)
    (hder : ∀ q ∈ U, ∀ x : K, HasFDerivAt (fun a => f a x) (A q x) q) :
    HasFDerivAt f
      ((pointwiseOperator K (A p)).comp (ContinuousLinearMap.const ℝ K)) p := by
  rw [hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro eps heps
  obtain ⟨r, hr, hclose⟩ := (Metric.continuousAt_iff (f := A) (a := p)).mp hA eps heps
  obtain ⟨s, hs, hsU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hp)
  let d : ℝ := min r s
  have hd : 0 < d := lt_min hr hs
  have hdU : ball p d ⊆ U := fun q hq =>
    hsU ((ball_subset_ball (min_le_right r s)) hq)
  filter_upwards [ball_mem_nhds p hd] with q hq
  apply (ContinuousMap.norm_le _ (mul_nonneg heps.le (norm_nonneg _))).mpr
  intro x
  have hbound : ∀ a ∈ ball p d, ‖A a x - A p x‖ ≤ eps := by
    intro a ha
    have haa : dist a p < r := (mem_ball.mp ha).trans_le (min_le_left r s)
    have hnorm : ‖A a - A p‖ < eps := by
      have hdist := hclose haa
      rw [dist_eq_norm (A a) (A p)] at hdist
      exact hdist
    exact ((A a - A p).norm_coe_le_norm x).trans hnorm.le
  have hrem := (convex_ball p d).norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (f := fun a => f a x) (f' := fun a => A a x) (φ := A p x)
    (fun a ha => (hder a (hdU ha) x).hasFDerivWithinAt)
    hbound (mem_ball_self hd) hq
  change ‖f q x - f p x - A p x (q - p)‖ ≤ eps * ‖q - p‖
  exact hrem

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "I" => 𝓡 n

theorem contMDiffOn_parameter_fderiv {U : Set P} (hU : IsOpen U)
    (f : P × M → F) (k : ℕ)
    (hf : ContMDiffOn (𝓘(ℝ, P).prod I) 𝓘(ℝ, F) (k + 1) f (U ×ˢ univ)) :
    ContMDiffOn (𝓘(ℝ, P).prod I) 𝓘(ℝ, P →L[ℝ] F) k
      (fun q => fderiv ℝ (fun a => f (a, q.2)) q.1) (U ×ˢ univ) := by
  intro q hq
  have hfa := hf.contMDiffAt ((hU.prod isOpen_univ).mem_nhds hq)
  have hcomp : ContMDiffAt ((𝓘(ℝ, P).prod I).prod 𝓘(ℝ, P)) 𝓘(ℝ, F)
      (k + 1) (fun z : (P × M) × P => f (z.2, z.1.2)) (q, q.1) :=
    hfa.comp (q, q.1) (contMDiffAt_snd.prodMk contMDiffAt_fst.snd)
  have hd := hcomp.mfderiv (fun z : P × M => fun a : P => f (a, z.2))
    Prod.fst (contMDiffAt_fst (n := (k : WithTop ℕ∞))) (by simp)
  simpa only [inTangentCoordinates_model_space, mfderiv_eq_fderiv] using
    hd.contMDiffWithinAt

set_option synthInstance.maxHeartbeats 100000 in
theorem contDiffOn_compact_curry_nat {U : Set P} (hU : IsOpen U)
    (k : ℕ) (f : P × M → F)
    (hf : ContMDiffOn (𝓘(ℝ, P).prod I) 𝓘(ℝ, F) k f (U ×ˢ univ)) :
    ContDiffOn ℝ k (fun p => ContinuousMap.mkD (fun x => f (p, x)) 0) U := by
  induction k generalizing F with
  | zero =>
    exact contDiffOn_zero.mpr (ContinuousMap.continuousOn_mkD_of_uncurry
      (fun p x => f (p, x)) 0 hf.continuousOn)
  | succ k ih =>
    let D : P × M → P →L[ℝ] F := fun q => fderiv ℝ (fun a => f (a, q.2)) q.1
    let A : P → C(M, P →L[ℝ] F) := fun p =>
      ContinuousMap.mkD (fun x => D (p, x)) 0
    let fbar : P → C(M, F) := fun p => ContinuousMap.mkD (fun x => f (p, x)) 0
    have hD : ContMDiffOn (𝓘(ℝ, P).prod I) 𝓘(ℝ, P →L[ℝ] F) k
        D (U ×ˢ univ) := contMDiffOn_parameter_fderiv hU f k hf
    have hA : ContDiffOn ℝ k A U := ih D hD
    have hf_slice (p : P) (hp : p ∈ U) : Continuous (fun x => f (p, x)) :=
      hf.continuousOn.comp_continuous (continuous_const.prodMk continuous_id)
        (fun x => ⟨hp, mem_univ x⟩)
    have hD_slice (p : P) (hp : p ∈ U) : Continuous (fun x => D (p, x)) :=
      hD.continuousOn.comp_continuous (continuous_const.prodMk continuous_id)
        (fun x => ⟨hp, mem_univ x⟩)
    have hder (p : P) (hp : p ∈ U) (x : M) :
        HasFDerivAt (fun a => fbar a x) (A p x) p := by
      have hfa := hf.contMDiffAt
        ((hU.prod isOpen_univ).mem_nhds (show (p, x) ∈ U ×ˢ univ from ⟨hp, mem_univ x⟩))
      have hsmooth : ContDiffAt ℝ (k + 1) (fun a => f (a, x)) p :=
        (hfa.comp p (contMDiffAt_id.prodMk contMDiffAt_const)).contDiffAt
      have heq : (fun a => fbar a x) =ᶠ[𝓝 p] (fun a => f (a, x)) := by
        filter_upwards [hU.mem_nhds hp] with a ha
        exact ContinuousMap.mkD_apply_of_continuous (hf_slice a ha)
      have hd := (hsmooth.differentiableAt (by simp)).hasFDerivAt
      have hAp : A p x = fderiv ℝ (fun a => f (a, x)) p :=
        ContinuousMap.mkD_apply_of_continuous (hD_slice p hp)
      rw [hAp]
      exact hd.congr_of_eventuallyEq heq
    rw [show (↑(k + 1) : WithTop ℕ∞) = (k : WithTop ℕ∞) + 1 by simp]
    apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hU.uniqueDiffOn).mpr
    refine ⟨by simp, fun p =>
      (pointwiseOperator M (A p)).comp (ContinuousLinearMap.const ℝ M), ?_, ?_⟩
    · have hpoint : ContDiffOn ℝ k
          (fun p => (pointwiseOperator M (A p) : C(M, P) →L[ℝ] C(M, F))) U := by
        simpa only [Function.comp_def, pointwiseOperatorCLM_apply] using
          (pointwiseOperatorCLM M :
            C(M, P →L[ℝ] F) →L[ℝ] (C(M, P) →L[ℝ] C(M, F))).contDiff.comp_contDiffOn hA
      exact hpoint.clm_comp (show ContDiffOn ℝ k
        (fun _ : P => (ContinuousLinearMap.const ℝ M : P →L[ℝ] C(M, P))) U from
          contDiffOn_const)
    · intro p hp
      exact (hasFDerivAt_compact_curry hU fbar A hp
        ((hA.continuousOn p hp).continuousAt (hU.mem_nhds hp)) hder).hasFDerivWithinAt

theorem contDiffOn_compact_curry {U : Set P} (hU : IsOpen U)
    (f : P × M → F)
    (hf : ContMDiffOn (𝓘(ℝ, P).prod I) 𝓘(ℝ, F) ∞ f (U ×ˢ univ)) :
    ContDiffOn ℝ ∞ (fun p => ContinuousMap.mkD (fun x => f (p, x)) 0) U := by
  apply contDiffOn_infty.mpr
  intro k
  exact contDiffOn_compact_curry_nat (n := n) hU k f
    (hf.of_le (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤)))

end CompactCurrying

section JointPullback

variable {P : Type v} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "I" => 𝓡 n

theorem contMDiffOn_parameter_pushforward {U : Set P}
    (Phi : P → Diffeomorph I I M M ∞)
    (hPhi : ContMDiffOn (𝓘(ℝ, P).prod I) I ∞
      (fun q : P × M => Phi q.1 q.2) (U ×ˢ univ))
    (X : SmoothField (n := n) (M := M)) :
    ContMDiffOn (𝓘(ℝ, P).prod I) ((𝓡 n).prod 𝓘(ℝ, E)) ∞
      (fun q : P × M => (⟨Phi q.1 q.2,
        mfderiv I I (Phi q.1) q.2 (X q.2)⟩ : TangentBundle I M))
      (U ×ˢ univ) := by
  intro q hq
  have hf : ContMDiffWithinAt ((𝓘(ℝ, P).prod I).prod I) I ∞
      (fun z : (P × M) × M => Phi z.1.1 z.2)
      ((U ×ˢ univ) ×ˢ univ) (q, q.2) :=
    (hPhi q hq).comp (q, q.2)
      (f := fun z : (P × M) × M => (z.1.1, z.2))
      (contMDiffWithinAt_fst.fst.prodMk contMDiffWithinAt_snd)
      (fun (z : (P × M) × M) (hz : z ∈ (U ×ˢ univ) ×ˢ univ) => ⟨hz.1.1, hz.2⟩)
  have hd := ContMDiffWithinAt.mfderivWithin
    (n := ∞) (m := ∞) (f := fun z : P × M => (Phi z.1 : M → M))
    (g := Prod.snd) hf contMDiffWithinAt_snd hq
    (fun _ _ => mem_univ _) (by simp) uniqueMDiffOn_univ
  have hsnd : ContMDiff (𝓘(ℝ, P).prod (𝓡 n)) (𝓡 n) ∞
      (Prod.snd : P × M → M) := contMDiff_snd
  have hfield : ContMDiffWithinAt (𝓘(ℝ, P).prod I) ((𝓡 n).prod 𝓘(ℝ, E)) ∞
      (fun z : P × M => (⟨z.2, X z.2⟩ : TangentBundle I M)) (U ×ˢ univ) q :=
    ((X.contMDiff.comp hsnd) q).contMDiffWithinAt
  have happ := ContMDiffWithinAt.clm_apply_of_inCoordinates
    (IB₁ := I) (IB₂ := I) (IM := 𝓘(ℝ, P).prod I)
    (b₁ := Prod.snd) (b₂ := fun z : P × M => Phi z.1 z.2) hd hfield (hPhi q hq)
  simpa only [mfderivWithin_univ] using happ

theorem contMDiffOn_parameter_pullback_pair {U : Set P}
    (g0 : RiemannianMetric n M) (Phi : P → Diffeomorph I I M M ∞)
    (hPhi : ContMDiffOn (𝓘(ℝ, P).prod I) I ∞
      (fun q : P × M => Phi q.1 q.2) (U ×ˢ univ))
    (X Y : SmoothField (n := n) (M := M)) :
    ContMDiffOn (𝓘(ℝ, P).prod I) 𝓘(ℝ, ℝ) ∞
      (fun q : P × M => g0.inner (Phi q.1 q.2)
        (mfderiv I I (Phi q.1) q.2 (X q.2))
        (mfderiv I I (Phi q.1) q.2 (Y q.2))) (U ×ˢ univ) := by
  have hmetric := g0.contMDiff.comp_contMDiffOn hPhi
  have hpair := ContMDiffOn.clm_bundle_apply₂
    (F₁ := E) (F₂ := E) (F₃ := ℝ)
    (E₁ := TangentSpace I) (E₂ := TangentSpace I) (E₃ := fun _ : M => ℝ)
    (b := fun q : P × M => Phi q.1 q.2)
    (ψ := fun q => g0.inner (Phi q.1 q.2)) hmetric
    (contMDiffOn_parameter_pushforward Phi hPhi X)
    (contMDiffOn_parameter_pushforward Phi hPhi Y)
  intro q hq
  exact (Bundle.contMDiffWithinAt_totalSpace.mp (hpair q hq)).2

theorem contMDiffOn_parameter_directional {U : Set P}
    (f : P × M → ℝ)
    (hf : ContMDiffOn (𝓘(ℝ, P).prod I) 𝓘(ℝ, ℝ) ∞ f (U ×ˢ univ))
    (X : SmoothField (n := n) (M := M)) :
    ContMDiffOn (𝓘(ℝ, P).prod I) 𝓘(ℝ, ℝ) ∞
      (fun q : P × M => scalarDirectional X (fun x => f (q.1, x)) q.2)
      (U ×ˢ univ) := by
  intro q hq
  have hcomp : ContMDiffWithinAt ((𝓘(ℝ, P).prod I).prod I) 𝓘(ℝ, ℝ) ∞
      (fun z : (P × M) × M => f (z.1.1, z.2))
      ((U ×ˢ univ) ×ˢ univ) (q, q.2) :=
    (hf q hq).comp (q, q.2)
      (f := fun z : (P × M) × M => (z.1.1, z.2))
      (contMDiffWithinAt_fst.fst.prodMk contMDiffWithinAt_snd)
      (fun (z : (P × M) × M) (hz : z ∈ (U ×ˢ univ) ×ˢ univ) => ⟨hz.1.1, hz.2⟩)
  have hd := ContMDiffWithinAt.mfderivWithin
    (n := ∞) (m := ∞) (f := fun z : P × M => fun x : M => f (z.1, x))
    (g := Prod.snd) hcomp contMDiffWithinAt_snd hq
    (fun _ _ => mem_univ _) (by simp) uniqueMDiffOn_univ
  have hsnd : ContMDiff (𝓘(ℝ, P).prod (𝓡 n)) (𝓡 n) ∞
      (Prod.snd : P × M → M) := contMDiff_snd
  have hfield : ContMDiffWithinAt (𝓘(ℝ, P).prod I) ((𝓡 n).prod 𝓘(ℝ, E)) ∞
      (fun z : P × M => (⟨z.2, X z.2⟩ : TangentBundle I M)) (U ×ˢ univ) q :=
    ((X.contMDiff.comp hsnd) q).contMDiffWithinAt
  have happ := ContMDiffWithinAt.clm_apply_of_inCoordinates
    (IB₁ := I) (IB₂ := 𝓘(ℝ, ℝ)) (IM := 𝓘(ℝ, P).prod I)
    (b₁ := Prod.snd) (b₂ := f) hd hfield (hf q hq)
  have hscalar := (contMDiff_snd_tangentBundle_modelSpace ℝ 𝓘(ℝ, ℝ)).contMDiffAt.comp_contMDiffWithinAt
    q happ
  simpa only [Function.comp_def, mfderivWithin_univ, scalarDirectional] using hscalar

theorem contMDiffOn_parameter_word {iota : Type*} {U : Set P}
    (V : iota → SmoothField (n := n) (M := M)) (w : List iota)
    (f : P × M → ℝ)
    (hf : ContMDiffOn (𝓘(ℝ, P).prod I) 𝓘(ℝ, ℝ) ∞ f (U ×ˢ univ)) :
    ContMDiffOn (𝓘(ℝ, P).prod I) 𝓘(ℝ, ℝ) ∞
      (fun q : P × M => directionalWord V w (fun x => f (q.1, x)) q.2)
      (U ×ˢ univ) := by
  induction w with
  | nil => exact hf
  | cons i w ih =>
    exact contMDiffOn_parameter_directional _ ih (V i)

end JointPullback

section ActualBackground

set_option synthInstance.maxHeartbeats 100000

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [CompactSpace M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

local notation "I" => 𝓡 n

variable (g0 : RiemannianMetric n M) (Phi : P → Diffeomorph I I M M ∞)

def background (g0 : RiemannianMetric n M) (Phi : P → Diffeomorph I I M M ∞)
    (p : P) : RiemannianMetric n M := smoothPullbackMetric g0 (Phi p)

theorem background_inner (g0 : RiemannianMetric n M) (Phi : P → Diffeomorph I I M M ∞)
    (p : P) (x : M) (v w : TangentSpace I x) :
    (background g0 Phi p).inner x v w =
      g0.inner (Phi p x) (mfderiv I I (Phi p) x v) (mfderiv I I (Phi p) x w) :=
  smoothPullbackMetric_inner g0 (Phi p) x v w

def seed (g0 : RiemannianMetric n M) (Phi : P → Diffeomorph I I M M ∞)
    (p : P) : SmoothTensor (n := n) (M := M) :=
  metricTensor (background g0 Phi p) - metricTensor g0

theorem seed_apply (g0 : RiemannianMetric n M) (Phi : P → Diffeomorph I I M M ∞)
    (p : P) (x : M) (v w : TangentSpace I x) :
    seed g0 Phi p x v w =
      g0.inner (Phi p x) (mfderiv I I (Phi p) x v) (mfderiv I I (Phi p) x w) -
        g0.inner x v w := by
  change (background g0 Phi p).inner x v w - g0.inner x v w = _
  rw [background_inner]

theorem seed_symm (g0 : RiemannianMetric n M) (Phi : P → Diffeomorph I I M M ∞)
    (p : P) (x : M) (v w : TangentSpace I x) :
    seed g0 Phi p x v w = seed g0 Phi p x w v := by
  change (background g0 Phi p).inner x v w - g0.inner x v w =
    (background g0 Phi p).inner x w v - g0.inner x w v
  rw [(background g0 Phi p).symm x v w, g0.symm x v w]

theorem background_eq_add_seed (g0 : RiemannianMetric n M) (Phi : P → Diffeomorph I I M M ∞)
    (p : P) (x : M) (v w : TangentSpace I x) :
    (background g0 Phi p).inner x v w = g0.inner x v w + seed g0 Phi p x v w := by
  change (background g0 Phi p).inner x v w =
    g0.inner x v w + ((background g0 Phi p).inner x v w - g0.inner x v w)
  ring

theorem seed_zero (g0 : RiemannianMetric n M) (Phi : P → Diffeomorph I I M M ∞)
    (hPhi0 : Phi 0 = Diffeomorph.refl I M ∞) : seed g0 Phi 0 = 0 := by
  ext x v w
  rw [seed_apply, hPhi0]
  simp only [Diffeomorph.coe_refl, mfderiv_id, ContinuousLinearMap.id_apply, id_eq, sub_self]
  rfl

variable {g0} (d : Data g0)

theorem seed_probe_eq (Phi : P → Diffeomorph I I M M ∞) (d : Data g0)
    (p : P) (ab : d.ProbeIndex) :
    scalarProbe d.fields (seed g0 Phi p) ab =
      probeDifference d.fields (background g0 Phi p) g0 ab := rfl

theorem contMDiffOn_seed_probe (Phi : P → Diffeomorph I I M M ∞) (d : Data g0) {U : Set P}
    (hPhi : ContMDiffOn (𝓘(ℝ, P).prod I) I ∞
      (fun q : P × M => Phi q.1 q.2) (U ×ˢ univ)) (ab : d.ProbeIndex) :
    ContMDiffOn (𝓘(ℝ, P).prod I) 𝓘(ℝ, ℝ) ∞
      (fun q : P × M => scalarProbe d.fields (seed g0 Phi q.1) ab q.2) (U ×ˢ univ) := by
  have hpull := contMDiffOn_parameter_pullback_pair g0 Phi hPhi
    (d.fields ab.1) (d.fields ab.2)
  have hsnd : ContMDiff (𝓘(ℝ, P).prod (𝓡 n)) (𝓡 n) ∞
      (Prod.snd : P × M → M) := contMDiff_snd
  have hbase := (contMDiff_pairing (metricTensor g0) (d.fields ab.1) (d.fields ab.2)).comp
    hsnd
  simpa only [scalarProbe, seed_apply, metricTensor_apply, Function.comp_def] using
    hpull.sub hbase.contMDiffOn

theorem contMDiffOn_seed_word (Phi : P → Diffeomorph I I M M ∞) (d : Data g0) {U : Set P}
    (hPhi : ContMDiffOn (𝓘(ℝ, P).prod I) I ∞
      (fun q : P × M => Phi q.1 q.2) (U ×ˢ univ))
    (ab : d.ProbeIndex) (w : List (Fin d.fieldCount)) :
    ContMDiffOn (𝓘(ℝ, P).prod I) 𝓘(ℝ, ℝ) ∞
      (fun q : P × M => directionalWord d.fields w
        (scalarProbe d.fields (seed g0 Phi q.1) ab) q.2) (U ×ˢ univ) :=
  contMDiffOn_parameter_word d.fields w _ (contMDiffOn_seed_probe Phi d hPhi ab)

def backgroundTuples (Phi : P → Diffeomorph I I M M ∞) (d : Data g0) (k : ℕ) (p : P) :
    NativeProbeContinuous (M := M) (iota := Fin d.fieldCount) k :=
  fun ab w => ⟨directionalWord d.fields (List.ofFn w.2)
      (scalarProbe d.fields (seed g0 Phi p) ab),
    (directionalWord_contMDiff d.fields (List.ofFn w.2)
      (scalarProbe_contMDiff d.fields (seed g0 Phi p) ab)).continuous⟩

theorem backgroundTuples_apply (Phi : P → Diffeomorph I I M M ∞) (d : Data g0)
    (k : ℕ) (p : P) (ab : d.ProbeIndex)
    (w : List (Fin d.fieldCount)) (hw : w.length ≤ k) (x : M) :
    backgroundTuples Phi d k p ab (wordIndex w hw) x =
      directionalWord d.fields w (probeDifference d.fields (background g0 Phi p) g0 ab) x := by
  simp only [backgroundTuples, wordIndex_word, ContinuousMap.coe_mk, seed_probe_eq]

theorem backgroundTuples_contDiffOn (Phi : P → Diffeomorph I I M M ∞) (d : Data g0)
    {U : Set P} (hU : IsOpen U)
    (hPhi : ContMDiffOn (𝓘(ℝ, P).prod I) I ∞
      (fun q : P × M => Phi q.1 q.2) (U ×ˢ univ)) (k : ℕ) :
    ContDiffOn ℝ ∞ (backgroundTuples Phi d k) U := by
  apply contDiffOn_pi.mpr
  intro ab
  apply contDiffOn_pi.mpr
  intro w
  have hc := contDiffOn_compact_curry hU
    (fun q : P × M => directionalWord d.fields (List.ofFn w.2)
      (scalarProbe d.fields (seed g0 Phi q.1) ab) q.2)
    (contMDiffOn_seed_word Phi d hPhi ab (List.ofFn w.2))
  have heq : (fun p => backgroundTuples Phi d k p ab w) =
      (fun p => ContinuousMap.mkD (directionalWord d.fields (List.ofFn w.2)
        (scalarProbe d.fields (seed g0 Phi p) ab)) 0) := by
    funext p
    exact (ContinuousMap.mkD_of_continuous
      (directionalWord_contMDiff d.fields (List.ofFn w.2)
        (scalarProbe_contMDiff d.fields (seed g0 Phi p) ab)).continuous).symm
  rw [heq]
  exact hc

theorem backgroundTuples_zero (Phi : P → Diffeomorph I I M M ∞) (d : Data g0)
    (hPhi0 : Phi 0 = Diffeomorph.refl I M ∞) (k : ℕ) :
    backgroundTuples Phi d k 0 = 0 := by
  funext ab w
  apply ContinuousMap.ext
  intro x
  change directionalWord d.fields (List.ofFn w.2)
    (scalarProbe d.fields (seed g0 Phi 0) ab) x = 0
  rw [seed_zero g0 Phi hPhi0]
  change directionalWord d.fields (List.ofFn w.2) (0 : M → ℝ) x = 0
  have hz (word : List (Fin d.fieldCount)) : directionalWord d.fields word (0 : M → ℝ) = 0 := by
    induction word with
    | nil => rfl
    | cons i word ih =>
      rw [directionalWord_cons, ih]
      funext y
      change mfderiv I 𝓘(ℝ, ℝ) (fun _ : M => (0 : ℝ)) y (d.fields i y) = 0
      simp
  exact congrFun (hz _) x

theorem smoothProbeTuples_seed_eq (Phi : P → Diffeomorph I I M M ∞) (d : Data g0)
    (k : ℕ) (p : P) :
    smoothProbeTuples d k (seed g0 Phi p) =
      fun ab w => ContinuousMap.toLp 2 d.charts.measure ℝ (backgroundTuples Phi d k p ab w) := rfl

theorem smoothProbeTuples_seed_contDiffOn (Phi : P → Diffeomorph I I M M ∞) (d : Data g0)
    {U : Set P} (hU : IsOpen U)
    (hPhi : ContMDiffOn (𝓘(ℝ, P).prod I) I ∞
      (fun q : P × M => Phi q.1 q.2) (U ×ˢ univ)) (k : ℕ) :
    ContDiffOn ℝ ∞ (fun p => smoothProbeTuples d k (seed g0 Phi p)) U := by
  apply contDiffOn_pi.mpr
  intro ab
  apply contDiffOn_pi.mpr
  intro w
  exact (ContinuousMap.toLp 2 d.charts.measure ℝ :
    C(M, ℝ) →L[ℝ] Lp ℝ 2 d.charts.measure).contDiff.comp_contDiffOn
      (contDiffOn_pi.mp (contDiffOn_pi.mp (backgroundTuples_contDiffOn Phi d hU hPhi k) ab) w)

def seedCoordinates (Phi : P → Diffeomorph I I M M ∞) (d : Data g0)
    (r : ℕ) (p : P) : State d.SymmetricIndex :=
  evenOutput d r (smoothProbeTuples d (2 * r) (seed g0 Phi p))

theorem seedCoordinates_eq (Phi : P → Diffeomorph I I M M ∞) (d : Data g0)
    (r : ℕ) (p : P) :
    seedCoordinates Phi d r p =
      d.smoothTensorCoordinates (2 * r) (seed g0 Phi p) (seed_symm g0 Phi p) :=
  evenOutput_smoothProbeTuples d r (seed g0 Phi p) (seed_symm g0 Phi p)

theorem seedCoordinates_contDiffOn (Phi : P → Diffeomorph I I M M ∞) (d : Data g0)
    {U : Set P} (hU : IsOpen U)
    (hPhi : ContMDiffOn (𝓘(ℝ, P).prod I) I ∞
      (fun q : P × M => Phi q.1 q.2) (U ×ˢ univ)) (r : ℕ) :
    ContDiffOn ℝ ∞ (seedCoordinates Phi d r) U :=
  (evenOutput d r).contDiff.comp_contDiffOn
    (smoothProbeTuples_seed_contDiffOn Phi d hU hPhi (2 * r))

theorem seedCoordinates_zero (Phi : P → Diffeomorph I I M M ∞) (d : Data g0)
    (hPhi0 : Phi 0 = Diffeomorph.refl I M ∞) (r : ℕ) :
    seedCoordinates Phi d r 0 = 0 := by
  have htuple : smoothProbeTuples d (2 * r) (seed g0 Phi 0) = 0 := by
    rw [smoothProbeTuples_seed_eq, backgroundTuples_zero Phi d hPhi0]
    funext ab w
    exact map_zero _
  rw [seedCoordinates, htuple, map_zero]

end ActualBackground

end PoincareConjecture.DeTurckParameterBackgroundNative

end
