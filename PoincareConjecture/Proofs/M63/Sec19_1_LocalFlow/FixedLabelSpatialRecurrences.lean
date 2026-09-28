import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.C1EmbeddingPushforward
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.C2NormalizationContinuity
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.C2GaugeWitnesses
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.UniquenessEmbeddedCurve
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.MixedEmbeddingHessian
import PoincareConjecture.Proofs.M63.Sec19_2_CurveEstimates.RelabelingGeometry
import PoincareConjecture.Proofs.M63.Mathlib.DenseParameterDerivative
import PoincareConjecture.Proofs.M63.Mathlib.SmoothRetractionDifferentials

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

set_option maxHeartbeats 800000 in

theorem fixedLabel_embedded_closed_spatial_recurrences
    (F : RicciFlow n M (Icc a b)) {c : ℝ → ℝ → M} {J : Set ℝ}
    (hc : M63C2ShrinkingCurveOn F c J) (hi : M63IntrinsicRegularityOn F c J)
    {tau s : ℝ} (hat : a < tau) (hts : tau < s) (hslab : Icc tau s ⊆ J)
    {psi : ℝ → ℝ} (hpsi : ContDiff ℝ 2 psi) (hpos : ∀ x, 0 < deriv psi x)
    {e : M → W} (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e)
    {U : Set W} (hU : IsOpen U) (heU : range e ⊆ U) {ρ : W → M}
    (hρ : ContMDiffOn 𝓘(ℝ, W) (𝓡 n) ∞ ρ U) (hρe : ∀ p, ρ (e p) = p) :
    let d := fun x t => c (psi x) t
    let q := fun x t => e (d x t)
    let v := fun x t => curveSpeed F d t x
    let K := fun (i : ℕ) (t x : ℝ) => match i with
      | 0 => spatialUnitTangent F c t x
      | i + 1 => m63CurvatureJet F c i t x
    let R : ℕ → ℝ → ℝ → W :=
      fun i x t => mfderiv (𝓡 n) 𝓘(ℝ, W) e (d x t) (K i t (psi x))
    let B := fun (t : ℝ) (z p h : W) => coordinateHessian (F.connection t) e (ρ z)
      (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z p) (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z h)
    ContinuousOn (fun z : ℝ × ℝ => q z.1 z.2) (univ ×ˢ Icc tau s) ∧
      ContinuousOn (fun z : ℝ × ℝ => v z.1 z.2) (univ ×ˢ Icc tau s) ∧
      (∀ i, ContinuousOn (fun z : ℝ × ℝ => R i z.1 z.2) (univ ×ˢ Icc tau s)) ∧
      (∀ t ∈ Icc tau s, ∀ x, HasDerivAt (fun y => q y t) (v x t • R 0 x t) x) ∧
      ∀ i, ∀ t ∈ Icc tau s, ∀ x, HasDerivAt (fun y => R i y t)
        (v x t • (B t (q x t) (R 0 x t) (R i x t) + R (i + 1) x t)) x := by
  let d := fun x t => c (psi x) t
  let q := fun x t => e (d x t)
  let v := fun x t => curveSpeed F d t x
  let K := fun (i : ℕ) (t x : ℝ) => match i with
    | 0 => spatialUnitTangent F c t x
    | i + 1 => m63CurvatureJet F c i t x
  let R : ℕ → ℝ → ℝ → W :=
    fun i x t => mfderiv (𝓡 n) 𝓘(ℝ, W) e (d x t) (K i t (psi x))
  let B := fun (t : ℝ) (z p h : W) => coordinateHessian (F.connection t) e (ρ z)
    (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z p) (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z h)
  let A : ℝ × ℝ → ℝ × ℝ := fun z => (psi z.1, z.2)
  have hA : Continuous A := (hpsi.continuous.comp continuous_fst).prodMk continuous_snd
  have hAJ : MapsTo A (univ ×ˢ Icc tau s) (univ ×ˢ J) :=
    fun z hz => ⟨mem_univ _, hslab hz.2⟩
  have hAS : MapsTo A (univ ×ˢ Icc tau s) (univ ×ˢ Icc tau s) :=
    fun z hz => ⟨mem_univ _, hz.2⟩
  have hdata := c2ShrinkingCurve_embedded_closed_data hc he
  have hq : ContinuousOn (fun z : ℝ × ℝ => q z.1 z.2) (univ ×ˢ Icc tau s) :=
    hdata.2.2.1.comp hA.continuousOn hAJ
  have hvold : ContinuousOn (fun z : ℝ × ℝ => curveSpeed F c z.2 (psi z.1))
      (univ ×ˢ Icc tau s) :=
    (c2ShrinkingCurve_speed_normalization_continuousOn F hc).1.comp hA.continuousOn hAJ
  have hvpos (t : ℝ) (ht : t ∈ Icc tau s) (x : ℝ) : 0 < curveSpeed F c t x :=
    Real.sqrt_pos.mpr ((F.metric t).pos _ _ (hc.immersed t (hslab ht) x))
  have hpsid (x : ℝ) : HasDerivAt psi (deriv psi x) x :=
    (hpsi.differentiable (by norm_num) x).hasDerivAt
  have hvspec (t : ℝ) (ht : t ∈ Icc tau s) (x : ℝ) :
      v x t = deriv psi x * curveSpeed F c t (psi x) :=
    curveSpeed_comp F c ((hc.spatial_regular t (hslab ht)).mdifferentiable
      (by norm_num) (psi x)) (hpsid x) (hpos x).le
  have hv : ContinuousOn (fun z : ℝ × ℝ => v z.1 z.2) (univ ×ˢ Icc tau s) :=
    (((hpsi.deriv' (n := 1)).continuous.comp continuous_fst).continuousOn.mul hvold).congr
      (fun z hz => hvspec z.2 hz.2 z.1)
  have hpush : Continuous (fun p : TangentBundle (𝓡 n) M =>
      (mfderiv (𝓡 n) 𝓘(ℝ, W) e p.1 p.2 : W)) :=
    (contMDiff_snd_tangentBundle_modelSpace (n := ∞) W 𝓘(ℝ, W)).continuous.comp
      (he.continuous_tangentMap (by simp))
  have hR : ∀ i, ContinuousOn (fun z : ℝ × ℝ => R i z.1 z.2) (univ ×ˢ Icc tau s) := by
    intro i
    cases i with
    | zero =>
      have hfirst := hdata.2.2.2.1.comp hA.continuousOn hAJ
      have hnorm := (hvold.inv₀ (fun z hz => (hvpos z.2 hz.2 (psi z.1)).ne')).smul hfirst
      apply hnorm.congr
      intro z hz
      change mfderiv (𝓡 n) 𝓘(ℝ, W) e (c (psi z.1) z.2)
          ((curveSpeed F c z.2 (psi z.1))⁻¹ •
            curveVelocity (n := n) (fun y => c y z.2) (psi z.1)) =
        (curveSpeed F c z.2 (psi z.1))⁻¹ • deriv (fun y => e (c y z.2)) (psi z.1)
      rw [map_smul, (hdata.2.1 z.2 (hslab hz.2) (psi z.1)).deriv]
    | succ i =>
      exact (hpush.comp_continuousOn (hi.closed_positive_jets tau s hat hts.le hslab i)).comp
        hA.continuousOn hAS
  have hleft := (smooth_retraction_differentials he hU heU hρ hρe).2.2
  have hBval (i : ℕ) (t x : ℝ) :
      B t (q x t) (R 0 x t) (R i x t) =
        coordinateHessian (F.connection t) e (d x t) (K 0 t (psi x)) (K i t (psi x)) := by
    dsimp only [B, q, R]
    erw [hleft (d x t) (K 0 t (psi x)), hleft (d x t) (K i t (psi x)), hρe (d x t)]
  have hB : ContinuousOn
      (fun z : (ℝ × W) × (W × W) => (B z.1.1 z.1.2 z.2.1 z.2.2 : W))
      ((Icc a b ×ˢ U) ×ˢ univ) :=
    (flow_coordinateHessian_mixed_pullback_contDiffOn F he hU hρ).continuousOn
  have hmap (i : ℕ) : ContinuousOn
      (fun z : ℝ × ℝ => ((z.2, q z.1 z.2), (R 0 z.1 z.2, R i z.1 z.2)))
      (univ ×ˢ Icc tau s) :=
    (continuous_snd.continuousOn.prodMk hq).prodMk ((hR 0).prodMk (hR i))
  have hmaps (i : ℕ) : MapsTo
      (fun z : ℝ × ℝ => ((z.2, q z.1 z.2), (R 0 z.1 z.2, R i z.1 z.2)))
      (univ ×ˢ Icc tau s) ((Icc a b ×ˢ U) ×ˢ univ) :=
    fun z hz => ⟨⟨hc.domain_subset (hslab hz.2), heU (mem_range_self _)⟩, mem_univ _⟩
  have hBR (i : ℕ) :=
    hB.comp (s := univ ×ˢ Icc tau s) (hmap i) (hmaps i)
  have hRHS (i : ℕ) : ContinuousOn
      (fun z : ℝ × ℝ => v z.1 z.2 •
        (B z.2 (q z.1 z.2) (R 0 z.1 z.2) (R i z.1 z.2) + R (i + 1) z.1 z.2))
      (univ ×ˢ Icc tau s) := hv.smul ((hBR i).add (hR (i + 1)))
  have hvelocity (t : ℝ) (ht : t ∈ Icc tau s) (x : ℝ) :
      curveVelocity (n := n) (fun y => c y t) x = curveSpeed F c t x • K 0 t x := by
    symm
    change curveSpeed F c t x • ((curveSpeed F c t x)⁻¹ •
      curveVelocity (n := n) (fun y => c y t) x) = _
    rw [smul_smul, mul_inv_cancel₀ (hvpos t ht x).ne', one_smul]
  have hqder (t : ℝ) (ht : t ∈ Icc tau s) (x : ℝ) :
      HasDerivAt (fun y => q y t) (v x t • R 0 x t) x := by
    have hd := (hdata.2.1 t (hslab ht) (psi x)).scomp x (hpsid x)
    apply hd.congr_deriv
    change deriv psi x • (mfderiv (𝓡 n) 𝓘(ℝ, W) e (c (psi x) t)
      (curveVelocity (n := n) (fun y => c y t) (psi x))) = v x t • R 0 x t
    rw [hvelocity t ht (psi x), map_smul, smul_smul, ← hvspec t ht x]
  have hKnext (i : ℕ) (t x : ℝ) : K (i + 1) t x =
      (curveSpeed F c t x)⁻¹ • rampHorizontalCovariantDerivative (F.connection t)
        (fun y => c y t) (K i t) x := by
    cases i <;> rfl
  have hcovold (i : ℕ) (t : ℝ) (ht : t ∈ Icc tau s) (x : ℝ) :
      rampHorizontalCovariantDerivative (F.connection t) (fun y => c y t) (K i t) x =
        curveSpeed F c t x • K (i + 1) t x := by
    rw [hKnext, smul_smul, mul_inv_cancel₀ (hvpos t ht x).ne', one_smul]
  have hKi (i : ℕ) (t : ℝ) (ht : t ∈ interior J) (x : ℝ) :
      ContMDiffAt 𝓘(ℝ, ℝ) ((𝓡 n).prod (𝓡 n)) 1
        (fun y => (⟨c y t, K i t y⟩ : TangentBundle (𝓡 n) M)) x := by
    cases i with
    | zero =>
      exact unitTangent_contMDiff_of_c2 F c (t := t)
        (hc.spatial_regular t (interior_subset ht)) (hc.immersed t (interior_subset ht)) x
    | succ i =>
      have hm : (x, t) ∈ univ ×ˢ interior J := ⟨mem_univ _, ht⟩
      have hiat := ((hi.interior_jets i) (x, t) hm).contMDiffAt
        ((isOpen_univ.prod isOpen_interior).mem_nhds hm)
      have hline : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ) 1 (fun y : ℝ => (y, t)) x :=
        (contDiffAt_id.prodMk contDiffAt_const).contMDiffAt
      exact hiat.comp x hline
  have hscale (t : ℝ) (p : M) (X Y : TangentSpace (𝓡 n) p) (r : ℝ) :
      coordinateHessian (F.connection t) e p (r • X) Y =
        r • coordinateHessian (F.connection t) e p X Y := by
    ext i
    have hei : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun q => e q i) :=
      (EuclideanSpace.proj i).contDiff.contMDiff.comp he
    obtain ⟨T, hT⟩ := (M04.isSmoothCovariantTensor_hessian (F.connection t) hei).1 p
    have hrep (v w : TangentSpace (𝓡 n) p) :
        (F.connection t).hessian (fun q => e q i) p v w = T ![v, w] := hT ![v, w]
    change (F.connection t).hessian (fun q => e q i) p (r • X) Y =
      r * (F.connection t).hessian (fun q => e q i) p X Y
    rw [hrep, hrep]
    simpa only [Matrix.vecCons, smul_eq_mul] using T.cons_smul ![Y] r X
  have hder (i : ℕ) (t : ℝ) (ht : t ∈ Ioo tau s) (x : ℝ) :
      HasDerivAt (fun y => R i y t)
        (v x t • (B t (q x t) (R 0 x t) (R i x t) + R (i + 1) x t)) x := by
    have htS : t ∈ Icc tau s := Ioo_subset_Icc_self ht
    have htI : t ∈ interior J := interior_mono hslab (by simpa only [interior_Icc] using ht)
    have hpsione : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) 1 psi x :=
      (hpsi.of_le (by norm_num)).contMDiff.contMDiffAt
    have hd : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n) 1 (fun y => d y t) x :=
      (((hc.spatial_regular t (hslab htS)).comp hpsi.contMDiff).of_le (by norm_num)) x
    have hY : ContMDiffAt 𝓘(ℝ, ℝ) ((𝓡 n).prod (𝓡 n)) 1
        (fun y => (⟨d y t, K i t (psi y)⟩ : TangentBundle (𝓡 n) M)) x :=
      (hKi i t htI (psi x)).comp x hpsione
    have hvel : curveVelocity (n := n) (fun y => d y t) x = v x t • K 0 t (psi x) := by
      rw [curveVelocity_comp
        ((hc.spatial_regular t (hslab htS)).mdifferentiable (by norm_num) (psi x))
        (hpsid x), hvelocity t htS (psi x), smul_smul, ← hvspec t htS x]
    have hcov : rampHorizontalCovariantDerivative (F.connection t)
        (fun y => d y t) (fun y => K i t (psi y)) x = v x t • K (i + 1) t (psi x) := by
      rw [pullback_comp (F.connection t)
        ((hKi i t htI (psi x)).mdifferentiableAt (by norm_num)) (hpsid x),
        hcovold i t htS (psi x), smul_smul, ← hvspec t htS x]
    have hp := hasDerivAt_embedding_pushforward_of_contMDiffAt_one
      (F.connection t) he hd (fun y => K i t (psi y)) hY
    apply hp.congr_deriv
    change HAdd.hAdd (α := W) (β := W) (γ := W)
      (coordinateHessian (F.connection t) e (d x t)
        (curveVelocity (n := n) (fun y => d y t) x) (K i t (psi x)))
      (mfderiv (𝓡 n) 𝓘(ℝ, W) e (d x t)
        (rampHorizontalCovariantDerivative (F.connection t)
          (fun y => d y t) (fun y => K i t (psi y)) x)) =
      v x t • (B t (q x t) (R 0 x t) (R i x t) + R (i + 1) x t)
    rw [hvel, hcov, hscale, map_smul, smul_add, hBval]
  refine ⟨hq, hv, hR, hqder, ?_⟩
  intro i
  exact hasDerivAt_of_dense_parameter_set Ioo_subset_Icc_self
    (by rw [closure_Ioo hts.ne]) (hR i) (hRHS i) (hder i)

end PoincareConjecture.M63
