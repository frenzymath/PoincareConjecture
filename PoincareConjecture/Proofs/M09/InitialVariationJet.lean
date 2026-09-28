import PoincareConjecture.Proofs.M09.ChartFieldDerivative
import PoincareConjecture.Proofs.M09.MixedPartials
import PoincareConjecture.Proofs.M09.CompactFieldExtension
import PoincareConjecture.Proofs.M09.InitialVariationFields
import PoincareConjecture.Proofs.M09.InitialVectorIdentification









set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 800000

open scoped Manifold ContDiff Bundle Topology
open Filter

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}

local notation "Q" => EuclideanSpace ℝ (Fin n)

set_option backward.isDefEq.respectTransparency false in
theorem initialVectorVariation_initial_pullback (A : LExponentialFamily F T τmax p)
    (Z W : TangentSpace (𝓡 n) p) (b : ℝ) (hb : 0 < b) (hmax : b < τmax)
    (E : ParametricAlongCurveExtensionOn (sqrtParameterInterval 0 b)
      (initialVectorVariation A Z W b hb hmax).toLVariation.baseSquareCurve
      (squareVariationField (initialVectorVariation A Z W b hb hmax).toLVariation)) :
    (pullbackCovariantDerivative F (fun s ↦ T - s ^ 2)
      (initialVectorVariation A Z W b hb hmax).toLVariation.baseSquareCurve
      (squareVariationField (initialVectorVariation A Z W b hb hmax).toLVariation)
      (sqrtParameterInterval 0 b) E 0 : Q) = (2 : ℝ) • W := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric T).toRiemannianMetric⟩
  let V := (initialVectorVariation A Z W b hb hmax).toLVariation
  let H : ℝ × ℝ → M := fun z ↦ V.squareFamily z.1 z.2
  let Ω := V.squareDomain ∩ H ⁻¹' (chartAt Q p).source
  let f : ℝ × ℝ → Q := fun z ↦ (chartAt Q p) (H z)
  let U := (fun s : ℝ ↦ (s, (0 : ℝ))) ⁻¹' Ω
  let v : ℝ → Q := fun s ↦ deriv (fun u ↦ f (s, u)) 0
  have hH : ContMDiffOn (𝓘(ℝ, ℝ × ℝ)) (𝓡 n) ∞ H V.squareDomain := by
    convert! V.square_smooth using 1 <;>
      simp only [modelWithCornersSelf_prod, chartedSpaceSelf_prod]
  have hΩ : IsOpen Ω := hH.continuousOn.isOpen_inter_preimage V.square_open
    (chartAt Q p).open_source
  have hf : ContDiffOn ℝ ∞ f Ω :=
    (contMDiffOn_chart.comp (hH.mono Set.inter_subset_left) (fun z hz ↦ hz.2)).contDiffOn
  have hU : IsOpen U := hΩ.preimage (continuous_id.prodMk continuous_const)
  have hK : sqrtParameterInterval 0 b = Set.Icc 0 (Real.sqrt b) := by
    simp [sqrtParameterInterval]
  have hzeroK : (0 : ℝ) ∈ sqrtParameterInterval 0 b := by
    rw [hK]
    exact ⟨le_rfl, Real.sqrt_nonneg b⟩
  have hbase : V.baseSquareCurve 0 = p := by
    rw [show V.baseSquareCurve = A.squareFamily Z from
      initialVectorVariation_baseSquareCurve A Z W b hb hmax]
    exact A.square_at_zero Z
  have hzeroΩ : ((0, 0) : ℝ × ℝ) ∈ Ω := by
    refine ⟨V.square_contains ⟨hzeroK,
      neg_lt_zero.mpr V.radius_pos, V.radius_pos⟩, ?_⟩
    change V.baseSquareCurve 0 ∈ (chartAt Q p).source
    rw [hbase]
    exact mem_chart_source Q p
  have hv : ContDiffOn ℝ ∞ v U := contDiffOn_partial_snd f Ω hΩ hf
  have hfield (s : ℝ) (hs : s ∈ U) :
      chartVectorField p (v s) (V.baseSquareCurve s) = squareVariationField V s := by
    have hslice : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) (V.squareFamily s) 0 :=
      ((hH.contMDiffAt (V.square_open.mem_nhds hs.1)).comp 0
        (show ContMDiffAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ × ℝ)) ∞
          (fun u : ℝ ↦ (s, u)) 0 from
          (contDiff_const.prodMk contDiff_id).contMDiff.contMDiffAt)).mdifferentiableAt
        (by simp)
    have hcoord := (hasDerivAt_chart_curve p (V.squareFamily s) 0 hs.2 hslice).deriv
    change v s = mfderiv (𝓡 n) (𝓡 n) (chartAt Q p) (V.baseSquareCurve s)
      (squareVariationField V s) at hcoord
    rw [hcoord]
    exact chartVectorField_differential p (V.baseSquareCurve s) (squareVariationField V s) hs.2
  let L : TangentSpace (𝓡 n) p →L[ℝ] Q := mfderiv (𝓡 n) (𝓡 n) (chartAt Q p) p
  let k : ℝ → Q := fun u ↦ L ((2 : ℝ) • (Z + u • W))
  have hline : HasDerivAt (fun u : ℝ ↦ Z + u • W) W 0 := by
    have hsmul : HasDerivAt (fun u : ℝ ↦ u • W) W 0 := by
      simpa only [id_eq, one_smul] using (hasDerivAt_id (0 : ℝ)).smul_const W
    exact hsmul.const_add Z
  have hk := L.hasFDerivAt.comp_hasDerivAt 0 (hline.const_smul (2 : ℝ))
  have hjet : ∀ᶠ u in 𝓝 (0 : ℝ), HasDerivAt (fun s ↦ f (s, u)) (k u) 0 := by
    apply Filter.Eventually.of_forall
    intro u
    have hsmooth := (lExponentialFamily_squareSlice_contMDiffAt A (Z + u • W) 0
      ⟨le_rfl, Real.sqrt_pos.mpr (hb.trans hmax)⟩).mdifferentiableAt (by simp)
    have hsource : A.squareFamily (Z + u • W) 0 ∈ (chartAt Q p).source := by
      rw [A.square_at_zero]
      exact mem_chart_source Q p
    have hd := hasDerivAt_chart_curve p (A.squareFamily (Z + u • W)) 0 hsource hsmooth
    change HasDerivAt (fun s ↦ (chartAt Q p) (A.squareFamily (Z + u • W) s))
      ((mfderiv (𝓡 n) (𝓡 n) (chartAt Q p) (A.squareFamily (Z + u • W) 0))
        (curveVelocity (n := n) (A.squareFamily (Z + u • W)) 0 : Q)) 0 at hd
    rw [lExponentialFamily_initial_velocity, A.square_at_zero] at hd
    exact hd
  have hdv : HasDerivAt v (L ((2 : ℝ) • W)) 0 :=
    hasDerivAt_partial_snd_of_initial_fst f (hf.contDiffAt (hΩ.mem_nhds hzeroΩ)) k _ hk hjet
  have hvzero : v 0 = 0 := by
    have heq : (fun u : ℝ ↦ f (0, u)) = fun _ ↦ (chartAt Q p) p := by
      funext u
      change (chartAt Q p) (A.squareFamily (Z + u • W) 0) = _
      rw [A.square_at_zero]
    change deriv (fun u ↦ f (0, u)) 0 = 0
    rw [heq, deriv_const]
  have hγ : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) V.baseSquareCurve 0 := by
    rw [show V.baseSquareCurve = A.squareFamily Z from
      initialVectorVariation_baseSquareCurve A Z W b hb hmax]
    exact (lExponentialFamily_squareSlice_contMDiffAt A Z 0
      ⟨le_rfl, Real.sqrt_pos.mpr (hb.trans hmax)⟩).mdifferentiableAt (by simp)
  have hKdiff : UniqueDiffWithinAt ℝ (sqrtParameterInterval 0 b) 0 := by
    rw [hK]
    exact uniqueDiffOn_Icc (Real.sqrt_pos.mpr hb) 0 (by simpa only [← hK] using hzeroK)
  have hpull := pullbackCovariantDerivative_chart_field_zero F (fun s ↦ T - s ^ 2)
    p V.baseSquareCurve (squareVariationField V) (sqrtParameterInterval 0 b) U E 0
    hzeroK hU hzeroΩ hKdiff hγ v hv (fun s hs ↦ hs.2.2)
    (fun s hs ↦ hfield s hs.2) _ hdv hvzero
  change (pullbackCovariantDerivative F (fun s ↦ T - s ^ 2) V.baseSquareCurve
    (squareVariationField V) (sqrtParameterInterval 0 b) E 0 : Q) = _
  rw [hpull]
  rw [hbase]
  exact chartVectorField_differential p p ((2 : ℝ) • W) (mem_chart_source Q p)

end PoincareConjecture.Proofs.M09
