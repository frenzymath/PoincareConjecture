import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerSmoothEuler
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.AlphaCriticalSmooth

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff

noncomputable section

universe u

namespace PoincareConjecture.M60

open CoordinateExponential ConnectionVariation

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "e" => EuclideanSpace.basisFun (Fin 2) ℝ

private theorem weighted_source_change {n : ℕ}
    {u : Plane → EuclideanSpace ℝ (Fin n)} {phi : Plane → Plane} {z : Plane}
    (Gamma : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (w : Plane → ℝ) (hu : ContDiffAt ℝ 2 u (phi z)) (hp : ContDiffAt ℝ 2 phi z)
    (hw : DifferentiableAt ℝ w (phi z)) {a : ℝ} (ha : 0 < a)
    (hgram : ∀ i j : Fin 2, inner ℝ (fderiv ℝ phi z (e i)) (fderiv ℝ phi z (e j)) =
      a * (if i = j then 1 else 0))
    (hlap : fderiv ℝ (fderiv ℝ phi) z (e 0) (e 0) +
      fderiv ℝ (fderiv ℝ phi) z (e 1) (e 1) = 0)
    (heq : ∑ i : Fin 2, covDerivAlong Gamma u
      (fun y => w y • fderiv ℝ u y (e i)) (e i) (phi z) = 0) :
    ∑ i : Fin 2, covDerivAlong Gamma (u ∘ phi)
      (fun y => w (phi y) • fderiv ℝ (u ∘ phi) y (e i)) (e i) z = 0 := by
  let E := EuclideanSpace ℝ (Fin n)
  let L := fderiv ℝ u (phi z)
  let Q := fderiv ℝ phi z
  let B : Plane →L[ℝ] Plane →L[ℝ] E :=
    w (phi z) • (fderiv ℝ (fderiv ℝ u) (phi z) + (Gamma (u (phi z))).bilinearComp L L) +
      (fderiv ℝ w (phi z)).smulRight L
  have hBeval (v : Plane) : B v v = w (phi z) •
      (fderiv ℝ (fderiv ℝ u) (phi z) v v + Gamma (u (phi z)) (L v) (L v)) +
      fderiv ℝ w (phi z) v • L v := rfl
  have hcol (i : Fin 2) :=
    ((hu.fderiv_right (m := 1) (by norm_num)).clm_apply
      (contDiffAt_const (c := e i))).differentiableAt (by norm_num)
  have hprod (i : Fin 2) : fderiv ℝ (fun y => w y • fderiv ℝ u y (e i)) (phi z) =
      w (phi z) • fderiv ℝ (fun y => fderiv ℝ u y (e i)) (phi z) +
        (fderiv ℝ w (phi z)).smulRight (fderiv ℝ u (phi z) (e i)) :=
    (hw.hasFDerivAt.smul (hcol i).hasFDerivAt).fderiv
  have hB : B (e 0) (e 0) + B (e 1) (e 1) = 0 := by
    simp only [Fin.sum_univ_two, covDerivAlong_def, hprod, fderiv_column hu,
      add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, map_smul] at heq
    rw [hBeval, hBeval]
    dsimp only [L]
    convert heq using 1
    module
  have hBq : B (Q (e 0)) (Q (e 0)) + B (Q (e 1)) (Q (e 1)) = 0 := by
    ext k
    let C := EuclideanSpace.proj (𝕜 := ℝ) k
    let B' := ((ContinuousLinearMap.compL ℝ Plane E ℝ C).comp B).toBilinForm
    have ht := sum_bilinear_conformal_basis B' e (fun i => Q (e i)) (by simp) ha hgram
    have hz := congrArg C hB
    simp only [map_add, map_zero] at hz
    change C (B (e 0) (e 0)) + C (B (e 1) (e 1)) = 0 at hz
    change C (B (Q (e 0)) (Q (e 0)) + B (Q (e 1)) (Q (e 1))) = 0
    rw [map_add]
    change (∑ i : Fin 2, C (B (Q (e i)) (Q (e i)))) =
      a * ∑ i : Fin 2, C (B (e i) (e i)) at ht
    simpa only [Fin.sum_univ_two, hz, mul_zero] using ht
  have huc := hu.comp z hp
  have hwc := hw.comp z (hp.differentiableAt (by norm_num))
  have hprod' (i : Fin 2) :
      fderiv ℝ (fun y => w (phi y) • fderiv ℝ (u ∘ phi) y (e i)) z =
      w (phi z) • fderiv ℝ (fun y => fderiv ℝ (u ∘ phi) y (e i)) z +
        (fderiv ℝ (w ∘ phi) z).smulRight (fderiv ℝ (u ∘ phi) z (e i)) :=
    (hwc.hasFDerivAt.smul
      (((huc.fderiv_right (m := 1) (by norm_num)).clm_apply
        (contDiffAt_const (c := e i))).differentiableAt (by norm_num)).hasFDerivAt).fderiv
  have hterm (i : Fin 2) : covDerivAlong Gamma (u ∘ phi)
      (fun y => w (phi y) • fderiv ℝ (u ∘ phi) y (e i)) (e i) z =
      B (Q (e i)) (Q (e i)) + w (phi z) • L (fderiv ℝ (fderiv ℝ phi) z (e i) (e i)) := by
    rw [covDerivAlong_def, hprod' i]
    simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply]
    rw [fderiv_column huc, second_fderiv_comp hu hp,
      fderiv_comp z (hu.differentiableAt (by norm_num)) (hp.differentiableAt (by norm_num)),
      fderiv_comp z hw (hp.differentiableAt (by norm_num))]
    rw [hBeval]
    simp only [Function.comp_apply, Q, L, ContinuousLinearMap.comp_apply, map_smul, smul_add]
    module
  simp_rw [hterm]
  rw [Fin.sum_univ_two]
  have hm : (B (Q (e 0)) (Q (e 0)) + w (phi z) • L
      (fderiv ℝ (fderiv ℝ phi) z (e 0) (e 0))) +
      (B (Q (e 1)) (Q (e 1)) + w (phi z) • L
      (fderiv ℝ (fderiv ℝ phi) z (e 1) (e 1))) =
      (B (Q (e 0)) (Q (e 0)) + B (Q (e 1)) (Q (e 1))) +
        w (phi z) • L (fderiv ℝ (fderiv ℝ phi) z (e 0) (e 0) +
          fderiv ℝ (fderiv ℝ phi) z (e 1) (e 1)) := by rw [map_add, smul_add]; abel
  rw [hm, hBq, hlap, map_zero, smul_zero, add_zero]

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)

private theorem weighted_target_change (g : RiemannianMetric n M)
    (f : Plane → M) (hf : ContMDiff (𝓡 2) (𝓡 n) ∞ f)
    (w : Plane → ℝ) (hw : ContDiff ℝ ∞ w) (p q : M) (z : Plane)
    (hp : f z ∈ (extChartAt (𝓡 n) p).source)
    (hq : f z ∈ (extChartAt (𝓡 n) q).source)
    (hzero : let u := extChartAt (𝓡 n) p ∘ f
      let Gamma := christoffelBilinear (g.pullbackCoefficients (extChartAt (𝓡 n) p).symm)
      ∑ i : Fin 2, covDerivAlong Gamma u
        (fun y => w y • fderiv ℝ u y (e i)) (e i) z = 0) :
    let u := extChartAt (𝓡 n) q ∘ f
    let Gamma := christoffelBilinear (g.pullbackCoefficients (extChartAt (𝓡 n) q).symm)
    ∑ i : Fin 2, covDerivAlong Gamma u
      (fun y => w y • fderiv ℝ u y (e i)) (e i) z = 0 := by
  let cp := extChartAt (𝓡 n) p
  let cq := extChartAt (𝓡 n) q
  let u := cp ∘ f
  let v := cq ∘ f
  let T := cq ∘ cp.symm
  let Gp := christoffelBilinear (g.pullbackCoefficients cp.symm)
  let Gq := christoffelBilinear (g.pullbackCoefficients cq.symm)
  have hu {y : Plane} (hy : f y ∈ cp.source) : ContDiffAt ℝ ∞ u y :=
    contMDiffAt_iff_contDiffAt.mp
      ((contMDiffAt_extChartAt' (x := p) (n := ∞)
        (by simpa only [cp, extChartAt_source] using hy)).comp y (hf y))
  have hsource : ∀ᶠ y in 𝓝 z, f y ∈ cp.source ∧ f y ∈ cq.source := by
    filter_upwards [hf.continuous.continuousAt ((isOpen_extChartAt_source p).mem_nhds hp),
      hf.continuous.continuousAt ((isOpen_extChartAt_source q).mem_nhds hq)] with y hyp hyq
    exact ⟨hyp, hyq⟩
  have hgerm {y : Plane} (hy : f y ∈ cp.source) : T ∘ u =ᶠ[𝓝 y] v := by
    filter_upwards [hf.continuous.continuousAt
      ((isOpen_extChartAt_source p).mem_nhds hy)] with x hx
    exact congrArg cq (cp.left_inv hx)
  have hfield (i : Fin 2) :
      (fun y => fderiv ℝ T (u y) (w y • fderiv ℝ u y (e i))) =ᶠ[𝓝 z]
        (fun y => w y • fderiv ℝ v y (e i)) := by
    filter_upwards [hsource] with y hy
    have hqi : cp.symm (u y) ∈ cq.source := by
      change cp.symm (cp (f y)) ∈ cq.source
      rw [cp.left_inv hy.1]
      exact hy.2
    have hT : ContDiffAt ℝ ∞ T (u y) := contMDiffAt_iff_contDiffAt.mp
      ((contMDiffAt_extChartAt' (x := q) (n := ∞)
        (by simpa only [cq, extChartAt_source] using hqi)).comp _
          ((contMDiffOn_extChartAt_symm (n := ∞) p).contMDiffAt
            ((isOpen_extChartAt_target p).mem_nhds (cp.map_source hy.1))))
    have hd := (hgerm hy.1).fderiv_eq (𝕜 := ℝ)
    rw [fderiv_comp y (hT.differentiableAt (by simp)) ((hu hy.1).differentiableAt (by simp))] at hd
    rw [map_smul]
    exact congrArg (fun A : Plane →L[ℝ] E => w y • A (e i)) hd
  have hterm (i : Fin 2) :
      covDerivAlong Gq v (fun y => w y • fderiv ℝ v y (e i)) (e i) z =
        fderiv ℝ T (u z) (covDerivAlong Gp u
          (fun y => w y • fderiv ℝ u y (e i)) (e i) z) := by
    have h := covDerivAlong_chart_change (P := Plane) (u := u)
      (V := fun y => w y • fderiv ℝ u y (e i)) (p := z) g p q (cp.map_source hp)
      (by change cp.symm (cp (f z)) ∈ cq.source; rw [cp.left_inv hp]; exact hq)
      ((hu hp).differentiableAt (by simp))
      ((hw.contDiffAt.smul (((hu hp).fderiv_right (m := ∞) (by simp)).clm_apply
        contDiffAt_const)).differentiableAt (by simp)) (e i)
    change covDerivAlong Gq (T ∘ u)
      (fun y => fderiv ℝ T (u y) (w y • fderiv ℝ u y (e i))) (e i) z = _ at h
    rw [covDerivAlong_congr_base Gq _ (hgerm hp), covDerivAlong_congr Gq v (hfield i)] at h
    exact h
  change (∑ i : Fin 2, covDerivAlong Gq v
    (fun y => w y • fderiv ℝ v y (e i)) (e i) z) = 0
  simp_rw [hterm]
  rw [← map_sum, hzero, map_zero]

private theorem sphere_transition (p q : UnitTwoSphere) (z : Plane)
    (hz : (chartAt Plane p).symm z ∈ (chartAt Plane q).source) :
    let t := (chartAt Plane q) ∘ (chartAt Plane p).symm
    ContDiffAt ℝ ∞ t z ∧ ∃ a : ℝ, 0 < a ∧
      (∀ i j : Fin 2, inner ℝ (fderiv ℝ t z (e i)) (fderiv ℝ t z (e j)) =
        a * (if i = j then 1 else 0)) ∧
      fderiv ℝ (fderiv ℝ t) z (e 0) (e 0) +
        fderiv ℝ (fderiv ℝ t) z (e 1) (e 1) = 0 := by
  let cp := chartAt Plane p
  let cq := chartAt Plane q
  let t := cq ∘ cp.symm
  have hcp := suSphereChart_smooth p
  have hcq := suSphereChart_smooth q
  have hdata (y : Plane) (hy : cp.symm y ∈ cq.source) :
      ContDiffAt ℝ ∞ t y ∧ (fderiv ℝ t y).IsInvertible ∧
        ∃ a : ℝ, 0 < a ∧ ∀ v w : Plane,
          inner ℝ (fderiv ℝ t y v) (fderiv ℝ t y w) = a * inner ℝ v w := by
    have hqs : ContMDiffAt (𝓡 2) (𝓡 2) ∞ cq (cp.symm y) :=
      (contMDiffOn_chart (I := 𝓡 2) (n := ∞)).contMDiffAt (cq.open_source.mem_nhds hy)
    have hts : ContDiffAt ℝ ∞ t y := contMDiffAt_iff_contDiffAt.mp (hqs.comp y (hcp y))
    have hpt : y ∈ cp.target := by rw [suSphereChart_target]; exact mem_univ y
    have hpd : cp.symm.MDifferentiable (𝓡 2) (𝓡 2) :=
      ⟨(contMDiffOn_chart_symm (n := ∞)).mdifferentiableOn (by simp),
        (contMDiffOn_chart (n := ∞)).mdifferentiableOn (by simp)⟩
    have hqd : cq.MDifferentiable (𝓡 2) (𝓡 2) :=
      ⟨(contMDiffOn_chart (n := ∞)).mdifferentiableOn (by simp),
        (contMDiffOn_chart_symm (n := ∞)).mdifferentiableOn (by simp)⟩
    refine ⟨hts, ?_, ?_⟩
    · change (fderiv ℝ (cq ∘ cp.symm) y).IsInvertible
      rw [← mfderiv_eq_fderiv, mfderiv_comp y (hqs.mdifferentiableAt (by simp))
        ((hcp y).mdifferentiableAt (by simp))]
      exact (show (mfderiv (𝓡 2) (𝓡 2) cq (cp.symm y)).IsInvertible from
        ⟨hqd.mfderiv hy, rfl⟩).comp ⟨hpd.mfderiv hpt, rfl⟩
    · let a := suAlphaRoundFactor y / suAlphaRoundFactor (t y)
      refine ⟨a, div_pos (suRoundFactor_smooth_pos.2 _) (suRoundFactor_smooth_pos.2 _), ?_⟩
      intro v w
      have he : cq.symm ∘ t =ᶠ[𝓝 y] cp.symm := by
        filter_upwards [hcp.continuous.continuousAt (cq.open_source.mem_nhds hy)] with x hx
        exact cq.left_inv hx
      have hval : (fun x => (cq.symm (t x)).1) =ᶠ[𝓝 y] (fun x => (cp.symm x).1) :=
        he.mono fun x hx => congrArg Subtype.val hx
      have hco : ContDiffAt ℝ ∞ (fun x => (cq.symm x).1) (t y) := by
        let : Fact (Module.finrank ℝ LoopAmbient = 2 + 1) := ⟨by simp [LoopAmbient]⟩
        exact contMDiffAt_iff_contDiffAt.mp
          ((contMDiff_coe_sphere (n := 2) (m := ∞) (cq.symm (t y))).comp _
            (hcq (t y)))
      have hder (v : Plane) :
          fderiv ℝ (fun x => (cq.symm x).1) (t y) (fderiv ℝ t y v) =
            fderiv ℝ (fun x => (cp.symm x).1) y v := by
        have h := hval.fderiv_eq (𝕜 := ℝ)
        change fderiv ℝ ((fun x => (cq.symm x).1) ∘ t) y = _ at h
        rw [fderiv_comp y (hco.differentiableAt (by simp)) (hts.differentiableAt (by simp))] at h
        exact congrArg (fun L => L v) h
      have hh := M36.sphere_chart_inverse_fderiv_inner q (t y)
        (fderiv ℝ t y v) (fderiv ℝ t y w)
      rw [hder v, hder w, M36.sphere_chart_inverse_fderiv_inner] at hh
      change suAlphaRoundFactor y * inner ℝ v w =
        suAlphaRoundFactor (t y) * inner ℝ (fderiv ℝ t y v) (fderiv ℝ t y w) at hh
      dsimp only [a]
      rw [div_mul_eq_mul_div]
      apply (eq_div_iff (suRoundFactor_smooth_pos.2 _).ne').mpr
      exact (mul_comm _ _).trans hh.symm
  obtain ⟨ht, htinv, a, ha, hgram⟩ := hdata z hz
  refine ⟨ht, a, ha, fun i j => ?_, ?_⟩
  · simpa only [(EuclideanSpace.basisFun (Fin 2) ℝ).inner_eq_ite] using hgram (e i) (e j)
  · have hlocal : ∀ᶠ y in 𝓝 z, cp.symm y ∈ cq.source :=
      hcp.continuous.continuousAt (cq.open_source.mem_nhds hz)
    have hself : (fun y => inner ℝ (fderiv ℝ t y (e 0)) (fderiv ℝ t y (e 0))) =ᶠ[𝓝 z]
        (fun y => inner ℝ (fderiv ℝ t y (e 1)) (fderiv ℝ t y (e 1))) := by
      filter_upwards [hlocal] with y hy
      obtain ⟨_, _, a, _, hg⟩ := hdata y hy
      rw [hg, hg]
      simp
    have horth : (fun y => inner ℝ (fderiv ℝ t y (e 0)) (fderiv ℝ t y (e 1))) =ᶠ[𝓝 z]
        (fun _ => 0) := by
      filter_upwards [hlocal] with y hy
      obtain ⟨_, _, a, _, hg⟩ := hdata y hy
      rw [hg]
      simp [EuclideanSpace.basisFun, EuclideanSpace.inner_single_left]
    obtain ⟨L, hL⟩ := htinv
    exact laplacian_eq_zero_of_conformal_plane
      (ht.of_le (WithTop.coe_le_coe.mpr le_top))
      (by rw [← hL]; exact L.surjective) hself horth

private def sphereWeight (g : RiemannianMetric n M) (alpha : ℝ)
    (f : UnitTwoSphere → M) (p : UnitTwoSphere) : ℝ :=
  (1 + 2 * m60SphereIntrinsicEnergy g f p) ^ (alpha - 1)

private theorem sphereWeight_chart_smooth (g : RiemannianMetric n M) (alpha : ℝ)
    (f : UnitTwoSphere → M) (hf : ContMDiff (𝓡 2) (𝓡 n) ∞ f) (p : UnitTwoSphere) :
    ContDiff ℝ ∞ (sphereWeight g alpha f ∘ (chartAt Plane p).symm) := by
  have he : ContDiff ℝ ∞ (m60SphereIntrinsicEnergy g f ∘ (chartAt Plane p).symm) :=
    contMDiff_iff_contDiff.mp ((m60SphereIntrinsicEnergy_contMDiff g f hf).comp
      (suSphereChart_smooth p))
  apply ContDiff.rpow_const_of_ne (contDiff_const.add (contDiff_const.mul he))
  intro z
  have hn := m60SphereIntrinsicEnergy_nonneg g f ((chartAt Plane p).symm z)
  positivity

private theorem sphereWeight_chart_energy (g : RiemannianMetric n M) (alpha : ℝ)
    (f : UnitTwoSphere → M) (hf : ContMDiff (𝓡 2) (𝓡 n) ∞ f) (p : UnitTwoSphere) :
    (fun z => (1 + 2 * m60EnergyDensity g (f ∘ (chartAt Plane p).symm) z /
      suAlphaRoundFactor z) ^ (alpha - 1)) =
      sphereWeight g alpha f ∘ (chartAt Plane p).symm := by
  funext z
  rw [suSphereChart_energy g f (hf.of_le (by simp))]
  change (1 + 2 * (m60SphereIntrinsicEnergy g f ((chartAt Plane p).symm z) *
      suAlphaRoundFactor z) / suAlphaRoundFactor z) ^ (alpha - 1) = _
  rw [← mul_assoc, mul_div_cancel_right₀ _ (suRoundFactor_smooth_pos.2 z).ne']
  rfl

theorem suWeakAlphaSphere_weightedEuler
    {g : RiemannianMetric n M} {eps0 alpha : ℝ} (S : SUWeakAlphaSphere g eps0 alpha)
    (hf : ContMDiff (𝓡 2) (𝓡 n) ∞ S.map) : SUSphereWeightedEuler g alpha S.map := by
  intro p b z hb
  let cp := chartAt Plane p
  let q := cp.symm z
  let cq := chartAt Plane q
  let f := S.map
  let w := sphereWeight g alpha f
  let v := f ∘ cp.symm
  let u := extChartAt (𝓡 n) b ∘ v
  let uq := extChartAt (𝓡 n) b ∘ f ∘ cq.symm
  let t := cq ∘ cp.symm
  let Gamma := christoffelBilinear (g.pullbackCoefficients (extChartAt (𝓡 n) b).symm)
  have hq : q ∈ cq.source := mem_chart_source Plane q
  have htq : t z = cq q := rfl
  have hqt : cq.symm (t z) = q := cq.left_inv hq
  have hsmooth : ContDiffAt ℝ ∞ (suAlphaChartCoordinate (n := n) f q) (cq q) := by
    apply contMDiffAt_iff_contDiffAt.mp
    have he : f (cq.symm (cq q)) = f q := congrArg f (cq.left_inv hq)
    exact (contMDiffAt_extChartAt' (x := f q) (n := ∞) (by
      change f (cq.symm (cq q)) ∈ (chartAt E (f q)).source
      rw [he]; exact mem_chart_source _ _)).comp _ ((hf.comp (suSphereChart_smooth q)) (cq q))
  have hlocal := suWeakAlphaCoordinate_weightedEuler_of_smooth (S.chart q).coordinateData
    S.alpha_mem.1.le hsmooth
  let u0 := extChartAt (𝓡 n) (f q) ∘ f ∘ cq.symm
  have hweight : (fun y => (1 + (∑ i : Fin 2,
      g.pullbackCoefficients (extChartAt (𝓡 n) (f q)).symm (u0 y)
        (fderiv ℝ u0 y (e i)) (fderiv ℝ u0 y (e i))) /
      suAlphaRoundFactor y) ^ (alpha - 1)) =ᶠ[𝓝 (t z)] w ∘ cq.symm := by
    have hy0 : f (cq.symm (t z)) ∈ (extChartAt (𝓡 n) (f q)).source := by
      rw [hqt]; exact mem_extChartAt_source _
    filter_upwards [(hf.comp (suSphereChart_smooth q)).continuous.continuousAt
      ((isOpen_extChartAt_source (f q)).mem_nhds hy0)] with y hy
    have he := m60EnergyDensity_eq_chart g (f q)
      ((hf.comp (suSphereChart_smooth q)).mdifferentiable (by simp) y) hy
    have hwgt := congrFun (sphereWeight_chart_energy g alpha f hf q) y
    dsimp only [Function.comp_apply, w, sphereWeight] at hwgt ⊢
    rw [he] at hwgt
    change (1 + 2 * ((1 / 2 : ℝ) * (∑ i : Fin 2,
      g.pullbackCoefficients (extChartAt (𝓡 n) (f q)).symm (u0 y)
        (fderiv ℝ u0 y (e i)) (fderiv ℝ u0 y (e i)))) / suAlphaRoundFactor y) ^
      (alpha - 1) = _ at hwgt
    simpa only [← mul_assoc, show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_mul] using hwgt
  have heq0 : (∑ i : Fin 2, covDerivAlong
      (christoffelBilinear (g.pullbackCoefficients (extChartAt (𝓡 n) (f q)).symm)) u0
      (fun y => w (cq.symm y) • fderiv ℝ u0 y (e i)) (e i) (t z)) = 0 := by
    change (∑ i : Fin 2, covDerivAlong
      (christoffelBilinear (g.pullbackCoefficients (extChartAt (𝓡 n) (f q)).symm)) u0
      (fun y => (1 + (∑ j : Fin 2,
        g.pullbackCoefficients (extChartAt (𝓡 n) (f q)).symm (u0 y)
          (fderiv ℝ u0 y (e j)) (fderiv ℝ u0 y (e j))) /
        suAlphaRoundFactor y) ^ (alpha - 1) • fderiv ℝ u0 y (e i)) (e i) (t z)) = 0 at hlocal
    convert hlocal using 1
    apply Finset.sum_congr rfl
    intro i _
    exact covDerivAlong_congr _ u0
      (hweight.symm.mono fun y hy => congrArg (fun a : ℝ => a • fderiv ℝ u0 y (e i)) hy) (e i)
  have heqb := weighted_target_change g (f ∘ cq.symm) (hf.comp (suSphereChart_smooth q))
    (w ∘ cq.symm) (sphereWeight_chart_smooth g alpha f hf q) (f q) b (t z)
    (by rw [Function.comp_apply, hqt]; exact mem_extChartAt_source _)
    (by simpa only [Function.comp_apply, hqt, q, cp] using hb) heq0
  obtain ⟨ht, a, ha, hgram, hlap⟩ := sphere_transition p q z hq
  have huq : ContDiffAt ℝ ∞ uq (t z) := contMDiffAt_iff_contDiffAt.mp
    ((contMDiffAt_extChartAt' (x := b) (n := ∞) (by
      simpa only [Function.comp_apply, hqt, q, cp, extChartAt_source] using hb)).comp _
        ((hf.comp (suSphereChart_smooth q)) (t z)))
  have heqc := weighted_source_change Gamma (w ∘ cq.symm)
    (huq.of_le (WithTop.coe_le_coe.mpr le_top))
    (ht.of_le (WithTop.coe_le_coe.mpr le_top))
    ((sphereWeight_chart_smooth g alpha f hf q).differentiable (by simp) _) ha hgram hlap heqb
  have hinv : cq.symm ∘ t =ᶠ[𝓝 z] cp.symm := by
    filter_upwards [(suSphereChart_smooth p).continuous.continuousAt
      (cq.open_source.mem_nhds hq)] with y hy
    exact cq.left_inv hy
  have hugerm : uq ∘ t =ᶠ[𝓝 z] u :=
    hinv.mono fun y hy => congrArg (fun p => extChartAt (𝓡 n) b (f p)) hy
  have hwgerm : (fun y => w (cq.symm (t y))) =ᶠ[𝓝 z] w ∘ cp.symm :=
    hinv.mono fun y hy => congrArg w hy
  change (∑ i : Fin 2, covDerivAlong Gamma u
    (fun y => (1 + 2 * m60EnergyDensity g v y / suAlphaRoundFactor y) ^ (alpha - 1) •
      fderiv ℝ u y (e i)) (e i) z) = 0
  have hwe (y : Plane) :
      (1 + 2 * m60EnergyDensity g v y / suAlphaRoundFactor y) ^ (alpha - 1) =
        w (cp.symm y) := congrFun (sphereWeight_chart_energy g alpha f hf p) y
  simp_rw [hwe]
  convert heqc using 1
  apply Finset.sum_congr rfl
  intro i _
  rw [covDerivAlong_congr_base Gamma _ hugerm]
  apply covDerivAlong_congr Gamma u _ (e i)
  filter_upwards [hwgerm, hugerm.fderiv (𝕜 := ℝ)] with y hy hdy
  simp only [Function.comp_apply] at hy ⊢
  rw [hy, hdy]

theorem suSmoothAlphaMinimizingSequence_of_regular [CompactSpace M] [T2Space M]
    (g : RiemannianMetric n M) (x : M) (hpi : Nontrivial (HomotopyGroup.Pi 2 M x))
    (eps0 : ℝ) (heps : 0 < eps0)
    (regular : ∀ (alpha : ℝ) (S : SUWeakAlphaSphere g eps0 alpha),
      ContMDiff (𝓡 2) (𝓡 n) ∞ S.map) :
    ∃ (alpha : ℕ → ℝ) (f : ℕ → UnitTwoSphere → M),
      Tendsto alpha atTop (𝓝 1) ∧
      (∀ j, 1 ≤ alpha j ∧ alpha j ≤ 33 / 32) ∧
      (∀ j, ContMDiff (𝓡 2) (𝓡 n) ∞ (f j)) ∧
      (∀ j, ¬ IsNullHomotopicSphere (f j)) ∧
      (∀ j (h : UnitTwoSphere → M), ContMDiff (𝓡 2) (𝓡 n) ∞ h →
        ¬ IsNullHomotopicSphere h →
        m60SphereAlphaEnergy g (alpha j) (f j) ≤ m60SphereAlphaEnergy g (alpha j) h) ∧
      (∀ j, SUSphereWeightedEuler g (alpha j) (f j)) ∧
      ∀ j, m60SphereAlphaEnergy g (alpha j) (f j) =
        sInf (m60NonNullAlphaEnergyValues g (alpha j)) := by
  let : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact E M
  let d := min eps0 (1 / 32 : ℝ) / 2
  have hd : 0 < d := div_pos (lt_min heps (by norm_num)) (by norm_num)
  have hde : d < eps0 := by
    have hm := min_le_left eps0 (1 / 32 : ℝ)
    dsimp only [d]
    linarith
  have hd32 : d ≤ 1 / 32 := by
    have hm := min_le_right eps0 (1 / 32 : ℝ)
    dsimp only [d]
    linarith
  let alpha := fun j : ℕ => 1 + d / ((j : ℝ) + 1)
  have hdiv (j : ℕ) : 0 < d / ((j : ℝ) + 1) ∧ d / ((j : ℝ) + 1) ≤ d :=
    ⟨div_pos hd (by positivity), div_le_self hd.le (by linarith [Nat.cast_nonneg (α := ℝ) j])⟩
  have hmem (j : ℕ) : alpha j ∈ Ioo 1 (1 + eps0) :=
    ⟨by dsimp [alpha]; linarith [(hdiv j).1],
      by dsimp [alpha]; linarith [(hdiv j).2]⟩
  have hrange (j : ℕ) : 1 ≤ alpha j ∧ alpha j ≤ 33 / 32 :=
    ⟨(hmem j).1.le, by dsimp [alpha]; linarith [(hdiv j).2]⟩
  choose S hSn hSE using fun j => m60_exists_weakAlphaSphere g x hpi (hmem j)
    (by linarith [(hrange j).2] : alpha j ≤ 2)
  have hs (j : ℕ) := regular (alpha j) (S j)
  refine ⟨alpha, fun j => (S j).map, ?_, hrange, hs, hSn, ?_, ?_, fun j => hSE j (hs j)⟩
  · have ht : Tendsto (fun j : ℕ => 1 + d * (1 / ((j : ℝ) + 1))) atTop
        (𝓝 (1 + d * 0)) := tendsto_const_nhds.add
      (tendsto_const_nhds.mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
    convert ht using 1 <;> simp only [alpha, mul_zero, add_zero, mul_one_div]
  · intro j h hh hn
    rw [hSE j (hs j)]
    exact csInf_le (m60NonNullAlphaEnergyValues_bddBelow g (alpha j)) ⟨h, hh, hn, rfl⟩
  · intro j
    exact suWeakAlphaSphere_weightedEuler (S j) (hs j)

theorem suSmoothAlphaMinimizingSequence [CompactSpace M] [T2Space M]
    (g : RiemannianMetric n M) (x : M) (hpi : Nontrivial (HomotopyGroup.Pi 2 M x)) :
    ∃ (alpha : ℕ → ℝ) (f : ℕ → UnitTwoSphere → M),
      Tendsto alpha atTop (𝓝 1) ∧
      (∀ j, 1 ≤ alpha j ∧ alpha j ≤ 33 / 32) ∧
      (∀ j, ContMDiff (𝓡 2) (𝓡 n) ∞ (f j)) ∧
      (∀ j, ¬ IsNullHomotopicSphere (f j)) ∧
      (∀ j (h : UnitTwoSphere → M), ContMDiff (𝓡 2) (𝓡 n) ∞ h →
        ¬ IsNullHomotopicSphere h →
        m60SphereAlphaEnergy g (alpha j) (f j) ≤ m60SphereAlphaEnergy g (alpha j) h) ∧
      (∀ j, SUSphereWeightedEuler g (alpha j) (f j)) ∧
      ∀ j, m60SphereAlphaEnergy g (alpha j) (f j) =
        sInf (m60NonNullAlphaEnergyValues g (alpha j)) := by
  obtain ⟨eps0, heps, regular⟩ := suWeakAlphaSphere_smooth g
  exact suSmoothAlphaMinimizingSequence_of_regular g x hpi eps0 heps regular

end PoincareConjecture.M60
