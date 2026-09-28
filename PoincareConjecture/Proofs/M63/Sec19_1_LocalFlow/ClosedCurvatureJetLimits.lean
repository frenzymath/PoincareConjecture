import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.EmbeddedCurvatureJetSpatial
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.C2TraceEmbeddingBounds
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.MixedEmbeddingHessian
import PoincareConjecture.Proofs.M63.Mathlib.SmoothRetractionDifferentials
import PoincareConjecture.Proofs.M63.Mathlib.PeriodicDerivativeConvergence
import PoincareConjecture.Proofs.M63.Mathlib.CompactPathDerivative
import PoincareConjecture.Proofs.M08.SecondVariationCoordinates
import Mathlib.Analysis.Calculus.Deriv.Shift










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology NNReal

universe u v

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {ι : Type v} [Fintype ι] {a b : ℝ}

local notation "W" => EuclideanSpace ℝ ι
local notation "X" => C(AddCircle curvePeriod, W)
local notation "XR" => C(AddCircle curvePeriod, ℝ)

set_option maxHeartbeats 800000 in




theorem exists_closed_embeddedCurvatureJet_limits
    [T2Space M] (F : RicciFlow n M (Icc a b)) (hcompact : IsCompact (univ : Set M))
    {tau s : ℝ} (hat : a < tau) (hts : tau < s) (hsb : s < b)
    {e : M → W} (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e)
    {U : Set W} (hU : IsOpen U) (heU : range e ⊆ U) {ρ : W → M}
    (hρ : ContMDiffOn 𝓘(ℝ, W) (𝓡 n) ∞ ρ U) (hρe : ∀ p, ρ (e p) = p)
    (c : ℕ → ℝ → ℝ → M) (hc : ∀ j, M62ShrinkingCurve F (c j))
    (R S H : ℕ → C(Icc tau s, X)) (V : ℕ → C(Icc tau s, XR))
    (r sigma h : C(Icc tau s, X)) (v : C(Icc tau s, XR))
    (hR : Tendsto R atTop (𝓝 r)) (hS : Tendsto S atTop (𝓝 sigma))
    (hH : Tendsto H atTop (𝓝 h)) (hV : Tendsto V atTop (𝓝 v))
    (hRrep : ∀ j (t : Icc tau s) (x : ℝ),
      R j t (x : AddCircle curvePeriod) = e (c j x t))
    (hSrep : ∀ j (t : Icc tau s) (x : ℝ), S j t (x : AddCircle curvePeriod) =
      mfderiv (𝓡 n) 𝓘(ℝ, W) e (c j x t) (spatialUnitTangent F (c j) t x))
    (hHrep : ∀ j (t : Icc tau s) (x : ℝ), H j t (x : AddCircle curvePeriod) =
      mfderiv (𝓡 n) 𝓘(ℝ, W) e (c j x t) (m62CurvatureVector F (c j) t x))
    (hVrep : ∀ j (t : Icc tau s) (x : ℝ),
      V j t (x : AddCircle curvePeriod) = curveSpeed F (c j) t x)
    (hrU : ∀ (t : Icc tau s) z, r t z ∈ U)
    (hvpos : ∀ (t : Icc tau s) z, 0 < v t z)
    (hjets : ∀ i : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ j (t : Icc tau s) (x : ℝ),
      (F.metric t).tangentNorm (c j x t) (m63CurvatureJet F (c j) i t x) ≤ K)
    (hspeed : ∃ V1 : ℝ, 0 ≤ V1 ∧ ∀ j (t : Icc tau s) (x : ℝ),
      |curveSpeed F (c j) t x| + |deriv (curveSpeed F (c j) t) x| ≤ V1) :
    ∃ (G : ℕ → ℕ → C(Icc tau s, X)) (η : ℕ → C(Icc tau s, X)),
      η 0 = h ∧
      (∀ i j (t : Icc tau s) (x : ℝ), G i j t (x : AddCircle curvePeriod) =
        mfderiv (𝓡 n) 𝓘(ℝ, W) e (c j x t) (m63CurvatureJet F (c j) i t x)) ∧
      (∀ i, Tendsto (G i) atTop (𝓝 (η i))) ∧
      ∀ i (t : Icc tau s) (x : ℝ),
        HasDerivAt (fun y : ℝ => η i t (y : AddCircle curvePeriod))
          (v t (x : AddCircle curvePeriod) •
            (η (i + 1) t (x : AddCircle curvePeriod) +
              coordinateHessian (F.connection t) e (ρ (r t (x : AddCircle curvePeriod)))
                (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (r t (x : AddCircle curvePeriod))
                  (sigma t (x : AddCircle curvePeriod)))
                (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (r t (x : AddCircle curvePeriod))
                  (η i t (x : AddCircle curvePeriod))))) x := by
  classical
  let : Fact (0 < curvePeriod) := ⟨by unfold curvePeriod; positivity⟩
  let C := Icc tau s
  let : Nonempty C := ⟨⟨tau, le_rfl, hts.le⟩⟩
  let Y := C × AddCircle curvePeriod
  let Path := C(C, X)
  let E := C(C, W)
  let B := fun (t : ℝ) (z p q : W) => coordinateHessian (F.connection t) e (ρ z)
    (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z p) (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z q)
  let A : ℕ → ℕ → ℝ × ℝ → W := fun i j z =>
    mfderiv (𝓡 n) 𝓘(ℝ, W) e (c j z.1 z.2) (m63CurvatureJet F (c j) i z.2 z.1)
  let Ω : Set (ℝ × ℝ) := univ ×ˢ Ioo a b
  have hΩ : IsOpen Ω := isOpen_univ.prod isOpen_Ioo
  have htime (t : C) : t.1 ∈ Ioo a b :=
    ⟨hat.trans_le t.2.1, t.2.2.trans_lt hsb⟩
  have hpush : ContMDiff ((𝓡 n).prod (𝓡 n)) 𝓘(ℝ, W) ∞
      (fun p : TangentBundle (𝓡 n) M => (mfderiv (𝓡 n) 𝓘(ℝ, W) e p.1 p.2 : W)) :=
    (contMDiff_snd_tangentBundle_modelSpace (n := ∞) W 𝓘(ℝ, W)).comp
      (he.contMDiff_tangentMap (by simp))
  have hA (i j : ℕ) : ContDiffOn ℝ ∞ (A i j) Ω :=
    (hpush.comp_contMDiffOn (curvatureJet_joint_contMDiff F (c j) (hc j) i)).contDiffOn
  have hdx (i j : ℕ) (t : C) (x : ℝ) :
      HasDerivAt (fun y => A i j (y, t)) (M08.coordinatePartialS (A i j) (x, t)) x :=
    M08.coordinateSlice_fst_hasDerivAt (A i j) (p := (x, t))
      (((hA i j).contDiffAt (hΩ.mem_nhds ⟨mem_univ _, htime t⟩)).differentiableAt (by simp))
  obtain ⟨E1, E2, E3, ⟨hE1, hE2, hE3⟩, hE⟩ :=
    exists_uniform_embedding_derivative_bounds F hcompact he
  choose K hK hKbound using hjets
  obtain ⟨V1, hV1, hV1bound⟩ := hspeed
  let bound (i : ℕ) := V1 * (E2 * K i + E1 * K (i + 1)) +
    V1 ^ 2 * (E3 * K i + E2 * K 0 * K i + 2 * E2 * K (i + 1) + E1 * K (i + 2))
  have hbound (i : ℕ) : 0 ≤ bound i := by
    dsimp only [bound]
    exact add_nonneg
      (mul_nonneg hV1 (add_nonneg (mul_nonneg hE2 (hK i))
        (mul_nonneg hE1 (hK (i + 1)))))
      (mul_nonneg (sq_nonneg V1)
        (add_nonneg (add_nonneg (add_nonneg (mul_nonneg hE3 (hK i))
          (mul_nonneg (mul_nonneg hE2 (hK 0)) (hK i)))
          (mul_nonneg (mul_nonneg (by norm_num) hE2) (hK (i + 1))))
          (mul_nonneg hE1 (hK (i + 2)))))
  have hsecond (i j : ℕ) (t : C) (x : ℝ) :
      ‖deriv (deriv (fun y => A i j (y, t))) x‖ ≤ bound i := by
    have ht := Ioo_subset_Icc_self (htime t)
    have hb := embeddedCurvatureJet_second_spatial_derivative_bound F (c j) (hc j) he i
      (htime t) x hE1 hE2 hE3
      (fun Z => (hE t ht (c j x t) Z 0 0).1)
      (fun Z Q => (hE t ht (c j x t) Z Q 0).2.1)
      (fun Z Q P => (hE t ht (c j x t) Z Q P).2.2)
    have hvx : |deriv (curveSpeed F (c j) t) x| ≤ V1 :=
      (le_add_of_nonneg_left (abs_nonneg _)).trans (hV1bound j t x)
    have hv : curveSpeed F (c j) t x ≤ V1 :=
      (le_abs_self _).trans ((le_add_of_nonneg_right (abs_nonneg _)).trans (hV1bound j t x))
    have hv0 : 0 ≤ curveSpeed F (c j) t x := (M62.speed_pos F (c j) (hc j) ht x).le
    have hk : m62Curvature F (c j) t x ≤ K 0 := hKbound 0 j t x
    have hk0 : 0 ≤ m62Curvature F (c j) t x := Real.sqrt_nonneg _
    have hni : 0 ≤ (F.metric t).tangentNorm (c j x t)
        (m63CurvatureJet F (c j) i t x) := Real.sqrt_nonneg _
    have hni1 : 0 ≤ (F.metric t).tangentNorm (c j x t)
        (m63CurvatureJet F (c j) (i + 1) t x) := Real.sqrt_nonneg _
    have hni2 : 0 ≤ (F.metric t).tangentNorm (c j x t)
        (m63CurvatureJet F (c j) (i + 2) t x) := Real.sqrt_nonneg _
    have hE2K0 : 0 ≤ E2 * K 0 := mul_nonneg hE2 (hK 0)
    apply hb.trans
    dsimp only [bound]
    gcongr <;> first
      | exact hvx
      | exact hv
      | exact hk
      | exact hKbound i j t x
      | exact hKbound (i + 1) j t x
      | exact hKbound (i + 2) j t x
  have descend (f : ℝ × ℝ → W) (hf : ContinuousOn f (univ ×ˢ C))
      (hp : ∀ t : C, Function.Periodic (fun x => f (x, t)) curvePeriod) :
      ∃ D : Path, ∀ (t : C) (x : ℝ), D t (x : AddCircle curvePeriod) = f (x, t) := by
    let D : C → X := fun t => ⟨(hp t).lift,
      (QuotientAddGroup.isQuotientMap_mk (AddSubgroup.zmultiples curvePeriod)).continuous_iff.mpr
        (hf.comp_continuous (continuous_id.prodMk continuous_const)
          (fun _ => ⟨mem_univ _, t.2⟩))⟩
    have hDval (t : C) (x : ℝ) : D t (x : AddCircle curvePeriod) = f (x, t) :=
      Function.Periodic.lift_coe (hp t) x
    have hD : Continuous D := by
      apply ContinuousMap.continuous_of_continuous_uncurry
      have hquot : IsOpenQuotientMap
          (fun p : C × ℝ => (p.1, (p.2 : AddCircle curvePeriod))) :=
        IsOpenQuotientMap.id.prodMap QuotientAddGroup.isOpenQuotientMap_mk
      apply hquot.continuous_comp_iff.mp
      have hcomp : Continuous (fun p : C × ℝ => f (p.2, p.1.1)) :=
        hf.comp_continuous (continuous_snd.prodMk (continuous_subtype_val.comp continuous_fst))
          (fun p => ⟨mem_univ _, p.1.2⟩)
      exact hcomp.congr (fun p => (hDval p.1 p.2).symm)
    exact ⟨⟨D, hD⟩, hDval⟩
  let swap0 : C(AddCircle curvePeriod × C, Y) := ⟨Prod.swap, continuous_swap⟩
  let swap1 : C(Y, AddCircle curvePeriod × C) := ⟨Prod.swap, continuous_swap⟩
  let spatial (f : Path) : C(AddCircle curvePeriod, E) := (f.uncurry.comp swap0).curry
  let temporal (f : C(AddCircle curvePeriod, E)) : Path := (f.uncurry.comp swap1).curry
  have hspatial : Continuous spatial := ContinuousMap.continuous_curry.comp
    ((ContinuousMap.continuous_precomp swap0).comp ContinuousMap.continuous_uncurry)
  have htemporal : Continuous temporal := ContinuousMap.continuous_curry.comp
    ((ContinuousMap.continuous_precomp swap1).comp ContinuousMap.continuous_uncurry)
  let D := (C × U) × (W × W)
  have hBC : ContinuousOn
      (fun z : (ℝ × W) × (W × W) => B z.1.1 z.1.2 z.2.1 z.2.2)
      ((Icc a b ×ˢ U) ×ˢ univ) :=
    (flow_coordinateHessian_mixed_pullback_contDiffOn F he hU hρ).continuousOn
  let coefficientInput : D → (ℝ × W) × (W × W) :=
    fun z => ((z.1.1.1, z.1.2.1), z.2)
  have hInput : Continuous coefficientInput :=
    ((continuous_subtype_val.comp continuous_fst.fst).prodMk
      (continuous_subtype_val.comp continuous_fst.snd)).prodMk continuous_snd
  have hInput_mem (z : D) : coefficientInput z ∈ ((Icc a b ×ˢ U) ×ˢ univ) :=
    ⟨⟨Ioo_subset_Icc_self (htime z.1.1), z.1.2.2⟩, mem_univ _⟩
  let BC : C(D, W) := ⟨fun z => B z.1.1 z.1.2 z.2.1 z.2.2,
    hBC.comp_continuous (f := coefficientInput) hInput hInput_mem⟩
  have hRU (j : ℕ) (y : Y) : (R j).uncurry y ∈ U := by
    obtain ⟨x, hx⟩ := QuotientAddGroup.mk_surjective y.2
    change R j y.1 y.2 ∈ U
    rw [← hx, hRrep]
    exact heU (mem_range_self _)
  let Rn (j : ℕ) : C(Y, U) :=
    ⟨fun y => ⟨(R j).uncurry y, hRU j y⟩, (R j).uncurry.continuous.subtype_mk _⟩
  let r0 : C(Y, U) :=
    ⟨fun y => ⟨r.uncurry y, hrU y.1 y.2⟩, r.uncurry.continuous.subtype_mk _⟩
  let inc : C(U, W) := ⟨Subtype.val, continuous_subtype_val⟩
  have hRn : Tendsto Rn atTop (𝓝 r0) := by
    apply (inc.isEmbedding_postcomp Topology.IsEmbedding.subtypeVal).tendsto_nhds_iff.mpr
    exact (ContinuousMap.continuous_uncurry.tendsto r).comp hR
  have hSn := (ContinuousMap.continuous_uncurry.tendsto sigma).comp hS
  let bundle (q : C(Y, U) × (C(Y, W) × C(Y, W))) : C(Y, D) :=
    ((ContinuousMap.fst : C(Y, C)).prodMk q.1).prodMk (q.2.1.prodMk q.2.2)
  have hbundle : Continuous bundle := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact ((continuous_fst.comp continuous_snd).prodMk
      (continuous_fst.fst.eval continuous_snd)).prodMk
      ((continuous_fst.snd.fst.eval continuous_snd).prodMk
        (continuous_fst.snd.snd.eval continuous_snd))
  let P := {z : ℝ // 0 < z}
  have hVpos (j : ℕ) (y : Y) : 0 < (V j).uncurry y := by
    obtain ⟨x, hx⟩ := QuotientAddGroup.mk_surjective y.2
    change 0 < V j y.1 y.2
    rw [← hx, hVrep]
    exact M62.speed_pos F (c j) (hc j) (Ioo_subset_Icc_self (htime y.1)) x
  let Vn (j : ℕ) : C(Y, P) :=
    ⟨fun y => ⟨(V j).uncurry y, hVpos j y⟩, (V j).uncurry.continuous.subtype_mk _⟩
  let v0 : C(Y, P) := ⟨fun y => ⟨v.uncurry y, hvpos y.1 y.2⟩,
    v.uncurry.continuous.subtype_mk _⟩
  let incP : C(P, ℝ) := ⟨Subtype.val, continuous_subtype_val⟩
  have hVn : Tendsto Vn atTop (𝓝 v0) := by
    apply (incP.isEmbedding_postcomp Topology.IsEmbedding.subtypeVal).tendsto_nhds_iff.mpr
    exact (ContinuousMap.continuous_uncurry.tendsto v).comp hV
  let reciprocal : C(P, ℝ) := ⟨fun z => (z.1)⁻¹,
    continuous_subtype_val.inv₀ (fun z => z.2.ne')⟩
  let IV (j : ℕ) : C(Y, ℝ) := reciprocal.comp (Vn j)
  let iv : C(Y, ℝ) := reciprocal.comp v0
  have hIV : Tendsto IV atTop (𝓝 iv) := (reciprocal.continuous_postcomp.tendsto _).comp hVn
  let mulV (q : C(Y, ℝ) × C(Y, W)) : C(Y, W) :=
    ⟨fun y => q.1 y • q.2 y, q.1.continuous.smul q.2.continuous⟩
  have hmulV : Continuous mulV := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    have hscalar : Continuous (fun z : (C(Y, ℝ) × C(Y, W)) × Y => z.1.1 z.2) :=
      continuous_fst.fst.eval continuous_snd
    have hvector : Continuous (fun z : (C(Y, ℝ) × C(Y, W)) × Y => z.1.2 z.2) :=
      continuous_fst.snd.eval continuous_snd
    exact hscalar.smul hvector
  have hleft := (smooth_retraction_differentials he hU heU hρ hρe).2.2
  let State (i : ℕ) := {p : (ℕ → Path) × Path //
    (∀ j (t : C) (x : ℝ), p.1 j t (x : AddCircle curvePeriod) = A i j (x, t)) ∧
      Tendsto p.1 atTop (𝓝 p.2)}
  have step (i : ℕ) (Q : State i) : ∃ Q' : State (i + 1),
      ∀ (t : C) (x : ℝ), HasDerivAt (fun y : ℝ => Q.1.2 t (y : AddCircle curvePeriod))
        (v t (x : AddCircle curvePeriod) •
          (Q'.1.2 t (x : AddCircle curvePeriod) +
            B t (r t (x : AddCircle curvePeriod)) (sigma t (x : AddCircle curvePeriod))
              (Q.1.2 t (x : AddCircle curvePeriod)))) x := by
    let G := Q.1.1
    let g := Q.1.2
    have hGrep := Q.2.1
    have hGlim := Q.2.2
    let DX (j : ℕ) := M08.coordinatePartialS (A i j)
    have hDX (j : ℕ) : ContDiffOn ℝ ∞ (DX j) Ω :=
      M08.coordinatePartialS_contDiffOn hΩ (A i j) (hA i j)
    have hXeq (j : ℕ) (t : C) :
        (fun x => DX j (x, t)) = deriv (fun x => A i j (x, t)) :=
      funext fun x => (hdx i j t x).deriv.symm
    have hper (j : ℕ) (t : C) : Function.Periodic (fun x => DX j (x, t)) curvePeriod := by
      rw [hXeq]
      have hp : Function.Periodic (fun x => A i j (x, t)) curvePeriod := by
        intro x
        change A i j (x + curvePeriod, t) = A i j (x, t)
        rw [← hGrep j t (x + curvePeriod), ← hGrep j t x, AddCircle.coe_add_period]
      intro x
      rw [← deriv_comp_add_const]
      exact congrArg (fun f : ℝ → W => deriv f x) (funext hp)
    have hDn (j : ℕ) : ∃ Dn : Path, ∀ (t : C) (x : ℝ),
        Dn t (x : AddCircle curvePeriod) = DX j (x, t) :=
      descend (DX j) ((hDX j).continuousOn.mono
        (fun z hz => ⟨mem_univ _, htime ⟨z.2, hz.2⟩⟩)) (hper j)
    choose Dn hDrep using hDn
    have hder (j : ℕ) (x : ℝ) : HasDerivAt
        (fun y : ℝ => spatial (G j) (y : AddCircle curvePeriod))
        (spatial (Dn j) (x : AddCircle curvePeriod)) x := by
      apply hasDerivAt_compact_curry isOpen_univ _ _ (mem_univ x)
        ((spatial (Dn j)).continuous.comp (AddCircle.continuous_mk' curvePeriod)).continuousAt
      intro y _hy t
      change HasDerivAt (fun z : ℝ => G j t (z : AddCircle curvePeriod))
        (Dn j t (y : AddCircle curvePeriod)) y
      rw [hDrep]
      exact (hdx i j t y).congr_of_eventuallyEq (Eventually.of_forall (hGrep j t))
    have hpointLip (j : ℕ) (t : C) : LipschitzWith (⟨bound i, hbound i⟩ : ℝ≥0)
        (fun x => DX j (x, t)) := by
      have hs : ContDiff ℝ ∞ (fun x => DX j (x, t)) :=
        (hDX j).comp_contDiff (contDiff_id.prodMk contDiff_const)
          (fun _ => ⟨mem_univ _, htime t⟩)
      apply lipschitzWith_of_nnnorm_deriv_le (hs.differentiable (by simp))
      intro x
      change ‖deriv (fun y => DX j (y, t)) x‖ ≤ bound i
      rw [hXeq]
      exact hsecond i j t x
    have hLip (j : ℕ) : LipschitzWith (⟨bound i, hbound i⟩ : ℝ≥0)
        (fun x : ℝ => spatial (Dn j) (x : AddCircle curvePeriod)) := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      apply (ContinuousMap.dist_le (mul_nonneg (hbound i) dist_nonneg)).mpr
      intro t
      change dist (Dn j t (x : AddCircle curvePeriod)) (Dn j t (y : AddCircle curvePeriod)) ≤ _
      rw [hDrep, hDrep]
      exact (hpointLip j t).dist_le_mul x y
    obtain ⟨dg, hdg, hderg⟩ := exists_periodic_derivative_limit
      (fun j => spatial (G j)) (fun j => spatial (Dn j)) (spatial g) hder hLip
      ((hspatial.tendsto g).comp hGlim)
    let d0 := temporal dg
    have hDlim : Tendsto Dn atTop (𝓝 d0) := (htemporal.tendsto dg).comp hdg
    let Bn (j : ℕ) : C(Y, W) := BC.comp (bundle (Rn j, (S j).uncurry, (G j).uncurry))
    let b0 : C(Y, W) := BC.comp (bundle (r0, sigma.uncurry, g.uncurry))
    have hBn : Tendsto Bn atTop (𝓝 b0) :=
      (BC.continuous_postcomp.tendsto _).comp ((hbundle.tendsto _).comp
        (hRn.prodMk_nhds (hSn.prodMk_nhds
          ((ContinuousMap.continuous_uncurry.tendsto g).comp hGlim))))
    let Gn (j : ℕ) : C(Y, W) := mulV (IV j, (Dn j).uncurry) - Bn j
    let g0 : C(Y, W) := mulV (iv, d0.uncurry) - b0
    have hGn : Tendsto Gn atTop (𝓝 g0) :=
      ((hmulV.tendsto _).comp (hIV.prodMk_nhds
        ((ContinuousMap.continuous_uncurry.tendsto d0).comp hDlim))).sub hBn
    have hBactual (j : ℕ) (t : C) (x : ℝ) :
        B t (R j t (x : AddCircle curvePeriod)) (S j t (x : AddCircle curvePeriod))
          (G j t (x : AddCircle curvePeriod)) =
          coordinateHessian (F.connection t) e (c j x t)
            (spatialUnitTangent F (c j) t x) (m63CurvatureJet F (c j) i t x) := by
      dsimp only [B]
      rw [hRrep, hSrep, hGrep]
      dsimp only [A]
      erw [hleft (c j x t) (spatialUnitTangent F (c j) t x),
        hleft (c j x t) (m63CurvatureJet F (c j) i t x), hρe (c j x t)]
    have hDnext (j : ℕ) (t : C) (x : ℝ) : Dn j t (x : AddCircle curvePeriod) =
        V j t (x : AddCircle curvePeriod) •
          (A (i + 1) j (x, t) + B t (R j t (x : AddCircle curvePeriod))
            (S j t (x : AddCircle curvePeriod)) (G j t (x : AddCircle curvePeriod))) := by
      rw [hDrep, hVrep, hBactual]
      exact (hdx i j t x).unique
        (hasDerivAt_embeddedCurvatureJet_spatial F (c j) (hc j) he i (htime t) x)
    have hGnext (j : ℕ) (t : C) (x : ℝ) :
        (Gn j).curry t (x : AddCircle curvePeriod) = A (i + 1) j (x, t) := by
      change (V j t (x : AddCircle curvePeriod))⁻¹ • Dn j t (x : AddCircle curvePeriod) -
        B t (R j t (x : AddCircle curvePeriod)) (S j t (x : AddCircle curvePeriod))
          (G j t (x : AddCircle curvePeriod)) = _
      have hvj : V j t (x : AddCircle curvePeriod) ≠ 0 :=
        (hVpos j (t, (x : AddCircle curvePeriod))).ne'
      rw [hDnext, smul_smul, inv_mul_cancel₀ hvj, one_smul, add_sub_cancel_right]
    refine ⟨⟨(fun j => (Gn j).curry, g0.curry), hGnext,
      (ContinuousMap.continuous_curry.tendsto g0).comp hGn⟩, ?_⟩
    intro t x
    have hd := (ContinuousMap.evalCLM ℝ t).hasFDerivAt.comp_hasDerivAt x (hderg x)
    apply hd.congr_deriv
    change dg (x : AddCircle curvePeriod) t = v t (x : AddCircle curvePeriod) •
      ((v t (x : AddCircle curvePeriod))⁻¹ • dg (x : AddCircle curvePeriod) t -
        B t (r t (x : AddCircle curvePeriod)) (sigma t (x : AddCircle curvePeriod))
          (g t (x : AddCircle curvePeriod)) +
        B t (r t (x : AddCircle curvePeriod)) (sigma t (x : AddCircle curvePeriod))
          (g t (x : AddCircle curvePeriod)))
    rw [sub_add_cancel, smul_smul, mul_inv_cancel₀ (hvpos t (x : AddCircle curvePeriod)).ne',
      one_smul]
  choose next hnext using step
  let initial : State 0 := ⟨(H, h), hHrep, hH⟩
  let seq : (i : ℕ) → State i := fun i => Nat.rec (motive := State) initial
    (fun j p => next j p) i
  exact ⟨fun i => (seq i).1.1, fun i => (seq i).1.2, rfl,
    fun i => (seq i).2.1, fun i => (seq i).2.2, fun i => hnext i (seq i)⟩

end PoincareConjecture.M63
