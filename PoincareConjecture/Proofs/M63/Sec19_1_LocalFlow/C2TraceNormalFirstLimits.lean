import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.PullbackMetricHessian
import PoincareConjecture.Proofs.M63.Mathlib.SmoothRetractionDifferentials
import PoincareConjecture.Proofs.M63.Sec19_2_CurveEstimates.RelabelingGeometry
import Mathlib.Topology.ContinuousMap.Compact










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u v

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {ι : Type v} [Fintype ι] {a b L S : ℝ}

local notation "W" => EuclideanSpace ℝ ι
local notation "X" => C(AddCircle L, W)
local notation "XR" => C(AddCircle L, ℝ)
local notation "Y" => C(AddCircle curvePeriod, W)




theorem exists_closed_normal_value_unitTangent_limits
    [Fact (0 < L)]
    (F : RicciFlow n M (Icc a b)) (_hS : 0 < S) (hab : a + S ≤ b)
    {e : M → W} (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e)
    {U : Set W} (hU : IsOpen U) (heU : range e ⊆ U) {ρ : W → M}
    (hρ : ContMDiffOn 𝓘(ℝ, W) (𝓡 n) ∞ ρ U) (hρe : ∀ z, ρ (e z) = z)
    (Q P : ℕ → C(Icc (0 : ℝ) S, X)) (q p : C(Icc (0 : ℝ) S, X))
    (D : ℕ → C(Icc (0 : ℝ) S, XR)) (d : C(Icc (0 : ℝ) S, XR))
    (psi : ℕ → ℝ → ℝ → ℝ) (c : ℕ → ℝ → ℝ → M)
    (hQ : Tendsto Q atTop (𝓝 q)) (hP : Tendsto P atTop (𝓝 p))
    (hD : Tendsto D atTop (𝓝 d))
    (hder : ∀ j (t : Icc (0 : ℝ) S) (x : ℝ),
      HasDerivAt (fun y : ℝ => Q j t (y : AddCircle L)) (P j t (x : AddCircle L)) x)
    (hguard : ∀ j (t : Icc (0 : ℝ) S) z, Q j t z ∈ U ∧
      mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (Q j t z) (P j t z) ≠ 0)
    (hguard0 : ∀ (t : Icc (0 : ℝ) S) z, q t z ∈ U ∧
      mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (q t z) (p t z) ≠ 0)
    (hfixed : ∀ j (t : Icc (0 : ℝ) S) z, Q j t z = e (ρ (Q j t z)))
    (hpsi : ∀ j (t : Icc (0 : ℝ) S), ContDiff ℝ 1 (psi j t))
    (hpos : ∀ j (t : Icc (0 : ℝ) S) x, 0 < deriv (psi j t) x)
    (hDrep : ∀ j (t : Icc (0 : ℝ) S) (x : ℝ),
      D j t (x : AddCircle L) = psi j t x - x)
    (hslice : ∀ j (t : Icc (0 : ℝ) S) x,
      c j x (a + t) = ρ (Q j t ((psi j t ((L / curvePeriod) * x) : ℝ) : AddCircle L))) :
    ∃ (R Sfield : ℕ → C(Icc (0 : ℝ) S, Y)) (r s : C(Icc (0 : ℝ) S, Y)),
      Tendsto R atTop (𝓝 r) ∧ Tendsto Sfield atTop (𝓝 s) ∧
      (∀ j (t : Icc (0 : ℝ) S) (x : ℝ),
        R j t (x : AddCircle curvePeriod) = e (c j x (a + t))) ∧
      (∀ j (t : Icc (0 : ℝ) S) (x : ℝ), Sfield j t (x : AddCircle curvePeriod) =
        mfderiv (𝓡 n) 𝓘(ℝ, W) e (c j x (a + t))
          (spatialUnitTangent F (c j) (a + t) x)) ∧
      ∀ (t : Icc (0 : ℝ) S) (x : ℝ),
        let y : AddCircle L := ((L / curvePeriod) * x +
          d t (((L / curvePeriod) * x : ℝ) : AddCircle L) : ℝ)
        let z := q t y
        let v := mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z (p t y)
        let ell := Real.sqrt ((F.metric (a + t)).inner (ρ z) v v)
        r t (x : AddCircle curvePeriod) = z ∧
          s t (x : AddCircle curvePeriod) = ell⁻¹ • p t y := by
  classical
  let : Fact (0 < curvePeriod) := ⟨by unfold curvePeriod; positivity⟩
  let κ := L / curvePeriod
  have hκ : 0 < κ := div_pos (Fact.out : 0 < L) (Fact.out : 0 < curvePeriod)
  let Z := Icc (0 : ℝ) S × AddCircle L
  let Ω : Set (W × W) := {z | z.1 ∈ U ∧ mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z.1 z.2 ≠ 0}
  let A := Icc a b × Ω
  have hmetric := (flow_pullback_metric_hessian_contDiffOn F hU hρ
    (f := fun _ => 0) contMDiff_const).1.continuousOn
  have hmap : Continuous (fun z : A => ((z.1.1, z.2.1.1), z.2.1.2)) :=
    ((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd).fst).prodMk
      (continuous_subtype_val.comp continuous_snd).snd
  have hsq : Continuous (fun z : A => (F.metric z.1).inner (ρ z.2.1.1)
      (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z.2.1.1 z.2.1.2)
      (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z.2.1.1 z.2.1.2)) :=
    hmetric.comp_continuous hmap (fun z => ⟨⟨z.1.2, z.2.2.1⟩, mem_univ _⟩)
  let N : C(A, W) := ⟨fun z =>
    (Real.sqrt ((F.metric z.1).inner (ρ z.2.1.1)
      (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z.2.1.1 z.2.1.2)
      (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z.2.1.1 z.2.1.2)))⁻¹ • z.2.1.2,
    (hsq.sqrt.inv₀ (fun z =>
      (Real.sqrt_pos.mpr ((F.metric z.1).pos _ _ z.2.2.2)).ne')).smul
        (continuous_subtype_val.comp continuous_snd).snd⟩
  let bundle (w : C(Z, W) × C(Z, W)) : C(Z, W × W) := w.1.prodMk w.2
  have hbundle : Continuous bundle := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact (continuous_fst.fst.eval continuous_snd).prodMk
      (continuous_fst.snd.eval continuous_snd)
  let J (j : ℕ) : C(Z, W × W) := bundle ((Q j).uncurry, (P j).uncurry)
  let J0 : C(Z, W × W) := bundle (q.uncurry, p.uncurry)
  have hQu := (ContinuousMap.continuous_uncurry.tendsto q).comp hQ
  have hPu := (ContinuousMap.continuous_uncurry.tendsto p).comp hP
  have hDu := (ContinuousMap.continuous_uncurry.tendsto d).comp hD
  have hJ : Tendsto J atTop (𝓝 J0) :=
    (hbundle.tendsto _).comp (hQu.prodMk_nhds hPu)
  let Jn (j : ℕ) : C(Z, Ω) :=
    ⟨fun z => ⟨J j z, hguard j z.1 z.2⟩, (J j).continuous.subtype_mk _⟩
  let j0 : C(Z, Ω) :=
    ⟨fun z => ⟨J0 z, hguard0 z.1 z.2⟩, J0.continuous.subtype_mk _⟩
  let inc : C(Ω, W × W) := ⟨Subtype.val, continuous_subtype_val⟩
  have hJn : Tendsto Jn atTop (𝓝 j0) := by
    apply (inc.isEmbedding_postcomp Topology.IsEmbedding.subtypeVal).tendsto_nhds_iff.mpr
    exact hJ
  have htime (z : Z) : a + (z.1 : ℝ) ∈ Icc a b :=
    ⟨le_add_of_nonneg_right z.1.2.1, (add_le_add le_rfl z.1.2.2).trans hab⟩
  let T : C(Z, Icc a b) := ⟨fun z => ⟨a + z.1, htime z⟩,
    (continuous_const.add (continuous_subtype_val.comp continuous_fst)).subtype_mk htime⟩
  let timed (w : C(Z, Ω)) : C(Z, A) := T.prodMk w
  have htimed : Continuous timed := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact (T.continuous.comp continuous_snd).prodMk (continuous_fst.eval continuous_snd)
  let Sn (j : ℕ) : C(Z, W) := N.comp (timed (Jn j))
  let s0 : C(Z, W) := N.comp (timed j0)
  have hSn : Tendsto Sn atTop (𝓝 s0) :=
    (N.continuous_postcomp.tendsto _).comp ((htimed.tendsto _).comp hJn)
  let labels (w : C(Z, ℝ)) : C(Z, Z) := ⟨fun z => (z.1, z.2 + (w z : AddCircle L)),
    continuous_fst.prodMk
      (continuous_snd.add (continuous_quotient_mk'.comp w.continuous))⟩
  have hlabels : Continuous labels := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact continuous_snd.fst.prodMk (continuous_snd.snd.add
      (continuous_quotient_mk'.comp (continuous_fst.eval continuous_snd)))
  let Ln (j : ℕ) := labels (D j).uncurry
  let l0 := labels d.uncurry
  have hLn : Tendsto Ln atTop (𝓝 l0) := (hlabels.tendsto _).comp hDu
  let scaleH := AddCircle.homeomorphAddCircle curvePeriod L
    (Fact.out : 0 < curvePeriod).ne' (Fact.out : 0 < L).ne'
  let scale : C(AddCircle curvePeriod, AddCircle L) := ⟨scaleH, scaleH.continuous⟩
  have hscale (x : ℝ) : scale (x : AddCircle curvePeriod) = ((κ * x : ℝ) : AddCircle L) := by
    change ((x * (curvePeriod⁻¹ * L) : ℝ) : AddCircle L) = _
    congr 1
    dsimp only [κ]
    ring
  let scaleT : C(Icc (0 : ℝ) S × AddCircle curvePeriod, Z) :=
    ⟨fun z => (z.1, scale z.2), continuous_fst.prodMk (scale.continuous.comp continuous_snd)⟩
  let Rn (j : ℕ) := (((Q j).uncurry.comp (Ln j)).comp scaleT).curry
  let rn := ((q.uncurry.comp l0).comp scaleT).curry
  let Sfn (j : ℕ) := (((Sn j).comp (Ln j)).comp scaleT).curry
  let sf := ((s0.comp l0).comp scaleT).curry
  have hRn : Tendsto Rn atTop (𝓝 rn) :=
    (ContinuousMap.continuous_curry.tendsto _).comp
      ((scaleT.continuous_precomp.tendsto _).comp (hQu.compCM hLn))
  have hSfn : Tendsto Sfn atTop (𝓝 sf) :=
    (ContinuousMap.continuous_curry.tendsto _).comp
      ((scaleT.continuous_precomp.tendsto _).comp (hSn.compCM hLn))
  have hlabel (j : ℕ) (t : Icc (0 : ℝ) S) (x : ℝ) :
      Ln j (scaleT (t, (x : AddCircle curvePeriod))) =
        (t, ((psi j t (κ * x) : ℝ) : AddCircle L)) := by
    change (t, scale (x : AddCircle curvePeriod) +
      ((D j t (scale (x : AddCircle curvePeriod)) : ℝ) : AddCircle L)) =
        (t, ((psi j t (κ * x) : ℝ) : AddCircle L))
    apply congrArg (fun z : AddCircle L => (t, z))
    rw [hscale, hDrep, ← AddCircle.coe_add]
    congr 1
    ring
  have hgeom (j : ℕ) (t : Icc (0 : ℝ) S) (x : ℝ) :
      mfderiv (𝓡 n) 𝓘(ℝ, W) e (c j x (a + t))
        (spatialUnitTangent F (c j) (a + t) x) =
        Sn j (t, ((psi j t (κ * x) : ℝ) : AddCircle L)) := by
    let f : ℝ → W := fun y => Q j t (y : AddCircle L)
    let f' : ℝ → W := fun y => P j t (y : AddCircle L)
    let gamma : ℝ → M := fun y => ρ (f y)
    let gammaT := fun y (_ : ℝ) => gamma y
    let phi : ℝ → ℝ := fun y => psi j t (κ * y)
    have hgam (y : ℝ) : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n) gamma y :=
      ((hρ.contMDiffAt (hU.mem_nhds (hguard j t (y : AddCircle L)).1)).mdifferentiableAt
        (by simp)).comp y (hder j t y).differentiableAt.mdifferentiableAt
    have hvel (y : ℝ) : curveVelocity (n := n) gamma y =
        mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (f y) (f' y) := by
      change (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (ρ ∘ f) y) 1 = _
      erw [mfderiv_comp y
        ((hρ.contMDiffAt (hU.mem_nhds (hguard j t (y : AddCircle L)).1)).mdifferentiableAt
          (by simp)) (hder j t y).differentiableAt.mdifferentiableAt,
        ContinuousLinearMap.comp_apply, mfderiv_eq_fderiv,
        (hder j t y).hasFDerivAt.fderiv]
      exact congrArg (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (f y))
        (ContinuousLinearMap.toSpanSingleton_apply_one ℝ (f' y))
    obtain ⟨hret, hretder, _⟩ := smooth_retraction_differentials he hU heU hρ hρe
    have hpush (y : ℝ) : mfderiv (𝓡 n) 𝓘(ℝ, W) e (gamma y)
        (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (f y) (f' y)) = f' y := by
      have hchain := ((hret.contDiffAt
        (hU.mem_nhds (hguard j t (y : AddCircle L)).1)).differentiableAt
          (by simp)).hasFDerivAt.comp_hasDerivAt y (hder j t y)
      have heq : (fun z : ℝ => (e ∘ ρ) (f z)) = f :=
        funext fun z => (hfixed j t (z : AddCircle L)).symm
      change HasDerivAt (fun z : ℝ => (e ∘ ρ) (f z))
        (fderiv ℝ (e ∘ ρ) (f y) (f' y)) y at hchain
      rw [heq] at hchain
      rw [← hretder (f y) (hguard j t (y : AddCircle L)).1 (f' y)]
      exact hchain.unique (hder j t y)
    have hlin : HasDerivAt (fun y : ℝ => κ * y) κ x := by
      simpa +instances only [id_eq, mul_one] using! (hasDerivAt_id x).const_mul κ
    have hphi : HasDerivAt phi (deriv (psi j t) (κ * x) * κ) x := by
      simpa only [phi, Function.comp_def, smul_eq_mul, mul_comm] using
        ((hpsi j t).differentiable (by norm_num) (κ * x)).hasDerivAt.scomp x hlin
    have hpositive : 0 < deriv (psi j t) (κ * x) * κ := mul_pos (hpos j t _) hκ
    have hslice' : (fun y => c j y (a + t)) = fun y => gamma (phi y) :=
      funext (hslice j t)
    have hpushSlice := congrArg (fun g : ℝ → M =>
      (mfderiv (𝓡 n) 𝓘(ℝ, W) e (g x)
        (((F.metric (a + t)).tangentNorm (g x) (curveVelocity (n := n) g x))⁻¹ •
          curveVelocity (n := n) g x) : W)) hslice'
    change mfderiv (𝓡 n) 𝓘(ℝ, W) e (c j x (a + t))
        (spatialUnitTangent F (c j) (a + t) x) =
      mfderiv (𝓡 n) 𝓘(ℝ, W) e (gamma (phi x))
        (spatialUnitTangent F (fun y s => gammaT (phi y) s) (a + t) x) at hpushSlice
    rw [hpushSlice, spatialUnitTangent_comp F gammaT (hgam (phi x)) hphi hpositive]
    simp only [spatialUnitTangent, map_smul]
    change (curveSpeed F gammaT (a + t) (phi x))⁻¹ •
      mfderiv (𝓡 n) 𝓘(ℝ, W) e (gamma (phi x)) (curveVelocity gamma (phi x)) = _
    rw [hvel, hpush]
    change ((F.metric (a + t)).tangentNorm (gamma (phi x))
      (curveVelocity gamma (phi x)))⁻¹ • f' (phi x) = _
    rw [hvel]
    rfl
  refine ⟨Rn, Sfn, rn, sf, hRn, hSfn, ?_, ?_, ?_⟩
  · intro j t x
    change (Q j).uncurry (Ln j (scaleT (t, (x : AddCircle curvePeriod)))) = _
    rw [hlabel]
    change Q j t ((psi j t (κ * x) : ℝ) : AddCircle L) = _
    rw [hslice]
    exact hfixed j t _
  · intro j t x
    change Sn j (Ln j (scaleT (t, (x : AddCircle curvePeriod)))) = _
    rw [hlabel]
    exact (hgeom j t x).symm
  · intro t x
    dsimp only
    have heval : l0 (scaleT (t, (x : AddCircle curvePeriod))) =
        (t, ((κ * x + d t ((κ * x : ℝ) : AddCircle L) : ℝ) : AddCircle L)) := by
      change (t, scale (x : AddCircle curvePeriod) +
        ((d t (scale (x : AddCircle curvePeriod)) : ℝ) : AddCircle L)) = _
      rw [hscale, ← AddCircle.coe_add]
    change q.uncurry (l0 (scaleT (t, (x : AddCircle curvePeriod)))) = _ ∧
      s0 (l0 (scaleT (t, (x : AddCircle curvePeriod)))) = _
    rw [heval]
    exact ⟨rfl, rfl⟩

end PoincareConjecture.M63
