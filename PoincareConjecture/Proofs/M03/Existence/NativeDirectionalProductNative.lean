import PoincareConjecture.Proofs.M03.Existence.NativeDirectionalClosedNative
import PoincareConjecture.Proofs.M03.Existence.TensorFirstOrderGraphNative
import Mathlib.Topology.Order.Compact
import Mathlib.Geometry.Manifold.VectorField.LieBracket

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

noncomputable section

universe u v

namespace PoincareConjecture.TensorProbeNative

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem scalarDirectional_mul (V : SmoothField (n := n) (M := M))
    {ψ f : M → ℝ} {x : M}
    (hψ : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) ψ x)
    (hf : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f x) :
    scalarDirectional V (fun y => ψ y * f y) x =
      ψ x * scalarDirectional V f x + f x * scalarDirectional V ψ x := by
  have h := congrArg (fun L : TangentSpace (𝓡 n) x →L[ℝ] ℝ => L (V x))
    (mvfderiv_fun_mul hψ hf)
  exact h

theorem scalarDirectional_mul_sq_le (V : SmoothField (n := n) (M := M))
    {ψ f : M → ℝ} {x : M}
    (hψ : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) ψ x)
    (hf : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f x)
    (hψbound : |ψ x| ≤ 1) {B : ℝ} (hB : 0 ≤ B)
    (hDbound : |scalarDirectional V ψ x| ≤ B) :
    scalarDirectional V (fun y => ψ y * f y) x ^ 2 ≤
      2 * scalarDirectional V f x ^ 2 + 2 * B ^ 2 * f x ^ 2 := by
  rw [scalarDirectional_mul V hψ hf]
  have hψsq : ψ x ^ 2 ≤ 1 := by
    simpa only [sq_abs, one_pow] using
      (sq_le_sq₀ (abs_nonneg (ψ x)) zero_le_one).mpr hψbound
  have hDsq : scalarDirectional V ψ x ^ 2 ≤ B ^ 2 := by
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg (scalarDirectional V ψ x)) hB).mpr hDbound
  have hψterm := mul_le_mul_of_nonneg_right hψsq (sq_nonneg (scalarDirectional V f x))
  have hDterm := mul_le_mul_of_nonneg_right hDsq (sq_nonneg (f x))
  nlinarith [sq_nonneg (ψ x * scalarDirectional V f x - f x * scalarDirectional V ψ x)]

variable {iota : Type v} [Fintype iota]

theorem directional_energy_mul_le (F : iota → SmoothField (n := n) (M := M))
    {ψ f : M → ℝ} {x : M}
    (hψ : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) ψ x)
    (hf : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f x)
    (hψbound : |ψ x| ≤ 1) {B : ℝ} (hB : 0 ≤ B)
    (hDbound : ∀ i, |scalarDirectional (F i) ψ x| ≤ B) :
    (∑ i, scalarDirectional (F i) (fun y => ψ y * f y) x ^ 2) ≤
      2 * (∑ i, scalarDirectional (F i) f x ^ 2) +
        2 * (Fintype.card iota : ℝ) * B ^ 2 * f x ^ 2 := by
  classical
  calc
    _ ≤ ∑ i, (2 * scalarDirectional (F i) f x ^ 2 + 2 * B ^ 2 * f x ^ 2) :=
      Finset.sum_le_sum (fun i _ => scalarDirectional_mul_sq_le (F i) hψ hf hψbound hB
        (hDbound i))
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul]
      ring

theorem exists_scalarDirectional_bound [CompactSpace M]
    (F : iota → SmoothField (n := n) (M := M))
    {ψ : M → ℝ} (hψ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ ψ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (i : iota) (x : M), |scalarDirectional (F i) ψ x| ≤ B := by
  classical
  have hex (i : iota) : ∃ b : ℝ, ∀ x : M, |scalarDirectional (F i) ψ x| ≤ b := by
    obtain ⟨b, hb⟩ := isCompact_univ.bddAbove_image
      (contMDiff_directional hψ (F i)).continuous.abs.continuousOn
    exact ⟨b, fun x => hb ⟨x, Set.mem_univ x, rfl⟩⟩
  choose b hb using hex
  let B : ℝ := ∑ i, max (b i) 0
  refine ⟨B, Finset.sum_nonneg (fun i _ => le_max_right (b i) 0), ?_⟩
  intro i x
  exact (hb i x).trans ((le_max_left (b i) 0).trans
    (Finset.single_le_sum (fun j _ => le_max_right (b j) 0) (Finset.mem_univ i)))

def smoothFieldBracket (V W : SmoothField (n := n) (M := M)) :
    SmoothField (n := n) (M := M) := by
  have hmin : minSmoothness ℝ 2 ≤ (∞ : ℕ∞ω) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact ENat.LEInfty.out
  letI : IsManifold (𝓡 n) (minSmoothness ℝ 2) M := IsManifold.of_le (n := ∞) hmin
  letI : IsManifold (𝓡 n) (∞ + 1) M := by simpa using (inferInstance : IsManifold (𝓡 n) ∞ M)
  exact ⟨VectorField.mlieBracket (𝓡 n) V W, fun x =>
    (V.contMDiff x).mlieBracket_vectorField (m := (⊤ : ℕ∞)) (n := (⊤ : ℕ∞))
      (W.contMDiff x) (by simp [minSmoothness_of_isRCLikeNormedField])⟩

private theorem directional_eq_chart_derivative (p : M)
    (V : SmoothField (n := n) (M := M)) {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    {z : EuclideanSpace ℝ (Fin n)}
    (hz : z ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).target) :
    scalarDirectional V f ((chartAt (EuclideanSpace ℝ (Fin n)) p).symm z) =
      fderiv ℝ (f ∘ (chartAt (EuclideanSpace ℝ (Fin n)) p).symm) z
        (chartField p V z) := by
  let e := chartAt (EuclideanSpace ℝ (Fin n)) p
  have he := mdifferentiable_chart (I := 𝓡 n) p
  have hinv := he.symm_comp_deriv (e.map_target hz)
  rw [e.right_inv hz] at hinv
  have hvinv : mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡 n) e.symm z
      (chartField p V z) = V (e.symm z) := by
    exact congrArg (fun L : TangentSpace (𝓡 n) (e.symm z) →L[ℝ]
      TangentSpace (𝓡 n) (e.symm z) => L (V (e.symm z))) hinv
  have hchain := mfderiv_comp_apply z
    ((hf (e.symm z)).mdifferentiableAt (by simp))
    (he.mdifferentiableAt_symm hz) (chartField p V z)
  rw [mfderiv_eq_fderiv] at hchain
  exact (hchain.trans (congrArg (mfderiv (𝓡 n) 𝓘(ℝ, ℝ) f (e.symm z)) hvinv)).symm

theorem chartField_smoothFieldBracket (p : M)
    (V W : SmoothField (n := n) (M := M))
    {z : EuclideanSpace ℝ (Fin n)}
    (hz : z ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).target) :
    chartField p (smoothFieldBracket V W) z =
      VectorField.lieBracket ℝ (chartField p V) (chartField p W) z := by
  let E := EuclideanSpace ℝ (Fin n)
  let e := chartAt E p
  have hmin : minSmoothness ℝ 2 ≤ (∞ : ℕ∞ω) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact ENat.LEInfty.out
  letI : IsManifold (𝓡 n) (minSmoothness ℝ 2) M :=
    IsManifold.of_le (n := ∞) hmin
  have hi : ContMDiffAt 𝓘(ℝ, E) (𝓡 n) ∞ e.symm z :=
    (contMDiffOn_chart_symm (I := 𝓡 n) (x := p) z hz).contMDiffAt
      (e.open_target.mem_nhds hz)
  have hpb (Z : (x : M) → TangentSpace (𝓡 n) x) {w : E}
      (hw : w ∈ e.target) :
      VectorField.mpullback 𝓘(ℝ, E) (𝓡 n) e.symm Z w =
        mfderiv (𝓡 n) 𝓘(ℝ, E) e (e.symm w) (Z (e.symm w)) := by
    let A := (mdifferentiable_chart (I := 𝓡 n) p).symm.mfderiv hw
    change A.toContinuousLinearMap.inverse (Z (e.symm w)) = _
    rw [ContinuousLinearMap.inverse_equiv]
    rfl
  have hVeq : VectorField.mpullback 𝓘(ℝ, E) (𝓡 n) e.symm V =ᶠ[𝓝 z]
      chartField p V := by
    filter_upwards [e.open_target.mem_nhds hz] with w hw
    exact hpb V hw
  have hWeq : VectorField.mpullback 𝓘(ℝ, E) (𝓡 n) e.symm W =ᶠ[𝓝 z]
      chartField p W := by
    filter_upwards [e.open_target.mem_nhds hz] with w hw
    exact hpb W hw
  have hnat := VectorField.mpullback_mlieBracket
    ((V.contMDiff (e.symm z)).mdifferentiableAt (by simp))
    ((W.contMDiff (e.symm z)).mdifferentiableAt (by simp)) hi hmin
  change mfderiv (𝓡 n) 𝓘(ℝ, E) e (e.symm z)
    (VectorField.mlieBracket (𝓡 n) V W (e.symm z)) = _
  calc
    _ = VectorField.mpullback 𝓘(ℝ, E) (𝓡 n) e.symm
        (VectorField.mlieBracket (𝓡 n) V W) z :=
      (hpb (VectorField.mlieBracket (𝓡 n) V W) hz).symm
    _ = VectorField.mlieBracket 𝓘(ℝ, E)
        (VectorField.mpullback 𝓘(ℝ, E) (𝓡 n) e.symm V)
        (VectorField.mpullback 𝓘(ℝ, E) (𝓡 n) e.symm W) z := hnat
    _ = VectorField.mlieBracket 𝓘(ℝ, E) (chartField p V) (chartField p W) z :=
      hVeq.mlieBracket_vectorField_eq hWeq
    _ = _ := by
      rw [← VectorField.mlieBracketWithin_univ,
        VectorField.mlieBracketWithin_eq_lieBracketWithin, VectorField.lieBracketWithin_univ]

theorem scalarDirectional_bracket (V W : SmoothField (n := n) (M := M))
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    scalarDirectional (smoothFieldBracket V W) f x =
      scalarDirectional V (scalarDirectional W f) x -
        scalarDirectional W (scalarDirectional V f) x := by
  let E := EuclideanSpace ℝ (Fin n)
  let e := chartAt E x
  let z := e x
  have hx : x ∈ e.source := mem_chart_source E x
  have hz : z ∈ e.target := e.map_source hx
  have hback : e.symm z = x := e.left_inv hx
  have hmin : minSmoothness ℝ 2 ≤ (∞ : ℕ∞ω) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact ENat.LEInfty.out
  have hfc := (contDiffOn_scalar_chartInverse x hf).contDiffAt (e.open_target.mem_nhds hz)
  have hVc := ((contDiffOn_chartField x V).contDiffAt
    (e.open_target.mem_nhds hz)).differentiableAt (by simp)
  have hWc := ((contDiffOn_chartField x W).contDiffAt
    (e.open_target.mem_nhds hz)).differentiableAt (by simp)
  have heq (Z : SmoothField (n := n) (M := M)) :
      (scalarDirectional Z f ∘ e.symm) =ᶠ[𝓝 z]
        (fun w => fderiv ℝ (f ∘ e.symm) w (chartField x Z w)) := by
    filter_upwards [e.open_target.mem_nhds hz] with w hw
    exact directional_eq_chart_derivative x Z hf hw
  have hVW := directional_eq_chart_derivative x V (f := scalarDirectional W f)
    (contMDiff_directional hf W) hz
  change scalarDirectional V (scalarDirectional W f) (e.symm z) = _ at hVW
  rw [hback] at hVW
  have hWV := directional_eq_chart_derivative x W (f := scalarDirectional V f)
    (contMDiff_directional hf V) hz
  change scalarDirectional W (scalarDirectional V f) (e.symm z) = _ at hWV
  rw [hback] at hWV
  calc
    _ = fderiv ℝ (f ∘ e.symm) z (chartField x (smoothFieldBracket V W) z) := by
      have h := directional_eq_chart_derivative x (smoothFieldBracket V W) hf hz
      change scalarDirectional (smoothFieldBracket V W) f (e.symm z) = _ at h
      rw [hback] at h
      exact h
    _ = fderiv ℝ (f ∘ e.symm) z
        (VectorField.lieBracket ℝ (chartField x V) (chartField x W) z) := by
      rw [chartField_smoothFieldBracket x V W hz]
    _ = fderiv ℝ (fun w => fderiv ℝ (f ∘ e.symm) w (chartField x W w)) z
          (chartField x V z) -
        fderiv ℝ (fun w => fderiv ℝ (f ∘ e.symm) w (chartField x V w)) z
          (chartField x W z) :=
      VectorField.fderiv_apply_lieBracket hfc hmin hWc hVc
    _ = _ := by
      rw [← (heq W).fderiv_eq, ← (heq V).fderiv_eq]
      exact congrArg₂ (fun a b : ℝ => a - b) hVW.symm hWV.symm

private theorem directional_add (V : SmoothField (n := n) (M := M))
    {f q : M → ℝ} {x : M}
    (hf : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f x)
    (hq : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) q x) :
    scalarDirectional V (fun y => f y + q y) x =
      scalarDirectional V f x + scalarDirectional V q x := by
  exact congrArg (fun L : TangentSpace (𝓡 n) x →L[ℝ] ℝ => L (V x)) (mfderiv_add hf hq)

theorem scalarDirectional_principal_commutator
    (X V W : SmoothField (n := n) (M := M)) {a f : M → ℝ}
    (ha : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ a)
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    scalarDirectional X (fun y => a y * scalarDirectional V (scalarDirectional W f) y) x -
      a x * scalarDirectional V (scalarDirectional W (scalarDirectional X f)) x =
      scalarDirectional X a x * scalarDirectional V (scalarDirectional W f) x +
        a x * scalarDirectional (smoothFieldBracket X V) (scalarDirectional W f) x +
        a x * scalarDirectional V (scalarDirectional (smoothFieldBracket X W) f) x := by
  have hinner : scalarDirectional X (scalarDirectional W f) =
      fun y => scalarDirectional W (scalarDirectional X f) y +
        scalarDirectional (smoothFieldBracket X W) f y := by
    funext y
    have h := scalarDirectional_bracket X W hf y
    linarith
  have hcomm : scalarDirectional X (scalarDirectional V (scalarDirectional W f)) x =
      scalarDirectional V (scalarDirectional W (scalarDirectional X f)) x +
        scalarDirectional (smoothFieldBracket X V) (scalarDirectional W f) x +
        scalarDirectional V (scalarDirectional (smoothFieldBracket X W) f) x := by
    have h := scalarDirectional_bracket X V (f := scalarDirectional W f)
      (contMDiff_directional hf W) x
    rw [hinner, directional_add V
      (f := scalarDirectional W (scalarDirectional X f))
      (q := scalarDirectional (smoothFieldBracket X W) f)
      ((contMDiff_directional (contMDiff_directional hf X) W).mdifferentiable (by simp) x)
      ((contMDiff_directional hf (smoothFieldBracket X W)).mdifferentiable (by simp) x)] at h
    linarith
  rw [scalarDirectional_mul X (ψ := a) (f := scalarDirectional V (scalarDirectional W f))
    (ha.mdifferentiable (by simp) x)
    ((contMDiff_directional (contMDiff_directional hf W) V).mdifferentiable (by simp) x), hcomm]
  ring

theorem scalarDirectional_neg (V : SmoothField (n := n) (M := M))
    (f : M → ℝ) (x : M) :
    scalarDirectional V (fun y => -f y) x = -scalarDirectional V f x := by
  change mfderiv (𝓡 n) 𝓘(ℝ, ℝ) (-f) x (V x) = _
  rw [mfderiv_neg]
  rfl

theorem scalarDirectional_sub (V : SmoothField (n := n) (M := M))
    {f q : M → ℝ} {x : M}
    (hf : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f x)
    (hq : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) q x) :
    scalarDirectional V (fun y => f y - q y) x =
      scalarDirectional V f x - scalarDirectional V q x := by
  exact congrArg (fun L : TangentSpace (𝓡 n) x →L[ℝ] ℝ => L (V x)) (mfderiv_sub hf hq)

def bracketCoefficient (g : RiemannianMetric n M)
    (F : iota → SmoothField (n := n) (M := M)) (i j k : iota) (x : M) : ℝ :=
  g.inner x (F k x) (smoothFieldBracket (F i) (F j) x)

theorem bracketCoefficient_contMDiff (g : RiemannianMetric n M)
    (F : iota → SmoothField (n := n) (M := M)) (i j k : iota) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (bracketCoefficient g F i j k) := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact (F k).contMDiff.inner_bundle (smoothFieldBracket (F i) (F j)).contMDiff

theorem scalarDirectional_bracket_eq_sum (g : RiemannianMetric n M)
    (F : iota → SmoothField (n := n) (M := M))
    (hF : ∀ (x : M) (v : TangentSpace (𝓡 n) x),
      (∑ k, g.inner x (F k x) v • F k x) = v)
    (i j : iota) (f : M → ℝ) (x : M) :
    scalarDirectional (smoothFieldBracket (F i) (F j)) f x =
      ∑ k, bracketCoefficient g F i j k x * scalarDirectional (F k) f x := by
  unfold scalarDirectional
  rw [← hF x (smoothFieldBracket (F i) (F j) x)]
  simp only [map_sum, map_smul, smul_eq_mul, bracketCoefficient]

theorem exists_bracketCoefficient_bound [CompactSpace M]
    (g : RiemannianMetric n M) (F : iota → SmoothField (n := n) (M := M)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (i j k : iota) (x : M), |bracketCoefficient g F i j k x| ≤ C := by
  classical
  have hb (q : iota × iota × iota) :
      ∃ c : ℝ, ∀ x : M, |bracketCoefficient g F q.1 q.2.1 q.2.2 x| ≤ c := by
    obtain ⟨c, hc⟩ := isCompact_univ.bddAbove_image
      (bracketCoefficient_contMDiff g F q.1 q.2.1 q.2.2).continuous.abs.continuousOn
    exact ⟨c, fun x => hc ⟨x, mem_univ x, rfl⟩⟩
  choose c hc using hb
  let C : ℝ := ∑ q : iota × iota × iota, max (c q) 0
  refine ⟨C, Finset.sum_nonneg (fun q _ => le_max_right _ _), ?_⟩
  intro i j k x
  exact (hc (i, j, k) x).trans ((le_max_left _ _).trans
    (Finset.single_le_sum (fun q _ => le_max_right (c q) 0) (Finset.mem_univ (i, j, k))))

def directionalWord (F : iota → SmoothField (n := n) (M := M)) :
    List iota → (M → ℝ) → M → ℝ
  | [], f => f
  | i :: w, f => scalarDirectional (F i) (directionalWord F w f)

@[simp] theorem directionalWord_nil (F : iota → SmoothField (n := n) (M := M))
    (f : M → ℝ) : directionalWord F [] f = f := rfl

@[simp] theorem directionalWord_cons (F : iota → SmoothField (n := n) (M := M))
    (i : iota) (w : List iota) (f : M → ℝ) :
    directionalWord F (i :: w) f = scalarDirectional (F i) (directionalWord F w f) := rfl

theorem directionalWord_contMDiff (F : iota → SmoothField (n := n) (M := M))
    (w : List iota) {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (directionalWord F w f) := by
  induction w with
  | nil => exact hf
  | cons i w ih => exact contMDiff_directional ih (F i)

theorem directionalWord_append (F : iota → SmoothField (n := n) (M := M))
    (v w : List iota) (f : M → ℝ) :
    directionalWord F (v ++ w) f = directionalWord F v (directionalWord F w f) := by
  induction v with
  | nil => rfl
  | cons i v ih => simp only [List.cons_append, directionalWord_cons, ih]

theorem scalarDirectional_finsetSum_smooth {jota : Type*} (s : Finset jota)
    (V : SmoothField (n := n) (M := M)) (f : jota → M → ℝ)
    (hf : ∀ j ∈ s, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (f j)) (x : M) :
    scalarDirectional V (fun y => ∑ j ∈ s, f j y) x =
      ∑ j ∈ s, scalarDirectional V (f j) x := by
  classical
  have hsum : ∀ t : Finset jota,
      (∀ j ∈ t, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (f j)) →
      HasMFDerivAt (𝓡 n) 𝓘(ℝ, ℝ) (fun y => ∑ j ∈ t, f j y) x
        (∑ j ∈ t, mfderiv (𝓡 n) 𝓘(ℝ, ℝ) (f j) x) := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      intro _
      simpa only [Finset.sum_empty] using
        (hasMFDerivAt_const (I := 𝓡 n) (c := (0 : ℝ)) x)
    | @insert j t hj ih =>
      intro ht
      have hdj := ((ht j (Finset.mem_insert_self j t)).mdifferentiable (by simp) x).hasMFDerivAt
      have hdt := ih (fun k hk => ht k (Finset.mem_insert_of_mem hk))
      have hfun : (fun y => ∑ k ∈ insert j t, f k y) =
          f j + (fun y => ∑ k ∈ t, f k y) := by
        funext y
        simp only [Finset.sum_insert hj, Pi.add_apply]
      rw [hfun, Finset.sum_insert hj]
      exact hdj.add hdt
  have hderiv := hsum s hf
  unfold scalarDirectional
  rw [hderiv.mfderiv]
  simp only [ContinuousLinearMap.sum_apply]
  rfl

structure DirectionalTerm where
  coefficient : M → ℝ
  smooth : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ coefficient
  word : List iota

def directionalTerms (F : iota → SmoothField (n := n) (M := M))
    (terms : List (DirectionalTerm (n := n) (M := M) (iota := iota)))
    (f : M → ℝ) (x : M) : ℝ :=
  (terms.map (fun t => t.coefficient x * directionalWord F t.word f x)).sum

@[simp] theorem directionalTerms_nil (F : iota → SmoothField (n := n) (M := M))
    (f : M → ℝ) (x : M) : directionalTerms F [] f x = 0 := rfl

@[simp] theorem directionalTerms_cons (F : iota → SmoothField (n := n) (M := M))
    (t : DirectionalTerm (n := n) (M := M) (iota := iota))
    (terms : List (DirectionalTerm (n := n) (M := M) (iota := iota)))
    (f : M → ℝ) (x : M) :
    directionalTerms F (t :: terms) f x =
      t.coefficient x * directionalWord F t.word f x + directionalTerms F terms f x := rfl

theorem directionalTerms_append (F : iota → SmoothField (n := n) (M := M))
    (a b : List (DirectionalTerm (n := n) (M := M) (iota := iota)))
    (f : M → ℝ) (x : M) :
    directionalTerms F (a ++ b) f x = directionalTerms F a f x + directionalTerms F b f x := by
  simp only [directionalTerms, List.map_append, List.sum_append]

theorem directionalTerms_contMDiff (F : iota → SmoothField (n := n) (M := M))
    (terms : List (DirectionalTerm (n := n) (M := M) (iota := iota)))
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (directionalTerms F terms f) := by
  induction terms with
  | nil => exact contMDiff_const
  | cons t terms ih =>
    exact (t.smooth.mul (directionalWord_contMDiff F t.word hf)).add ih

def appendDirectionalWords
    (terms : List (DirectionalTerm (n := n) (M := M) (iota := iota))) (w : List iota) :=
  terms.map (fun t => { t with word := t.word ++ w })

theorem directionalTerms_appendWords (F : iota → SmoothField (n := n) (M := M))
    (terms : List (DirectionalTerm (n := n) (M := M) (iota := iota))) (w : List iota)
    (f : M → ℝ) (x : M) :
    directionalTerms F (appendDirectionalWords terms w) f x =
      directionalTerms F terms (directionalWord F w f) x := by
  simp only [directionalTerms, appendDirectionalWords, List.map_map,
    Function.comp_def, directionalWord_append]

def differentiateDirectionalTerms (F : iota → SmoothField (n := n) (M := M))
    (j : iota) (terms : List (DirectionalTerm (n := n) (M := M) (iota := iota))) :
    List (DirectionalTerm (n := n) (M := M) (iota := iota)) :=
  terms.flatMap (fun t =>
    [⟨scalarDirectional (F j) t.coefficient, contMDiff_directional t.smooth (F j), t.word⟩,
      ⟨t.coefficient, t.smooth, j :: t.word⟩])

theorem directionalTerms_differentiate (F : iota → SmoothField (n := n) (M := M))
    (j : iota) (terms : List (DirectionalTerm (n := n) (M := M) (iota := iota)))
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    directionalTerms F (differentiateDirectionalTerms F j terms) f x =
      scalarDirectional (F j) (directionalTerms F terms f) x := by
  induction terms with
  | nil =>
    change 0 = scalarDirectional (F j) (fun _ : M => (0 : ℝ)) x
    simp only [scalarDirectional, mfderiv_const, ContinuousLinearMap.zero_apply]
  | cons t terms ih =>
    have ht : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞
        (fun y => t.coefficient y * directionalWord F t.word f y) :=
      t.smooth.mul (directionalWord_contMDiff F t.word hf)
    have hs := directionalTerms_contMDiff F terms hf
    simp only [differentiateDirectionalTerms, List.flatMap_cons, directionalTerms_append,
      directionalTerms_cons, directionalTerms_nil]
    change _ = scalarDirectional (F j)
      (fun y => t.coefficient y * directionalWord F t.word f y + directionalTerms F terms f y) x
    rw [directional_add (F j) (ht.mdifferentiable (by simp) x)
      (hs.mdifferentiable (by simp) x),
      scalarDirectional_mul (F j) (t.smooth.mdifferentiable (by simp) x)
        ((directionalWord_contMDiff F t.word hf).mdifferentiable (by simp) x)]
    change _ + directionalTerms F (differentiateDirectionalTerms F j terms) f x = _
    rw [ih]
    simp only [directionalWord_cons]
    ring

theorem appendDirectionalWords_order
    (terms : List (DirectionalTerm (n := n) (M := M) (iota := iota)))
    (w : List iota) {k : ℕ} (h : ∀ t ∈ terms, t.word.length ≤ k) :
    ∀ t ∈ appendDirectionalWords terms w, t.word.length ≤ k + w.length := by
  intro t ht
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ht
  simpa only [List.length_append] using Nat.add_le_add_right (h q hq) w.length

theorem differentiateDirectionalTerms_order (F : iota → SmoothField (n := n) (M := M))
    (j : iota) (terms : List (DirectionalTerm (n := n) (M := M) (iota := iota)))
    {k : ℕ} (h : ∀ t ∈ terms, t.word.length ≤ k) :
    ∀ t ∈ differentiateDirectionalTerms F j terms, t.word.length ≤ k + 1 := by
  intro t ht
  obtain ⟨q, hq, ht⟩ := List.mem_flatMap.mp ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl
  · exact (h q hq).trans (Nat.le_add_right _ _)
  · simpa only [List.length_cons] using Nat.add_le_add_right (h q hq) 1

end PoincareConjecture.TensorProbeNative
