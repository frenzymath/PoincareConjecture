import PoincareConjecture.Proofs.M14.Sec6_3_SliceLift
import PoincareConjecture.Statements.M14GeneralizedLGeometry











set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M46

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T tau : ℝ} {x y : G.Point}



theorem minimizing_initialValuePath (LG : GeneralizedLGeometryConclusion G)
    (p : M14BackwardPath G T 0 tau x y) (hp : M14IsMinimizing p) :
    ∃ Z : G.Horizontal x, ∃ Q : M14SquareRootInitialValuePath G T tau x y Z,
      Q.path = p := by
  obtain ⟨E0, hE0⟩ := LG.path_calculus.minimizer_euler T 0 tau x y p hp
  obtain ⟨R, ER, hER⟩ :=
    LG.path_calculus.square_root_regularization T 0 tau x y p E0 hE0
  have hzero : R.curve 0 = x := by
    have hz : (0 : ℝ) ∈ M14SqrtParameterInterval 0 tau := by
      simp only [M14SqrtParameterInterval, Real.sqrt_zero, mem_Icc, le_refl,
        Real.sqrt_nonneg, and_self]
    simpa only [zero_pow (by norm_num : 2 ≠ 0), p.curve_start] using R.agrees 0 hz
  let A : G.Horizontal x := hzero ▸ R.horizontal_velocity 0
  let Z : G.Horizontal x := (1 / 2 : ℝ) • A
  refine ⟨Z, {
    path := p
    square_path := R
    extension := ER
    euler := hER
    initial_velocity := ⟨hzero, ?_⟩
  }, rfl⟩
  change A = (2 : ℝ) • ((1 / 2 : ℝ) • A)
  simp only [smul_smul, mul_one_div_cancel (by norm_num : (2 : ℝ) ≠ 0), one_smul]

private theorem initialValuePath_cast_curve {b : ℝ} {Z : G.Horizontal x}
    (h : tau = b) (Q : M14SquareRootInitialValuePath G T tau x y Z) :
    (h ▸ Q : M14SquareRootInitialValuePath G T b x y Z).path.curve = Q.path.curve := by
  cases h
  rfl



theorem initialValue_exponential_branch
    (E : M14ExponentialFamily G T x)
    {Z : G.Horizontal x} (Q : M14SquareRootInitialValuePath G T tau x y Z) :
    (Z, Real.sqrt tau) ∈ E.domain ∧
      EqOn Q.path.curve (fun s => E.gamma Z (Real.sqrt s)) (Icc 0 tau) ∧
      E.gamma Z (Real.sqrt tau) = y := by
  let Q' : M14SquareRootInitialValuePath G T ((Real.sqrt tau) ^ 2) x y Z :=
    (Real.sq_sqrt Q.path.tau_lt.le).symm ▸ Q
  have hQcurve : Q'.path.curve = Q.path.curve :=
    initialValuePath_cast_curve (Real.sq_sqrt Q.path.tau_lt.le).symm Q
  have hsurvive : (Z, Real.sqrt tau) ∈ E.domain :=
    (E.positive_survival_iff Z (Real.sqrt tau) (Real.sqrt_pos.mpr Q.path.tau_lt)).mpr
      ⟨y, ⟨Q'⟩⟩
  have htrace : EqOn Q.path.curve (fun s => E.gamma Z (Real.sqrt s)) (Icc 0 tau) := by
    simpa only [hQcurve, Real.sq_sqrt Q.path.tau_lt.le] using
      E.initial_value_agreement Z (Real.sqrt tau) (Real.sqrt_pos.mpr Q.path.tau_lt) y Q'
  exact ⟨hsurvive, htrace,
    (htrace ⟨Q.path.tau_lt.le, le_rfl⟩).symm.trans Q.path.curve_end⟩



theorem minimizing_exponential_branch (LG : GeneralizedLGeometryConclusion G)
    (E : M14ExponentialFamily G T x)
    (p : M14BackwardPath G T 0 tau x y) (hp : M14IsMinimizing p) :
    ∃ Z : G.Horizontal x, (Z, Real.sqrt tau) ∈ E.domain ∧
      EqOn p.curve (fun s => E.gamma Z (Real.sqrt s)) (Icc 0 tau) ∧
      E.gamma Z (Real.sqrt tau) = y := by
  obtain ⟨Z, Q, hQ⟩ := minimizing_initialValuePath LG p hp
  obtain ⟨hsurvive, htrace, hend⟩ := initialValue_exponential_branch E Q
  rw [hQ] at htrace
  exact ⟨Z, hsurvive, htrace, hend⟩



theorem survival_domain_open (E : M14ExponentialFamily G T x) (s : ℝ) :
    IsOpen {Z | (Z, s) ∈ E.domain} := by
  rw [isOpen_iff_mem_nhds]
  intro Z hZ
  obtain ⟨U, hU, hZU, hsub⟩ := E.domain_relative_open (Z, s) hZ
  have hcont : Continuous (fun W : G.Horizontal x => (W, s)) :=
    continuous_id.prodMk continuous_const
  apply mem_of_superset ((hU.preimage hcont).mem_nhds hZU)
  intro W hW
  exact hsub ⟨hW, (E.domain_admissible hZ).1, (E.domain_admissible hZ).2⟩



noncomputable def survivalSliceMap (E : M14ExponentialFamily G T x)
    (tau : ℝ) (htau : 0 ≤ tau) (q0 : (G.slices (T - tau)).Point)
    (Z : G.Horizontal x) : (G.slices (T - tau)).Point := by
  classical
  exact if hZ : (Z, Real.sqrt tau) ∈ E.domain then
    ⟨E.gamma Z (Real.sqrt tau), by simpa only [Real.sq_sqrt htau] using E.clock Z _ hZ⟩
  else q0



theorem survivalSliceMap_val (E : M14ExponentialFamily G T x)
    (htau : 0 ≤ tau) (q0 : (G.slices (T - tau)).Point)
    {Z : G.Horizontal x} (hZ : (Z, Real.sqrt tau) ∈ E.domain) :
    (survivalSliceMap E tau htau q0 Z).val = E.gamma Z (Real.sqrt tau) := by
  simp only [survivalSliceMap, dif_pos hZ]



theorem survivalSliceMap_smooth (E : M14ExponentialFamily G T x)
    (htau : 0 ≤ tau) (q0 : (G.slices (T - tau)).Point)
    {Z : G.Horizontal x} (hZ : (Z, Real.sqrt tau) ∈ E.domain) :
    letI : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) :=
      ⟨G.spacetime.horizontalMetric.toRiemannianMetric⟩
    ContMDiffAt (𝓘(ℝ, G.Horizontal x)) (𝓡 n) ∞
      (survivalSliceMap E tau htau q0) Z := by
  let : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) :=
    ⟨G.spacetime.horizontalMetric.toRiemannianMetric⟩
  have hgamma : ContMDiffOn (𝓘(ℝ, G.Horizontal x)) (spacetimeModel n) ∞
      (fun W => E.gamma W (Real.sqrt tau)) {W | (W, Real.sqrt tau) ∈ E.domain} :=
    E.family_smooth.comp
      (contMDiff_id.prodMk (contMDiff_const (c := Real.sqrt tau))).contMDiffOn
      (fun _ hW => hW)
  apply M14.contMDiffAt_slice_of_inclusion
  apply ((hgamma Z hZ).contMDiffAt ((survival_domain_open E _).mem_nhds hZ)).congr_of_eventuallyEq
  filter_upwards [(survival_domain_open E (Real.sqrt tau)).mem_nhds hZ] with W hW
  exact survivalSliceMap_val E htau q0 hW



theorem survivalSliceMap_differential (E : M14ExponentialFamily G T x)
    (htau : 0 ≤ tau) (q0 : (G.slices (T - tau)).Point)
    {Z : G.Horizontal x} (hZ : (Z, Real.sqrt tau) ∈ E.domain) (W : G.Horizontal x) :
    letI : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) :=
      ⟨G.spacetime.horizontalMetric.toRiemannianMetric⟩
    ((G.slices (T - tau)).tangentEquiv (survivalSliceMap E tau htau q0 Z)
      (mfderiv (𝓘(ℝ, G.Horizontal x)) (𝓡 n)
        (survivalSliceMap E tau htau q0) Z W)).val =
      (E.differential Z (Real.sqrt tau) hZ W).val := by
  let : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) :=
    ⟨G.spacetime.horizontalMetric.toRiemannianMetric⟩
  let f := survivalSliceMap E tau htau q0
  have hf := (survivalSliceMap_smooth E htau q0 hZ).mdifferentiableAt (by simp)
  have hi := (G.slices (T - tau)).inclusion_smooth.mdifferentiableAt
    (x := f Z) (by simp)
  have hchain := mfderiv_comp_apply Z hi hf W
  have heq : ((Subtype.val : (G.slices (T - tau)).Point → G.Point) ∘ f) =ᶠ[𝓝 Z]
      (fun A => E.gamma A (Real.sqrt tau)) := by
    filter_upwards [(survival_domain_open E (Real.sqrt tau)).mem_nhds hZ] with A hA
    exact survivalSliceMap_val E htau q0 hA
  have hd := congrArg (fun L : G.Horizontal x →L[ℝ] SpacetimeModelVector n => L W)
    (heq.mfderiv_eq (I := 𝓘(ℝ, G.Horizontal x)) (I' := spacetimeModel n))
  rw [(G.slices (T - tau)).tangentEquiv_eq]
  exact hchain.symm.trans
    (hd.trans (E.differential_pointwise_mfderiv Z (Real.sqrt tau) hZ W).symm)

private theorem bijective_iff_of_horizontal_val_eq {a b : G.Point} (h : a = b)
    (A : G.Horizontal x →L[ℝ] G.Horizontal a)
    (B : G.Horizontal x →L[ℝ] G.Horizontal b)
    (hval : ∀ W, (A W).val = (B W).val) : Function.Bijective A ↔ Function.Bijective B := by
  cases h
  have heq : A = B := ContinuousLinearMap.ext (fun W => Subtype.ext (hval W))
  rw [heq]



theorem survivalSliceMap_differential_bijective_iff
    (E : M14ExponentialFamily G T x) (htau : 0 ≤ tau)
    (q0 : (G.slices (T - tau)).Point)
    {Z : G.Horizontal x} (hZ : (Z, Real.sqrt tau) ∈ E.domain) :
    letI : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) :=
      ⟨G.spacetime.horizontalMetric.toRiemannianMetric⟩
    Function.Bijective (mfderiv (𝓘(ℝ, G.Horizontal x)) (𝓡 n)
      (survivalSliceMap E tau htau q0) Z) ↔
        Function.Bijective (E.differential Z (Real.sqrt tau) hZ) := by
  let : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) :=
    ⟨G.spacetime.horizontalMetric.toRiemannianMetric⟩
  let f := survivalSliceMap E tau htau q0
  let A : G.Horizontal x →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    mfderiv (𝓘(ℝ, G.Horizontal x)) (𝓡 n) f Z
  let L := (G.slices (T - tau)).tangentEquiv (f Z)
  have hcomp := bijective_iff_of_horizontal_val_eq (survivalSliceMap_val E htau q0 hZ)
    (L.toContinuousLinearMap.comp A) (E.differential Z (Real.sqrt tau) hZ)
    (fun W => survivalSliceMap_differential E htau q0 hZ W)
  exact (Function.Bijective.of_comp_iff' L.bijective A).symm.trans hcomp

end PoincareConjecture.Proofs.M46
