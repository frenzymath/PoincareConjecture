import PoincareConjecture.Proofs.M03.Existence.FrameDeTurckDerivativeNative
import PoincareConjecture.Proofs.M03.CurvatureJoint
import PoincareConjecture.Proofs.M03.CurvaturePairExchange
import PoincareConjecture.Proofs.M03.Existence.TensorProbeL2Native











set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators Topology

noncomputable section

universe u

namespace PoincareConjecture.DeTurckNative

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "BilinE" => E →L[ℝ] E →L[ℝ] ℝ
local notation "BilinFib" =>
  fun x : M => TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x →L[ℝ] ℝ

private theorem exists_curvatureFirstSlot {g : RiemannianMetric n M}
    (D : LeviCivitaData g) (x : M) (v w : TangentSpace (𝓡 n) x) :
    ∃ L : TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x,
      ∀ u, L u = D.curvature x u v w := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  obtain ⟨U, hU, hw⟩ :=
    FiberBundle.exists_contMDiffOn_extend (k := ∞) (𝓡 n) E w
  obtain ⟨S, hSU, hS, hxS⟩ := mem_nhds_iff.mp hU
  have hT := Proofs.M03.curvatureOnFields_tensorial_first D hS
    (FiberBundle.extend E v) (FiberBundle.extend E w) (hw.mono hSU) hxS
  refine ⟨TensorialAt.mkHom
    (fun X : (y : M) → TangentSpace (𝓡 n) y =>
      D.curvatureOnFields X (FiberBundle.extend E v) (FiberBundle.extend E w) x)
    x hT, ?_⟩
  intro u
  rfl

private def curvatureFirstSlot {g : RiemannianMetric n M}
    (D : LeviCivitaData g) (x : M) (v w : TangentSpace (𝓡 n) x) :
    TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x :=
  Classical.choose (exists_curvatureFirstSlot D x v w)

private theorem curvatureFirstSlot_apply {g : RiemannianMetric n M}
    (D : LeviCivitaData g) (x : M) (u v w : TangentSpace (𝓡 n) x) :
    curvatureFirstSlot D x v w u = D.curvature x u v w :=
  Classical.choose_spec (exists_curvatureFirstSlot D x v w) u


def intrinsicRicciBilin {g : RiemannianMetric n M} (D : LeviCivitaData g)
    (x : M) : BilinFib x := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact ∑ i, (g.inner x).comp
    (curvatureFirstSlot D x (g.orthonormalBasis x i) (g.orthonormalBasis x i))

@[simp] theorem intrinsicRicciBilin_apply {g : RiemannianMetric n M}
    (D : LeviCivitaData g) (x : M) (u v : TangentSpace (𝓡 n) x) :
    intrinsicRicciBilin D x u v = D.ricci x u v := by
  simp only [intrinsicRicciBilin, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply, curvatureFirstSlot_apply,
    LeviCivitaData.ricci, LeviCivitaData.curvatureTensor]

theorem intrinsicRicci_symm {g : RiemannianMetric n M}
    (D : LeviCivitaData g) (x : M) (u v : TangentSpace (𝓡 n) x) :
    D.ricci x u v = D.ricci x v u := by
  unfold LeviCivitaData.ricci
  apply Finset.sum_congr rfl
  intro i _
  exact Proofs.M03.curvatureTensor_pair_exchange D x u (g.orthonormalBasis x i)
    v (g.orthonormalBasis x i)

private theorem contMDiffAt_clm_apply_iff_native
    {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ F]
    {f : M → F →L[ℝ] G} {x : M} :
    ContMDiffAt (𝓡 n) 𝓘(ℝ, F →L[ℝ] G) ∞ f x ↔
      ∀ v : F, ContMDiffAt (𝓡 n) 𝓘(ℝ, G) ∞ (fun y => f y v) x := by
  constructor
  · intro h v
    exact h.clm_apply contMDiffAt_const
  · intro h
    let d := Module.finrank ℝ F
    let e₁ := ContinuousLinearEquiv.ofFinrankEq
      (show d = Module.finrank ℝ (Fin d → ℝ) from (Module.finrank_fin_fun ℝ).symm)
    let e₂ := (e₁.arrowCongr (ContinuousLinearEquiv.refl ℝ G)).trans
      (ContinuousLinearEquiv.piRing (Fin d))
    have hc : ContMDiffAt (𝓡 n) 𝓘(ℝ, Fin d → G) ∞ (fun y => e₂ (f y)) x := by
      apply contMDiffAt_pi_space.mpr
      intro i
      exact h (e₁.symm (Pi.single i 1))
    have hb := (contMDiffAt_const (c := e₂.symm.toContinuousLinearMap)).clm_apply hc
    simpa only [ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.symm_apply_apply] using hb

private theorem contMDiff_bilin_of_local_pairings
    (A : (x : M) → BilinFib x)
    (hA : ∀ (U : Set M), IsOpen U →
      ∀ (X Y : (x : M) → TangentSpace (𝓡 n) x),
      ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) ∞ (T% X) U →
      ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) ∞ (T% Y) U →
      ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun x => A x (X x) (Y x)) U) :
    ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, BilinE)) ∞
      (fun x => Bundle.TotalSpace.mk' BilinE x (A x)) := by
  intro x
  let e := trivializationAt E (TangentSpace (𝓡 n)) x
  have hx : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  let F (a : E) (y : M) : TangentSpace (𝓡 n) y := e.symmL ℝ y a
  have hF (a : E) : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) ∞
      (T% (F a)) e.baseSet := by
    rw [e.contMDiffOn_section_baseSet_iff (IB := (𝓡 n)) (n := ∞)]
    refine (contMDiffOn_const (c := a)).congr ?_
    intro y hy
    simpa [F, Bundle.Trivialization.symmL_apply _ hy] using
      congrArg Prod.snd (e.apply_mk_symm hy a)
  apply (contMDiffAt_hom_bundle _).mpr
  refine ⟨contMDiffAt_id, ?_⟩
  apply contMDiffAt_clm_apply_iff_native.mpr
  intro a
  apply contMDiffAt_clm_apply_iff_native.mpr
  intro b
  have hp := (hA e.baseSet e.open_baseSet (F a) (F b) (hF a) (hF b)).contMDiffAt
    (e.open_baseSet.mem_nhds hx)
  apply hp.congr_of_eventuallyEq
  filter_upwards [e.open_baseSet.mem_nhds hx] with y hy
  rw [inCoordinates_apply_eq₂
    (F₁ := E) (F₂ := E) (F₃ := ℝ)
    (E₁ := TangentSpace (𝓡 n)) (E₂ := TangentSpace (𝓡 n))
    (E₃ := fun _ : M => ℝ) hy hy (by simp)]
  simp only [Bundle.Trivial.fiberBundle_trivializationAt',
    Bundle.Trivial.linearMapAt_trivialization, LinearMap.id_coe, id_eq]
  simp only [F, Bundle.Trivialization.symmL_apply _ hy, e]

theorem contMDiffOn_ricci_pair {g : RiemannianMetric n M}
    (D : LeviCivitaData g) {U : Set M} (hU : IsOpen U)
    (X Y : (x : M) → TangentSpace (𝓡 n) x)
    (hX : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) ∞ (T% X) U)
    (hY : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) ∞ (T% Y) U) :
    ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun x => D.ricci x (X x) (Y x)) U := by
  intro x hx
  let e := trivializationAt E (TangentSpace (𝓡 n)) x
  have he : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  let F (a : E) (y : M) : TangentSpace (𝓡 n) y := e.symmL ℝ y a
  have hF (a : E) : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) ∞
      (T% (F a)) e.baseSet := by
    rw [e.contMDiffOn_section_baseSet_iff (IB := (𝓡 n)) (n := ∞)]
    refine (contMDiffOn_const (c := a)).congr ?_
    intro y hy
    simpa [F, Bundle.Trivialization.symmL_apply _ hy] using
      congrArg Prod.snd (e.apply_mk_symm hy a)
  have hg : RiemannianMetric.IsSmoothFamilyOn (fun _ : ℝ => g) Set.univ :=
    (g.contMDiff.comp contMDiff_snd).contMDiffOn
  have hcurv (i : Fin n) :
      ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) ∞
        (fun y => Bundle.TotalSpace.mk' E y
          (D.curvature y (F ((PiLp.basisFun 2 ℝ (Fin n)) i) y) (X y) (Y y))) x := by
    have hs := Proofs.M03.contMDiffOn_family_curvature hg (fun _ => D)
      (hU.inter e.open_baseSet) (F ((PiLp.basisFun 2 ℝ (Fin n)) i)) X Y
      ((hF _).mono Set.inter_subset_right) (hX.mono Set.inter_subset_left)
      (hY.mono Set.inter_subset_left)
    have hc := hs.comp
      (contMDiffOn_const (c := (0 : ℝ)).prodMk contMDiffOn_id)
      (fun y (hy : y ∈ U ∩ e.baseSet) => ⟨Set.mem_univ _, hy⟩)
    exact hc.contMDiffAt ((hU.inter e.open_baseSet).mem_nhds ⟨hx, he⟩)
  have hcomponent (i : Fin n) : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun y => (e (Bundle.TotalSpace.mk' E y
        (D.curvature y (F ((PiLp.basisFun 2 ℝ (Fin n)) i) y) (X y) (Y y)))).2 i) x :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).contMDiff.contMDiffAt.comp x
      (Bundle.contMDiffAt_totalSpace.mp (hcurv i)).2
  have hsum := contMDiffAt_finsetSum (t := Finset.univ) (fun i _ => hcomponent i)
  apply (hsum.congr_of_eventuallyEq ?_).contMDiffWithinAt
  filter_upwards [e.open_baseSet.mem_nhds he] with y hy
  let b := (PiLp.basisFun 2 ℝ (Fin n)).map
    (e.continuousLinearEquivAt ℝ y hy).symm.toLinearEquiv
  rw [Proofs.M03.ricci_eq_sum_basis D y (X y) (Y y) b]
  apply Finset.sum_congr rfl
  intro i _
  change b.repr (D.curvature y (b i) (X y) (Y y)) i = _
  have hb : b i = F ((PiLp.basisFun 2 ℝ (Fin n)) i) y := by
    exact congrFun (e.symm_continuousLinearEquivAt_eq hy) _
  have hrepr (v : TangentSpace (𝓡 n) y) :
      b.repr v i = (e (Bundle.TotalSpace.mk' E y v)).2 i := by
    rfl
  rw [hrepr, hb]

theorem intrinsicRicciBilin_contMDiff {g : RiemannianMetric n M}
    (D : LeviCivitaData g) :
    ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, BilinE)) ∞
      (fun x => Bundle.TotalSpace.mk' BilinE x (intrinsicRicciBilin D x)) := by
  apply contMDiff_bilin_of_local_pairings
  intro U hU X Y hX hY
  simpa only [intrinsicRicciBilin_apply] using contMDiffOn_ricci_pair D hU X Y hX hY

def smoothRicciTensor {g : RiemannianMetric n M} (D : LeviCivitaData g) :
    TensorProbeNative.SmoothTensor (n := n) (M := M) :=
  ⟨intrinsicRicciBilin D, intrinsicRicciBilin_contMDiff D⟩

@[simp] theorem smoothRicciTensor_apply {g : RiemannianMetric n M}
    (D : LeviCivitaData g) (x : M) (u v : TangentSpace (𝓡 n) x) :
    smoothRicciTensor D x u v = D.ricci x u v := intrinsicRicciBilin_apply D x u v

theorem smoothRicciTensor_symm {g : RiemannianMetric n M}
    (D : LeviCivitaData g) (x : M) (u v : TangentSpace (𝓡 n) x) :
    smoothRicciTensor D x u v = smoothRicciTensor D x v u := by
  simpa only [smoothRicciTensor_apply] using intrinsicRicci_symm D x u v

def metricLieDerivative {g : RiemannianMetric n M} (D : LeviCivitaData g)
    (W : (y : M) → TangentSpace (𝓡 n) y) (x : M) :
    TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x →L[ℝ] ℝ := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact (g.inner x).comp (D.connection W x) + ((g.inner x).comp (D.connection W x)).flip

theorem metricLieDerivative_apply {g : RiemannianMetric n M} (D : LeviCivitaData g)
    (W : (y : M) → TangentSpace (𝓡 n) y) (x : M)
    (u v : TangentSpace (𝓡 n) x) :
    metricLieDerivative D W x u v =
      g.inner x (D.connection W x u) v + g.inner x u (D.connection W x v) := by
  change g.inner x (D.connection W x u) v + g.inner x (D.connection W x v) u = _
  rw [g.symm x (D.connection W x v) u]

theorem metricLieDerivative_symm {g : RiemannianMetric n M} (D : LeviCivitaData g)
    (W : (y : M) → TangentSpace (𝓡 n) y) (x : M)
    (u v : TangentSpace (𝓡 n) x) :
    metricLieDerivative D W x u v = metricLieDerivative D W x v u := by
  change g.inner x (D.connection W x u) v + g.inner x (D.connection W x v) u =
    g.inner x (D.connection W x v) u + g.inner x (D.connection W x u) v
  exact add_comm _ _

theorem contMDiffOn_metricLieDerivative_pair {g : RiemannianMetric n M}
    (D : LeviCivitaData g) {U : Set M} (hU : IsOpen U)
    (W X Y : (x : M) → TangentSpace (𝓡 n) x)
    (hW : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) ∞ (T% W) U)
    (hX : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) ∞ (T% X) U)
    (hY : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) ∞ (T% Y) U) :
    ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun x => metricLieDerivative D W x (X x) (Y x)) U := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hWX := D.contMDiffOn_connection_apply hU X W hX hW
  have hWY := D.contMDiffOn_connection_apply hU Y W hY hW
  have hleft : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun x => g.inner x (D.connection W x (X x)) (Y x)) U :=
    hWX.inner_bundle hY
  have hright : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun x => g.inner x (X x) (D.connection W x (Y x))) U :=
    hX.inner_bundle hWY
  exact (hleft.add hright).congr
    (fun x _ => metricLieDerivative_apply D W x (X x) (Y x))

theorem metricLieDerivative_contMDiff {g : RiemannianMetric n M}
    (D : LeviCivitaData g) (W : (x : M) → TangentSpace (𝓡 n) x)
    (hW : ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) ∞ (T% W)) :
    ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, BilinE)) ∞
      (fun x => Bundle.TotalSpace.mk' BilinE x (metricLieDerivative D W x)) := by
  apply contMDiff_bilin_of_local_pairings
  intro U hU X Y hX hY
  exact contMDiffOn_metricLieDerivative_pair D hU W X Y hW.contMDiffOn hX hY

def smoothMetricLieDerivative {g : RiemannianMetric n M}
    (D : LeviCivitaData g) (W : (x : M) → TangentSpace (𝓡 n) x)
    (hW : ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) ∞ (T% W)) :
    TensorProbeNative.SmoothTensor (n := n) (M := M) :=
  ⟨metricLieDerivative D W, metricLieDerivative_contMDiff D W hW⟩


def smoothRicciDeTurckTensor {g background : RiemannianMetric n M}
    (D : LeviCivitaData g) (B : LeviCivitaData background) :
    TensorProbeNative.SmoothTensor (n := n) (M := M) :=
  (-2 : ℝ) • smoothRicciTensor D +
    smoothMetricLieDerivative D (intrinsicDeTurckField D B)
      (intrinsicDeTurckField_contMDiffAt D B)

@[simp] theorem smoothRicciDeTurckTensor_apply
    {g background : RiemannianMetric n M}
    (D : LeviCivitaData g) (B : LeviCivitaData background) (x : M)
    (u v : TangentSpace (𝓡 n) x) :
    smoothRicciDeTurckTensor D B x u v = -2 * D.ricci x u v +
      metricLieDerivative D (intrinsicDeTurckField D B) x u v := by
  change (-2 : ℝ) * smoothRicciTensor D x u v +
    metricLieDerivative D (intrinsicDeTurckField D B) x u v = _
  rw [smoothRicciTensor_apply]

theorem smoothRicciDeTurckTensor_symm {g background : RiemannianMetric n M}
    (D : LeviCivitaData g) (B : LeviCivitaData background) (x : M)
    (u v : TangentSpace (𝓡 n) x) :
    smoothRicciDeTurckTensor D B x u v = smoothRicciDeTurckTensor D B x v u := by
  rw [smoothRicciDeTurckTensor_apply, smoothRicciDeTurckTensor_apply,
    intrinsicRicci_symm D x u v,
    metricLieDerivative_symm D (intrinsicDeTurckField D B) x u v]

theorem metricLieDerivative_connection_independent {g : RiemannianMetric n M}
    (D D' : LeviCivitaData g) (W : (y : M) → TangentSpace (𝓡 n) y) {x : M}
    (hW : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) (T% W) x) :
    metricLieDerivative D W x = metricLieDerivative D' W x := by
  unfold metricLieDerivative
  rw [D.connection_eq_at D' W hW]

theorem metricLieDerivative_on_fields {g : RiemannianMetric n M} (D : LeviCivitaData g)
    (W X Y : (y : M) → TangentSpace (𝓡 n) y) {x : M}
    (hW : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) (T% W) x)
    (hX : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) (T% X) x)
    (hY : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) (T% Y) x) :
    metricLieDerivative D W x (X x) (Y x) =
      mvfderiv (𝓡 n) (fun y => g.inner y (X y) (Y y)) x (W x) -
        g.inner x (VectorField.mlieBracket (𝓡 n) W X x) (Y x) -
        g.inner x (X x) (VectorField.mlieBracket (𝓡 n) W Y x) := by
  have hWX := (D.connection.torsion_eq_zero_iff.mp D.torsion_eq_zero) hW hX
  have hWY := (D.connection.torsion_eq_zero_iff.mp D.torsion_eq_zero) hW hY
  rw [metricLieDerivative_apply, D.mvfderiv_inner W X Y hX hY, ← hWX, ← hWY]
  simp only [map_sub, ContinuousLinearMap.sub_apply]
  ring

theorem metricLieDerivative_frame {g : RiemannianMetric n M} (D : LeviCivitaData g)
    (F : Fin n → (y : M) → TangentSpace (𝓡 n) y)
    (C : Fin n → M → ℝ) (W : (y : M) → TangentSpace (𝓡 n) y) {x : M}
    (hF : ∀ a, MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) (T% (F a)) x)
    (hC : ∀ a, MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) (C a) x)
    (hW : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) (T% W) x)
    (hrep : ∀ᶠ y in 𝓝 x, W y = ∑ k, C k y • F k y)
    (hbracket : ∀ a b, VectorField.mlieBracket (𝓡 n) (F a) (F b) x = 0)
    (i j : Fin n) :
    metricLieDerivative D W x (F i x) (F j x) =
      ∑ k, (C k x * (frameMetricJet g F x).first k i j +
        (frameMetricJet g F x).value k j * mvfderiv (𝓡 n) (C k) x (F i x) +
        (frameMetricJet g F x).value i k * mvfderiv (𝓡 n) (C k) x (F j x)) := by
  have hswap (a b : Fin n) :
      D.connection (F b) x (F a x) = D.connection (F a) x (F b x) := by
    have h := (D.connection.torsion_eq_zero_iff.mp D.torsion_eq_zero) (hF a) (hF b)
    rw [hbracket a b] at h
    exact sub_eq_zero.mp h
  have hfirst (k : Fin n) : (frameMetricJet g F x).first k i j =
      g.inner x (D.connection (F i) x (F k x)) (F j x) +
        g.inner x (F i x) (D.connection (F j) x (F k x)) :=
    D.mvfderiv_inner (F k) (F i) (F j) (hF i) (hF j)
  rw [metricLieDerivative_apply,
    connection_frame_expansion D F C W hF hC hW hrep (F i x),
    connection_frame_expansion D F C W hF hC hW hrep (F j x)]
  simp only [map_sum, map_add, map_smul, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [hswap i k, hswap j k, hfirst k]
  dsimp only [frameMetricJet]
  ring

theorem metricLieDerivative_intrinsicDeTurck_chartFrame
    {g background : RiemannianMetric n M}
    (D : LeviCivitaData g) (B : LeviCivitaData background) (p : M)
    {x : M} (hx : x ∈ (chartAt E p).source) (i j : Fin n) :
    metricLieDerivative D (intrinsicDeTurckField D B) x (chartFrame p i x) (chartFrame p j x) =
      lieDerivativeJet (frameMetricJet background (chartFrame p) x)
        (frameMetricJet g (chartFrame p) x) i j := by
  let C : Fin n → M → ℝ := fun k y =>
    deTurckVector (frameMetricJet background (chartFrame p) y)
      (frameMetricJet g (chartFrame p) y) k
  have hF (a : Fin n) := (chartFrame_contMDiffOn p a).contMDiffAt
    ((chartAt E p).open_source.mem_nhds hx)
  have hdet : (frameMetricJet g (chartFrame p) x).value.det ≠ 0 :=
    ne_of_gt (frameMetricJet_value_posDef g (chartFrame p) x
      (chartFrameBasis p x hx) (chartFrame_eq_basis p x hx)).det_pos
  have hdetB : (frameMetricJet background (chartFrame p) x).value.det ≠ 0 :=
    ne_of_gt (frameMetricJet_value_posDef background (chartFrame p) x
      (chartFrameBasis p x hx) (chartFrame_eq_basis p x hx)).det_pos
  have hC (k : Fin n) : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) (C k) x :=
    (frameDeTurck_contMDiffAt g background (chartFrame p) hF hdet hdetB k).mdifferentiableAt
      (by simp)
  have hW := (intrinsicDeTurckField_contMDiffAt D B x).mdifferentiableAt (by simp)
  have hrep : ∀ᶠ y in 𝓝 x, intrinsicDeTurckField D B y = ∑ k, C k y • chartFrame p k y := by
    filter_upwards [(chartAt E p).open_source.mem_nhds hx] with y hy
    exact intrinsicDeTurckField_eq_chartFrame_sum D B p hy
  rw [metricLieDerivative_frame D (chartFrame p) C (intrinsicDeTurckField D B)
    (fun a => (hF a).mdifferentiableAt (by simp)) hC hW hrep
    (chartFrame_mlieBracket_eq_zero p x hx) i j]
  unfold lieDerivativeJet
  apply Finset.sum_congr rfl
  intro k _
  dsimp only [C]
  rw [mvfderiv_deTurckVector_frameMetricJet g background (chartFrame p) hF hdet hdetB i k,
    mvfderiv_deTurckVector_frameMetricJet g background (chartFrame p) hF hdet hdetB j k]

theorem ricciDeTurckSource_frameMetricJet_eq_intrinsic
    {g background : RiemannianMetric n M}
    (D : LeviCivitaData g) (B : LeviCivitaData background) (p : M)
    {x : M} (hx : x ∈ (chartAt E p).source) (i j : Fin n) :
    ricciDeTurckSource (frameMetricJet background (chartFrame p) x)
        (frameMetricJet g (chartFrame p) x) i j =
      -2 * D.ricci x (chartFrame p i x) (chartFrame p j x) +
        metricLieDerivative D (intrinsicDeTurckField D B) x (chartFrame p i x) (chartFrame p j x) := by
  rw [ricci_eq_ricciJet_chartFrame D p hx,
    metricLieDerivative_intrinsicDeTurck_chartFrame D B p hx]
  rfl

theorem ricciDeTurckSource_coordinateMetricJet_eq_intrinsic
    {g background : RiemannianMetric n M}
    (D : LeviCivitaData g) (B : LeviCivitaData background) (p : M)
    {x : M} (hx : x ∈ (chartAt E p).source) (i j : Fin n) :
    ricciDeTurckSource
        (coordinateMetricJet (PiLp.basisFun 2 ℝ (Fin n))
          (chartMetricCoefficients background p) (extChartAt (𝓡 n) p x))
        (coordinateMetricJet (PiLp.basisFun 2 ℝ (Fin n))
          (chartMetricCoefficients g p) (extChartAt (𝓡 n) p x)) i j =
      -2 * D.ricci x (chartFrame p i x) (chartFrame p j x) +
        metricLieDerivative D (intrinsicDeTurckField D B) x (chartFrame p i x) (chartFrame p j x) := by
  rw [← frameMetricJet_eq_coordinateMetricJet background p hx,
    ← frameMetricJet_eq_coordinateMetricJet g p hx]
  exact ricciDeTurckSource_frameMetricJet_eq_intrinsic D B p hx i j

end PoincareConjecture.DeTurckNative

end
