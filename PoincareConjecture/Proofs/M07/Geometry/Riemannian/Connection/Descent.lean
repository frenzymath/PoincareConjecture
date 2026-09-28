import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Connection.Pullback









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology
open Bundle Filter Set VectorField

universe u v w

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

variable (g : RiemannianMetric n M)
  (cov : CovariantDerivative (𝓡 n) (EuclideanSpace ℝ (Fin n))
    (TangentSpace (𝓡 n) : M → Type _))
  (htorsion : cov.torsion = 0)
  (hmetric : letI : RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩; cov.IsMetricCompatible)

include htorsion hmetric

private theorem descent_koszul
    {X Y Z : (x : M) → TangentSpace (𝓡 n) x} {x : M}
    (hX : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (T% X) x)
    (hY : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (T% Y) x)
    (hZ : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (T% Z) x) :
    2 * g.inner x (cov Y x (X x)) (Z x) =
      mvfderiv (𝓡 n) (fun y => g.inner y (Y y) (Z y)) x (X x) +
      mvfderiv (𝓡 n) (fun y => g.inner y (Z y) (X y)) x (Y x) -
      mvfderiv (𝓡 n) (fun y => g.inner y (X y) (Y y)) x (Z x) +
      g.inner x (mlieBracket (𝓡 n) X Y x) (Z x) -
      g.inner x (mlieBracket (𝓡 n) Y Z x) (X x) +
      g.inner x (mlieBracket (𝓡 n) Z X x) (Y x) := by
  let : RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hm := CovariantDerivative.IsMetricCompatible.mvfderiv_inner_eq
    (cov := cov) (x := x) hmetric
  have hXY := cov.torsion_eq_zero_iff.mp htorsion hX hY
  have hYZ := cov.torsion_eq_zero_iff.mp htorsion hY hZ
  have hZX := cov.torsion_eq_zero_iff.mp htorsion hZ hX
  rw [show mvfderiv (𝓡 n) (fun y => g.inner y (Y y) (Z y)) x (X x) =
      g.inner x (cov Y x (X x)) (Z x) + g.inner x (Y x) (cov Z x (X x)) from
      hm X hY hZ,
    show mvfderiv (𝓡 n) (fun y => g.inner y (Z y) (X y)) x (Y x) =
      g.inner x (cov Z x (Y x)) (X x) + g.inner x (Z x) (cov X x (Y x)) from
      hm Y hZ hX,
    show mvfderiv (𝓡 n) (fun y => g.inner y (X y) (Y y)) x (Z x) =
      g.inner x (cov X x (Z x)) (Y x) + g.inner x (X x) (cov Y x (Z x)) from
      hm Z hX hY,
    ← hXY, ← hYZ, ← hZX]
  simp only [map_sub, sub_apply]
  rw [g.symm x (Y x), g.symm x (Z x), g.symm x (X x)]
  ring

private theorem descent_inner_smooth
    {X Y Z : (x : M) → TangentSpace (𝓡 n) x} {x : M}
    (hX : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% X) x)
    (hY : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% Y) x)
    (hZ : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% Z) x) :
    ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun y => g.inner y (cov Y y (X y)) (Z y)) x := by
  let : RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hi (A B : (x : M) → TangentSpace (𝓡 n) x)
      (hA : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        ∞ (T% A) x)
      (hB : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        ∞ (T% B) x) :
      ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y => g.inner y (A y) (B y)) x :=
    hA.inner_bundle hB
  have hs := (((((LeviCivitaData.contMDiffAt_mvfderiv_apply (hi Y Z hY hZ) hX).add
    (LeviCivitaData.contMDiffAt_mvfderiv_apply (hi Z X hZ hX) hY)).sub
    (LeviCivitaData.contMDiffAt_mvfderiv_apply (hi X Y hX hY) hZ)).add
    (hi _ Z (LeviCivitaData.contMDiffAt_mlieBracket hX hY) hZ)).sub
    (hi _ X (LeviCivitaData.contMDiffAt_mlieBracket hY hZ) hX)).add
    (hi _ Y (LeviCivitaData.contMDiffAt_mlieBracket hZ hX) hY)
  have hhalf := (ContinuousLinearMap.lsmul ℝ ℝ (1 / 2 : ℝ)).contDiff.contMDiff.contMDiffAt.comp x hs
  apply hhalf.congr_of_eventuallyEq
  filter_upwards [LeviCivitaData.eventually_mdifferentiableAt_of_contMDiffAt hX,
    LeviCivitaData.eventually_mdifferentiableAt_of_contMDiffAt hY,
    LeviCivitaData.eventually_mdifferentiableAt_of_contMDiffAt hZ] with y hyX hyY hyZ
  simp only [Function.comp_apply, ContinuousLinearMap.lsmul_apply, smul_eq_mul, Pi.add_apply]
  linarith [descent_koszul g cov htorsion hmetric hyX hyY hyZ]

private theorem descent_field_smooth
    {X Y : (x : M) → TangentSpace (𝓡 n) x} {x : M}
    (hX : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% X) x)
    (hY : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% Y) x) :
    ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (T% (fun y => cov Y y (X y))) x := by
  apply g.contMDiffAt_of_metricDual
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  apply contMDiffAt_clm_of_apply
  intro v
  let E := EuclideanSpace ℝ (Fin n)
  let V := TangentSpace (𝓡 n) (M := M)
  let e := trivializationAt E V x
  have hv : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) ∞
      (fun y => TotalSpace.mk' E y v) x := by
    rw [contMDiffAt_totalSpace]
    exact ⟨contMDiffAt_id, by simpa using contMDiffAt_const (c := v)⟩
  have hZ := (e.contMDiffAt_symmL (IB := 𝓡 n) (n := ∞)
    (FiberBundle.mem_baseSet_trivializationAt E V x)).clm_bundle_apply hv
  have h := descent_inner_smooth g cov htorsion hmetric hX hY hZ
  change ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞
    (fun y => (ContinuousLinearMap.inCoordinates E V ℝ (fun _ : M => ℝ)
      x y x y (g.inner y (cov Y y (X y)))) v) x
  have he : trivializationAt ℝ (fun _ : M => ℝ) x = Bundle.Trivial.trivialization M ℝ := rfl
  simpa only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply,
    he, Bundle.Trivial.continuousLinearMapAt_trivialization,
    ContinuousLinearMap.id_apply] using h



theorem smooth_covariantDerivative_of_torsion_eq_zero_of_metricCompatible :
    CovariantDerivative.ContMDiffCovariantDerivative cov ∞ := by
  constructor
  constructor
  intro Y hY
  apply contMDiffOn_univ.mpr
  intro x
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  apply contMDiffAt_clm_of_apply
  intro v
  let E := EuclideanSpace ℝ (Fin n)
  let V := TangentSpace (𝓡 n) (M := M)
  let e := trivializationAt E V x
  have hv : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) ∞
      (fun y => TotalSpace.mk' E y v) x := by
    rw [contMDiffAt_totalSpace]
    exact ⟨contMDiffAt_id, by simpa using contMDiffAt_const (c := v)⟩
  have hX := (e.contMDiffAt_symmL (IB := 𝓡 n) (n := ∞)
    (FiberBundle.mem_baseSet_trivializationAt E V x)).clm_bundle_apply hv
  have hfield := descent_field_smooth g cov htorsion hmetric hX
    ((contMDiffOn_univ.mp hY) x)
  have hc := (contMDiffAt_totalSpace.mp hfield).2
  apply hc.congr_of_eventuallyEq
  filter_upwards [e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt E V x)]
    with y hy
  simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply]
  rw [Bundle.Trivialization.continuousLinearMapAt_apply_of_mem ℝ _ hy]

end PoincareConjecture.RiemannianMetric

namespace PoincareConjecture.ConnectionDescent

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

private structure PointData (g : RiemannianMetric n M) (x : M) where
  toFun : ((y : M) → TangentSpace (𝓡 n) y) →
    TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x
  add {Y Z : (y : M) → TangentSpace (𝓡 n) y}
    (hY : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% Y) x)
    (hZ : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% Z) x) :
    toFun (Y + Z) = toFun Y + toFun Z
  leibniz {Y : (y : M) → TangentSpace (𝓡 n) y} {a : M → ℝ}
    (hY : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% Y) x)
    (ha : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) a x) :
    toFun (a • Y) = a x • toFun Y + (mvfderiv (𝓡 n) a x).smulRight (Y x)
  torsion {Y Z : (y : M) → TangentSpace (𝓡 n) y}
    (hY : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% Y) x)
    (hZ : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% Z) x) :
    toFun Z (Y x) - toFun Y (Z x) = mlieBracket (𝓡 n) Y Z x
  metric {Y Z : (y : M) → TangentSpace (𝓡 n) y}
    (hY : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% Y) x)
    (hZ : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% Z) x)
    (v : TangentSpace (𝓡 n) x) :
    mvfderiv (𝓡 n) (fun y => g.inner y (Y y) (Z y)) x v =
      g.inner x (toFun Y v) (Z x) + g.inner x (Y x) (toFun Z v)

private noncomputable def ofPointData (g : RiemannianMetric n M)
    (data : ∀ x, PointData g x) : LeviCivitaData g := by
  let cov : CovariantDerivative (𝓡 n) (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) := {
    toFun := fun Y x => (data x).toFun Y
    isCovariantDerivativeOnUniv := {
      add := fun hY hZ _ => (data _).add hY hZ
      leibniz := fun hY ha _ => (data _).leibniz hY ha } }
  have ht : cov.torsion = 0 := cov.torsion_eq_zero_iff.mpr
    (fun hY hZ => (data _).torsion hY hZ)
  let : RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hm : cov.IsMetricCompatible := (cov.isMetricCompatible_iff).mpr
    (fun _ hY hZ => (data _).metric hY hZ _)
  exact {
    connection := cov
    smooth := g.smooth_covariantDerivative_of_torsion_eq_zero_of_metricCompatible cov ht hm
    torsion_eq_zero := ht
    metricCompatible := hm }

variable {N : Type v} [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N] [IsManifold (𝓡 n) ∞ N]
  (g : RiemannianMetric n M) (h : RiemannianMetric n N) (D : LeviCivitaData h)
  (e : N → M) (he : ContMDiff (𝓡 n) (𝓡 n) ∞ e)
  (hinv : ∀ y, (mfderiv (𝓡 n) (𝓡 n) e y).IsInvertible)
  (hmetric : ∀ y (v w : TangentSpace (𝓡 n) y),
    h.inner y v w = g.inner (e y)
      (mfderiv (𝓡 n) (𝓡 n) e y v) (mfderiv (𝓡 n) (𝓡 n) e y w))

private noncomputable def transported (y : N)
    (Y : (x : M) → TangentSpace (𝓡 n) x) :
    TangentSpace (𝓡 n) (e y) →L[ℝ] TangentSpace (𝓡 n) (e y) :=
  (mfderiv (𝓡 n) (𝓡 n) e y).comp
    ((D.connection (mpullback (𝓡 n) (𝓡 n) e Y) y).comp
      (mfderiv (𝓡 n) (𝓡 n) e y).inverse)

include he hinv in
private theorem transported_add (y : N)
    {Y Z : (x : M) → TangentSpace (𝓡 n) x}
    (hY : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (T% Y) (e y))
    (hZ : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (T% Z) (e y)) :
    transported h D e y (Y + Z) = transported h D e y Y + transported h D e y Z := by
  have hpY := hY.mpullback_vectorField (he y) (hinv y) (by norm_cast)
  have hpZ := hZ.mpullback_vectorField (he y) (hinv y) (by norm_cast)
  simp only [transported, mpullback_add,
    D.connection.isCovariantDerivativeOn.add hpY hpZ,
    ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add]

include he hinv in
private theorem transported_leibniz (y : N)
    {Y : (x : M) → TangentSpace (𝓡 n) x} {a : M → ℝ}
    (hY : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (T% Y) (e y))
    (ha : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) a (e y)) :
    transported h D e y (a • Y) = a (e y) • transported h D e y Y +
      (mvfderiv (𝓡 n) a (e y)).smulRight (Y (e y)) := by
  have hpY := hY.mpullback_vectorField (he y) (hinv y) (by norm_cast)
  have ha' := ha.comp y ((he y).mdifferentiableAt (by simp))
  ext v
  simp only [transported, mpullback_smul,
    D.connection.isCovariantDerivativeOn.leibniz hpY ha',
    ContinuousLinearMap.comp_apply, add_apply,
    smul_apply, ContinuousLinearMap.smulRight_apply,
    Function.comp_apply, map_add, map_smul]
  rw [mvfderiv_comp y ha ((he y).mdifferentiableAt (by simp))]
  simp only [ContinuousLinearMap.comp_apply, mpullback, (hinv y).self_apply_inverse]

include he hinv in
private theorem transported_torsion (y : N)
    {Y Z : (x : M) → TangentSpace (𝓡 n) x}
    (hY : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (T% Y) (e y))
    (hZ : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (T% Z) (e y)) :
    transported h D e y Z (Y (e y)) - transported h D e y Y (Z (e y)) =
      mlieBracket (𝓡 n) Y Z (e y) := by
  have : IsManifold (𝓡 n) (minSmoothness ℝ 2) N := by
    simpa only [minSmoothness_of_isRCLikeNormedField] using
      (inferInstance : IsManifold (𝓡 n) 2 N)
  have : IsManifold (𝓡 n) (minSmoothness ℝ 2) M := by
    simpa only [minSmoothness_of_isRCLikeNormedField] using
      (inferInstance : IsManifold (𝓡 n) 2 M)
  have hpY := hY.mpullback_vectorField (he y) (hinv y) (by norm_cast)
  have hpZ := hZ.mpullback_vectorField (he y) (hinv y) (by norm_cast)
  have ht := D.connection.torsion_eq_zero_iff.mp D.torsion_eq_zero hpY hpZ
  have hb := mpullback_mlieBracket hY hZ (he y)
    (by simp only [minSmoothness_of_isRCLikeNormedField]; norm_cast)
  have hh := congrArg (mfderiv (𝓡 n) (𝓡 n) e y) ht
  simpa only [transported, ContinuousLinearMap.comp_apply, map_sub,
    ← hb, mpullback, (hinv y).self_apply_inverse] using hh

include hinv hmetric in
private theorem inner_mpullback (y : N)
    (Y Z : (x : M) → TangentSpace (𝓡 n) x) :
    h.inner y (mpullback (𝓡 n) (𝓡 n) e Y y) (mpullback (𝓡 n) (𝓡 n) e Z y) =
      g.inner (e y) (Y (e y)) (Z (e y)) := by
  rw [hmetric]
  simp only [mpullback, (hinv y).self_apply_inverse]

include he hinv hmetric in
private theorem transported_metric (y : N)
    {Y Z : (x : M) → TangentSpace (𝓡 n) x}
    (hY : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (T% Y) (e y))
    (hZ : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (T% Z) (e y)) (v : TangentSpace (𝓡 n) (e y)) :
    mvfderiv (𝓡 n) (fun x => g.inner x (Y x) (Z x)) (e y) v =
      g.inner (e y) (transported h D e y Y v) (Z (e y)) +
      g.inner (e y) (Y (e y)) (transported h D e y Z v) := by
  let : RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hscalar : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ)
      (fun x => g.inner x (Y x) (Z x)) (e y) := hY.inner_bundle hZ
  have hpY := hY.mpullback_vectorField (he y) (hinv y) (by norm_cast)
  have hpZ := hZ.mpullback_vectorField (he y) (hinv y) (by norm_cast)
  let w := (mfderiv (𝓡 n) (𝓡 n) e y).inverse v
  have hm := D.mvfderiv_inner_on_fields
    (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) w) hpY hpZ
  have hscalar_eq : (fun z => h.inner z (mpullback (𝓡 n) (𝓡 n) e Y z)
      (mpullback (𝓡 n) (𝓡 n) e Z z)) =
      (fun x => g.inner x (Y x) (Z x)) ∘ e := by
    funext z
    exact inner_mpullback g h e hinv hmetric z Y Z
  rw [hscalar_eq, mvfderiv_comp y hscalar ((he y).mdifferentiableAt (by simp))] at hm
  simp only [FiberBundle.extend_apply_self, ContinuousLinearMap.comp_apply,
    w, (hinv y).self_apply_inverse, LeviCivitaData.covariantDerivativeOnFields] at hm
  rw [hm, hmetric, hmetric]
  simp only [transported, ContinuousLinearMap.comp_apply, mpullback,
    (hinv y).self_apply_inverse]

private noncomputable def transportedPointData (y : N) : PointData g (e y) where
  toFun := transported h D e y
  add := transported_add h D e he hinv y
  leibniz := transported_leibniz h D e he hinv y
  torsion := transported_torsion h D e he hinv y
  metric := transported_metric g h D e he hinv hmetric y

end PoincareConjecture.ConnectionDescent

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]




noncomputable def leviCivitaDataOfCover
    {ι : Type w} {N : ι → Type v} [∀ i, TopologicalSpace (N i)]
    [∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (N i)]
    [∀ i, IsManifold (𝓡 n) ∞ (N i)]
    (g : RiemannianMetric n M) (h : ∀ i, RiemannianMetric n (N i))
    (D : ∀ i, LeviCivitaData (h i)) (e : ∀ i, N i → M)
    (he : ∀ i, ContMDiff (𝓡 n) (𝓡 n) ∞ (e i))
    (hinv : ∀ i y, (mfderiv (𝓡 n) (𝓡 n) (e i) y).IsInvertible)
    (hmetric : ∀ i y (v w : TangentSpace (𝓡 n) y),
      (h i).inner y v w = g.inner (e i y)
        (mfderiv (𝓡 n) (𝓡 n) (e i) y v) (mfderiv (𝓡 n) (𝓡 n) (e i) y w))
    (hcover : ∀ x, ∃ i y, e i y = x) : LeviCivitaData g := by
  classical
  have hdata : ∀ x, Nonempty (ConnectionDescent.PointData g x) := by
    intro x
    obtain ⟨i, y, rfl⟩ := hcover x
    exact ⟨ConnectionDescent.transportedPointData g (h i) (D i) (e i)
      (he i) (hinv i) (hmetric i) y⟩
  exact ConnectionDescent.ofPointData g (fun x => Classical.choice (hdata x))

end PoincareConjecture.RiemannianMetric
