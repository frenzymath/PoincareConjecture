import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Connection.EuclideanConstruction
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

set_option autoImplicit false
set_option maxSynthPendingDepth 8
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology
open Bundle Filter Set VectorField TopologicalSpace

namespace PoincareConjecture.RiemannianMetric

private abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

variable {n : ℕ} (U : Opens (E n))

private lemma chart_eq (x y : U) : chartAt (E n) x = chartAt (E n) y := by
  simp [Opens.chartAt_eq]

private lemma tangent_symmL (x y : U) :
    (trivializationAt (E n) (TangentSpace (𝓡 n)) x).symmL ℝ y =
      ContinuousLinearMap.id ℝ (E n) := by
  have hy : y ∈ (chartAt (E n) x).source := by
    rw [chart_eq U x y]
    exact mem_chart_source _ y
  rw [TangentBundle.symmL_trivializationAt_eq_core hy]
  have hchart : achart (E n) x = achart (E n) y := Subtype.ext (chart_eq U x y)
  rw [hchart]
  apply ContinuousLinearMap.ext
  intro v
  exact (tangentBundleCore (𝓡 n) U).coordChange_self
    (achart (E n) y) y (mem_chart_source _ y) v

private lemma tangent_coordinates (x y : U) (v : TangentSpace (𝓡 n) y) :
    (trivializationAt (E n) (TangentSpace (𝓡 n)) x) ⟨y, v⟩ = ⟨y, v⟩ := by
  have hy : y ∈ (trivializationAt (E n) (TangentSpace (𝓡 n)) x).baseSet := by
    simp [Opens.chartAt_eq]
  have h := (trivializationAt (E n) (TangentSpace (𝓡 n)) x).apply_mk_symm hy v
  rw [← Bundle.Trivialization.symmL_apply (R := ℝ) _ hy, tangent_symmL] at h
  exact h

private lemma field_mdifferentiable_iff
    (Y : (x : U) → TangentSpace (𝓡 n) x) (x : U) :
    MDifferentiableAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) (T% Y) x ↔
      MDifferentiableAt (𝓡 n) (𝓡 n) (fun y => Y y) x := by
  rw [mdifferentiableAt_totalSpace]
  simp only [tangent_coordinates]
  exact and_iff_right mdifferentiableAt_id

private lemma field_contMDiff_iff
    (Y : (x : U) → TangentSpace (𝓡 n) x) (x : U) :
    ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% Y) x ↔
      ContMDiffAt (𝓡 n) (𝓡 n) ∞ (fun y => Y y) x := by
  rw [Bundle.contMDiffAt_section]
  simp only [tangent_coordinates]

private lemma bilinear_coordinates (x y : U)
    (B : E n →L[ℝ] E n →L[ℝ] ℝ) :
    ContinuousLinearMap.inCoordinates (E n) (TangentSpace (𝓡 n))
      (E n →L[ℝ] ℝ) (fun z : U => TangentSpace (𝓡 n) z →L[ℝ] ℝ)
      x y x y B = B := by
  have hy : y ∈ (trivializationAt (E n →L[ℝ] ℝ)
      (fun z : U => TangentSpace (𝓡 n) z →L[ℝ] ℝ) x).baseSet := by
    simp [Opens.chartAt_eq]
  ext v w
  simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.coe_comp,
    Function.comp_apply, tangent_symmL]
  rw [Bundle.Trivialization.continuousLinearMapAt_apply_of_mem ℝ _ hy]
  simp +instances [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates,
    tangent_symmL]
  rfl

private lemma metric_coefficients_smooth (g : RiemannianMetric n U) (x : U) :
    ContMDiffAt (𝓡 n) 𝓘(ℝ, E n →L[ℝ] E n →L[ℝ] ℝ) ∞
      (show U → E n →L[ℝ] E n →L[ℝ] ℝ from g.inner) x := by
  have h := g.contMDiff x
  rw [Bundle.contMDiffAt_section] at h
  simpa only [hom_trivializationAt_apply, bilinear_coordinates] using h

private lemma tangent_inCoordinates
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : U → F) (A : U → E n →L[ℝ] F) (x y : U) :
    inTangentCoordinates (𝓡 n) 𝓘(ℝ, F) id f A x y = A y := by
  rw [inTangentCoordinates_eq]
  · have hchart : achart (E n) x = achart (E n) y := Subtype.ext (chart_eq U x y)
    simp only [id_eq, hchart]
    ext v
    simp only [ContinuousLinearMap.comp_apply]
    rw [(tangentBundleCore (𝓡 n) U).coordChange_self
      (achart (E n) y) y (mem_chart_source _ y)]
    simp +instances
  · simp [Opens.chartAt_eq]
  · simp

private lemma mvfderiv_smooth
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : U → F} {x : U} (hf : ContMDiffAt (𝓡 n) 𝓘(ℝ, F) ∞ f x) :
    ContMDiffAt (𝓡 n) 𝓘(ℝ, E n →L[ℝ] F) ∞
      (show U → E n →L[ℝ] F from mvfderiv (𝓡 n) f) x := by
  have h := hf.mfderiv_const (show ∞ + 1 ≤ (∞ : ℕ∞ω) by simp)
  convert! h using 1
  funext y
  exact (tangent_inCoordinates U f _ x y).symm

private noncomputable def koszulMap
    (B : E n →L[ℝ] E n →L[ℝ] E n →L[ℝ] ℝ) :
    E n →L[ℝ] E n →L[ℝ] E n →L[ℝ] ℝ :=
  let flipL := (ContinuousLinearMap.flipₗᵢ ℝ (E n) (E n) ℝ).toContinuousLinearMap
  (2⁻¹ : ℝ) • (B + (flipL.comp B).flip - flipL.comp B.flip)

private theorem koszulMap_apply
    (B : E n →L[ℝ] E n →L[ℝ] E n →L[ℝ] ℝ) (u v : E n) :
    koszulMap B u v = metricKoszulCovector B u v := by
  ext w
  rfl

private theorem contDiff_koszulMap : ContDiff ℝ ∞ (koszulMap (n := n)) := by
  unfold koszulMap
  have hf : ContDiff ℝ ∞ (fun B : E n →L[ℝ] E n →L[ℝ] ℝ => B.flip) :=
    (ContinuousLinearMap.flipₗᵢ ℝ (E n) (E n) ℝ).toContinuousLinearMap.contDiff
  have hf' : ContDiff ℝ ∞
      (fun B : E n →L[ℝ] E n →L[ℝ] E n →L[ℝ] ℝ => B.flip) :=
    (ContinuousLinearMap.flipₗᵢ ℝ (E n) (E n) (E n →L[ℝ] ℝ)).toContinuousLinearMap.contDiff
  fun_prop

private def coefficients (g : RiemannianMetric n U) :
    U → E n →L[ℝ] E n →L[ℝ] ℝ := g.inner

private noncomputable def metricDerivative (g : RiemannianMetric n U) :
    U → E n →L[ℝ] E n →L[ℝ] E n →L[ℝ] ℝ :=
  mvfderiv (𝓡 n) (coefficients U g)

private noncomputable def christoffel (g : RiemannianMetric n U) (x : U) :
    E n →L[ℝ] E n →L[ℝ] E n :=
  (ContinuousLinearMap.compL ℝ (E n) (E n →L[ℝ] ℝ) (E n)
    (coefficients U g x).inverse).comp (koszulMap (metricDerivative U g x))

private theorem christoffel_apply (g : RiemannianMetric n U) (x : U) (u v : E n) :
    christoffel U g x u v = (coefficients U g x).inverse
      (metricKoszulCovector (metricDerivative U g x) u v) := by
  simp only [christoffel, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.compL_apply, koszulMap_apply]

private theorem christoffel_smooth (g : RiemannianMetric n U) (x : U) :
    ContMDiffAt (𝓡 n) 𝓘(ℝ, E n →L[ℝ] E n →L[ℝ] E n) ∞
      (christoffel U g) x := by
  have hG := metric_coefficients_smooth U g x
  have hginv : (coefficients U g x).IsInvertible := by
    convert! g.inner_isInvertible x
  have hi : ContMDiffAt (𝓡 n) 𝓘(ℝ, (E n →L[ℝ] ℝ) →L[ℝ] E n) ∞
      (fun y => (coefficients U g y).inverse) x :=
    hginv.contDiffAt_map_inverse.contMDiffAt.comp x hG
  have hd := mvfderiv_smooth U hG
  have hk := contDiff_koszulMap.contMDiff.contMDiffAt.comp x hd
  unfold christoffel
  exact (ContMDiffAt.clm_apply contMDiffAt_const hi).clm_comp hk

private theorem metricDerivative_apply (g : RiemannianMetric n U)
    (x : U) (a b c : E n) :
    mvfderiv (𝓡 n) (fun y => g.inner y a b) x c =
      metricDerivative U g x c a b := by
  let L : (E n →L[ℝ] E n →L[ℝ] ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.apply ℝ ℝ b).comp
      (ContinuousLinearMap.apply ℝ (E n →L[ℝ] ℝ) a)
  have hG : MDifferentiableAt (𝓡 n) 𝓘(ℝ, E n →L[ℝ] E n →L[ℝ] ℝ)
      (coefficients U g) x :=
    (metric_coefficients_smooth U g x).mdifferentiableAt (by simp)
  have h := mfderiv_comp x (L.differentiableAt.mdifferentiableAt) hG
  have hL : mfderiv 𝓘(ℝ, E n →L[ℝ] E n →L[ℝ] ℝ) 𝓘(ℝ, ℝ)
      L (coefficients U g x) = L := by
    simpa only [mfderiv_eq_fderiv] using L.fderiv
  rw [hL] at h
  exact congrArg (fun A => A c) h

private theorem metricDerivative_symm (g : RiemannianMetric n U)
    (x : U) (a b c : E n) :
    metricDerivative U g x c a b = metricDerivative U g x c b a := by
  rw [← metricDerivative_apply, ← metricDerivative_apply]
  congr 2
  ext y
  exact g.symm y a b

private theorem inner_christoffel (g : RiemannianMetric n U)
    (x : U) (u v w : E n) :
    g.inner x (christoffel U g x u v) w =
      (2⁻¹ : ℝ) * (metricDerivative U g x u v w +
        metricDerivative U g x v w u - metricDerivative U g x w u v) := by
  rw [christoffel_apply]
  have hginv : (coefficients U g x).IsInvertible := by
    convert! g.inner_isInvertible x
  have hi := hginv.self_apply_inverse
    (metricKoszulCovector (metricDerivative U g x) u v)
  have h := congrArg (fun L => L w) hi
  simp only [metricKoszulCovector, smul_apply, add_apply, sub_apply,
    ContinuousLinearMap.flip_apply, smul_eq_mul] at h
  exact h

private theorem christoffel_symm (g : RiemannianMetric n U)
    (x : U) (u v : E n) :
    christoffel U g x u v = christoffel U g x v u := by
  have hginv : (coefficients U g x).IsInvertible := by
    convert! g.inner_isInvertible x
  apply hginv.injective
  ext w
  change g.inner x (christoffel U g x u v) w = g.inner x (christoffel U g x v u) w
  rw [inner_christoffel, inner_christoffel]
  rw [metricDerivative_symm U g x v w u,
    metricDerivative_symm U g x w u v, metricDerivative_symm U g x u v w]
  ring

private theorem inner_christoffel_add (g : RiemannianMetric n U)
    (x : U) (u v w : E n) :
    g.inner x (christoffel U g x u v) w + g.inner x v (christoffel U g x u w) =
      metricDerivative U g x u v w := by
  rw [g.symm x v, inner_christoffel, inner_christoffel]
  rw [metricDerivative_symm U g x w v u,
    metricDerivative_symm U g x v u w, metricDerivative_symm U g x u w v]
  ring

private noncomputable def vectorDerivative {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (Y : U → F) : U → E n →L[ℝ] F :=
  mvfderiv (𝓡 n) Y

private noncomputable def openConnection (g : RiemannianMetric n U) :
    CovariantDerivative (𝓡 n) (E n) (TangentSpace (𝓡 n) : U → Type _) where
  toFun Y x := vectorDerivative U Y x + (christoffel U g x).flip (Y x)
  isCovariantDerivativeOnUniv := {
    add := by
      intro Y Z x hY hZ hx
      have hY' := (field_mdifferentiable_iff U Y x).mp hY
      have hZ' := (field_mdifferentiable_iff U Z x).mp hZ
      change vectorDerivative U (Y + Z) x + (christoffel U g x).flip (Y x + Z x) =
        (vectorDerivative U Y x + (christoffel U g x).flip (Y x)) +
        (vectorDerivative U Z x + (christoffel U g x).flip (Z x))
      unfold vectorDerivative
      simp only [mvfderiv_add hY' hZ', map_add]
      abel
    leibniz := by
      intro Y f x hY hf hx
      have hY' := (field_mdifferentiable_iff U Y x).mp hY
      let S : U → E n := Y
      change vectorDerivative U (f • S) x + (christoffel U g x).flip (f x • S x) =
        f x • (vectorDerivative U S x + (christoffel U g x).flip (S x)) +
          (vectorDerivative U f x).smulRight (S x)
      unfold vectorDerivative
      rw [mvfderiv_smul hf hY', map_smul, smul_add]
      abel }

private theorem openConnection_const (g : RiemannianMetric n U)
    (x : U) (u v : E n) :
    openConnection U g (fun _ : U => v) x u = christoffel U g x u v := by
  simp [openConnection, vectorDerivative, mvfderiv_const]
  rfl

private theorem mfderiv_val (x : U) :
    mfderiv (𝓡 n) (𝓡 n) (Subtype.val : U → E n) x =
      ContinuousLinearMap.id ℝ (E n) := by
  have hc : (extChartAt (𝓡 n) x : U → E n) = Subtype.val := by
    ext y
    simp [extChartAt, Opens.chartAt_eq]
  rw [← hc]
  exact mfderiv_extChartAt_self

private theorem mlieBracket_const (x : U) (u v : E n) :
    mlieBracket (𝓡 n) (fun _ : U => u) (fun _ : U => v) x = 0 := by
  have hp (w : E n) : mpullback (𝓡 n) (𝓡 n) (Subtype.val : U → E n)
      (fun _ : E n => w) = fun _ : U => w := by
    funext y
    simp only [mpullback, mfderiv_val]
    change (ContinuousLinearMap.id ℝ (E n)).inverse w = w
    rw [ContinuousLinearMap.inverse_id]
    rfl
  have hd (w : E n) : MDifferentiableAt (𝓡 n) ((𝓡 n).prod (𝓡 n))
      (fun y : E n => TotalSpace.mk' (E n) y (E := TangentSpace (𝓡 n)) w) x.val := by
    rw [mdifferentiableAt_totalSpace]
    exact ⟨mdifferentiableAt_id, by simpa using
      (mdifferentiableAt_const (I := 𝓡 n) (I' := 𝓡 n) (c := w) (x := x.val))⟩
  have h := mpullback_mlieBracket (hd u) (hd v)
    (contMDiff_subtype_val (I := 𝓡 n) (U := U) (n := ∞) x)
    (by simp only [minSmoothness_of_isRCLikeNormedField]; norm_cast)
  rw [hp u, hp v] at h
  rw [← h]
  have he : mlieBracket (𝓡 n) (fun _ : E n => u) (fun _ : E n => v) = 0 := by
    funext z
    simp only [mlieBracket, mlieBracketWithin_eq_lieBracketWithin,
      lieBracketWithin, fderivWithin_univ, fderiv_const_apply]
    simp +instances
  rw [he]
  simp [mpullback]

private theorem openConnection_torsion (g : RiemannianMetric n U) :
    (openConnection U g).torsion = 0 := by
  funext x
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  have hd (w : E n) := (field_mdifferentiable_iff U (fun _ => w) x).mpr
    mdifferentiableAt_const
  have h := (openConnection U g).torsion_apply (hd u) (hd v)
  change (openConnection U g).torsion x u v = 0
  rw [h, openConnection_const, openConnection_const, christoffel_symm U g x u v]
  simp [mlieBracket_const]

private theorem openConnection_metricCompatible (g : RiemannianMetric n U) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : U → Type _) :=
      ⟨g.toRiemannianMetric⟩
    (openConnection U g).IsMetricCompatible := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : U → Type _) :=
    ⟨g.toRiemannianMetric⟩
  unfold CovariantDerivative.IsMetricCompatible
  funext x
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  apply ContinuousLinearMap.ext
  intro u
  have hd (a : E n) := (field_mdifferentiable_iff U (fun _ => a) x).mpr
    mdifferentiableAt_const
  have h := (openConnection U g).derivMetricTensor_apply (X := fun _ => u) x (hd v) (hd w)
  change (openConnection U g).derivMetricTensor x v w u = 0
  rw [h]
  change (mvfderiv (𝓡 n) (fun y => g.inner y v w) x) u -
    g.inner x (openConnection U g (fun _ => v) x u) w -
    g.inner x v (openConnection U g (fun _ => w) x u) = 0
  rw [openConnection_const, openConnection_const, metricDerivative_apply]
  linarith [inner_christoffel_add U g x u v w]

private theorem openConnection_smooth (g : RiemannianMetric n U) :
    CovariantDerivative.ContMDiffCovariantDerivative (openConnection U g) ∞ := by
  constructor
  constructor
  intro Y hY
  have hY' (x : U) : ContMDiffAt (𝓡 n) (𝓡 n) ∞ (fun y => Y y) x :=
    (field_contMDiff_iff U Y x).mp ((contMDiffOn_univ.mp hY) x)
  apply contMDiffOn_univ.mpr
  intro x
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  have hd := mvfderiv_smooth U (hY' x)
  have hc := christoffel_smooth U g x
  have hf : ContMDiff 𝓘(ℝ, E n →L[ℝ] E n →L[ℝ] E n)
      𝓘(ℝ, E n →L[ℝ] E n →L[ℝ] E n) ∞
      (fun B : E n →L[ℝ] E n →L[ℝ] E n => B.flip) :=
    (ContinuousLinearMap.flipₗᵢ ℝ (E n) (E n) (E n)).toContinuousLinearMap.contDiff.contMDiff
  have hh := hd.add ((hf.contMDiffAt.comp x hc).clm_apply (hY' x))
  convert! hh using 1
  funext y
  apply ContinuousLinearMap.ext
  intro u
  have hy : y ∈ (trivializationAt (E n) (TangentSpace (𝓡 n)) x).baseSet := by
    simp [Opens.chartAt_eq]
  simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply,
    tangent_symmL]
  rw [Bundle.Trivialization.continuousLinearMapAt_apply_of_mem ℝ _ hy]
  rw [tangent_coordinates]
  rfl

noncomputable def openEuclideanLeviCivitaData (g : RiemannianMetric n U) :
    LeviCivitaData g where
  connection := openConnection U g
  smooth := openConnection_smooth U g
  torsion_eq_zero := openConnection_torsion U g
  metricCompatible := openConnection_metricCompatible U g

end PoincareConjecture.RiemannianMetric
