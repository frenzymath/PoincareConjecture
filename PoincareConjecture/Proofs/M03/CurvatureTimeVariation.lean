import PoincareConjecture.Proofs.M03.ConnectionMovingField
import PoincareConjecture.Proofs.M03.CurvatureExtension
import PoincareConjecture.Proofs.M03.CurvatureHom
import PoincareConjecture.Proofs.M03.MetricInverse
import PoincareConjecture.Proofs.M03.CurvatureDerivativeTensoriality











set_option autoImplicit false
set_option maxHeartbeats 1800000

open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle Manifold Set

universe u

namespace PoincareConjecture.Proofs.M03

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem hasDerivAt_ricciFlow_curvature
    {J : Set ℝ} (F : RicciFlow n M J)
    {t : ℝ} (ht : t ∈ interior J)
    {U : Set M} (hU : IsOpen U)
    (X Y Z : (x : M) → TangentSpace (𝓡 n) x)
    (hX : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) U)
    (hY : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) U)
    (hZ : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Z) U)
    {x : M} (hx : x ∈ U) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric 0).toRiemannianMetric⟩
    let D := F.connection t
    let B := fun (A C : (y : M) → TangentSpace (𝓡 n) y) (y : M) =>
      deriv (fun s => (F.connection s).connection C y (A y)) t
    let nablaB := fun
        (A C E : (y : M) → TangentSpace (𝓡 n) y) (y : M) =>
      D.connection (B C E) y (A y) -
        B (fun z => D.connection C z (A z)) E y -
        B C (fun z => D.connection E z (A z)) y
    HasDerivAt
      (fun s => (F.connection s).curvature x (X x) (Y x) (Z x))
      (nablaB X Y Z x - nablaB Y X Z x) t := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric 0).toRiemannianMetric⟩
  let D := F.connection t
  let B := fun (A C : (y : M) → TangentSpace (𝓡 n) y) (y : M) =>
    deriv (fun s => (F.connection s).connection C y (A y)) t
  let nablaB := fun
      (A C E : (y : M) → TangentSpace (𝓡 n) y) (y : M) =>
    D.connection (B C E) y (A y) -
      B (fun z => D.connection C z (A z)) E y -
      B C (fun z => D.connection E z (A z)) y
  have hYZ := contMDiffOn_connection_family_apply F.smooth F.connection hU Z Y hZ hY
  have hXZ := contMDiffOn_connection_family_apply F.smooth F.connection hU Z X hZ hX
  have hfirst := hasDerivAt_ricciFlow_connection_moving_field F ht hU X
    (fun s y => (F.connection s).connection Z y (Y y)) hX hYZ hx
  have hsecond := hasDerivAt_ricciFlow_connection_moving_field F ht hU Y
    (fun s y => (F.connection s).connection Z y (X y)) hY hXZ hx
  change HasDerivAt
    (fun s => (F.connection s).connection
      (fun y => (F.connection s).connection Z y (Y y)) x (X x))
    (B X (fun y => D.connection Z y (Y y)) x + D.connection (B Y Z) x (X x)) t
    at hfirst
  change HasDerivAt
    (fun s => (F.connection s).connection
      (fun y => (F.connection s).connection Z y (X y)) x (Y x))
    (B Y (fun y => D.connection Z y (X y)) x + D.connection (B X Z) x (Y x)) t
    at hsecond
  let Axy := fun y => D.connection Y y (X y)
  let Ayx := fun y => D.connection X y (Y y)
  have hAxy := D.contMDiffOn_connection_apply hU X Y hX hY
  have hAyx := D.contMDiffOn_connection_apply hU Y X hY hX
  have hbr₁ := (family_tangent_time_derivative (F.metric 0) hU
    (fun s y => (F.connection s).connection Z y (Axy y))
    (contMDiffOn_connection_family_apply F.smooth F.connection hU Z Axy hZ hAxy) ht).1 x hx
  have hbr₂ := (family_tangent_time_derivative (F.metric 0) hU
    (fun s y => (F.connection s).connection Z y (Ayx y))
    (contMDiffOn_connection_family_apply F.smooth F.connection hU Z Ayx hZ hAyx) ht).1 x hx
  have htors := (D.connection.torsion_eq_zero_iff.mp D.torsion_eq_zero)
    ((hX.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp))
    ((hY.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp))
  have hbr : HasDerivAt
      (fun s => (F.connection s).connection Z x (VectorField.mlieBracket (𝓡 n) X Y x))
      (B Axy Z x - B Ayx Z x) t := by
    apply (hbr₁.sub hbr₂).congr_of_eventuallyEq
    filter_upwards [] with s
    rw [← htors, map_sub]
    rfl
  have hd := (hfirst.sub hsecond).sub hbr
  apply (hd.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun s =>
    curvature_eq_curvatureOnFields (F.connection s) hU X Y Z hX hY hZ hx))).congr_deriv
  dsimp only [nablaB, Axy, Ayx]
  module

theorem hasDerivAt_ricciFlow_curvature_derivative
    {J : Set ℝ} (F : RicciFlow n M J)
    {t : ℝ} (ht : t ∈ interior J)
    {U : Set M} (hU : IsOpen U)
    (P A B C : (x : M) → TangentSpace (𝓡 n) x)
    (hP : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% P) U)
    (hA : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% A) U)
    (hB : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% B) U)
    (hC : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% C) U)
    {x : M} (hx : x ∈ U) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric 0).toRiemannianMetric⟩
    let N := fun s (X Y : (y : M) → TangentSpace (𝓡 n) y) y =>
      (F.connection s).connection Y y (X y)
    let R := fun s (X Y Z : (y : M) → TangentSpace (𝓡 n) y) y =>
      (F.connection s).curvatureOnFields X Y Z y
    let K := fun s (X Y Z W : (y : M) → TangentSpace (𝓡 n) y) y =>
      N s X (R s Y Z W) y -
        R s (N s X Y) Z W y -
        R s Y (N s X Z) W y -
        R s Y Z (N s X W) y
    let dotR := fun (X Y Z : (y : M) → TangentSpace (𝓡 n) y) y =>
      deriv (fun s => R s X Y Z y) t
    let Btime := fun (X Y : (y : M) → TangentSpace (𝓡 n) y) y =>
      deriv (fun s => N s X Y y) t
    let nablaDotR := fun (X Y Z W : (y : M) → TangentSpace (𝓡 n) y) y =>
      N t X (dotR Y Z W) y -
        dotR (N t X Y) Z W y -
        dotR Y (N t X Z) W y -
        dotR Y Z (N t X W) y
    HasDerivAt (fun s => K s P A B C x)
      (nablaDotR P A B C x +
        Btime P (R t A B C) x -
        R t (Btime P A) B C x -
        R t A (Btime P B) C x -
        R t A B (Btime P C) x) t := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric 0).toRiemannianMetric⟩
  let : NormedAddCommGroup
      (TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x) := inferInstance
  let : NormedSpace ℝ
      (TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x) := inferInstance
  let : NormedAddCommGroup (TangentSpace (𝓡 n) x →L[ℝ]
      TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x) := inferInstance
  let : NormedSpace ℝ (TangentSpace (𝓡 n) x →L[ℝ]
      TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x) := inferInstance
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) x) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) x
  let N := fun s (X Y : (y : M) → TangentSpace (𝓡 n) y) y =>
    (F.connection s).connection Y y (X y)
  let R := fun s (X Y Z : (y : M) → TangentSpace (𝓡 n) y) y =>
    (F.connection s).curvatureOnFields X Y Z y
  let dotR := fun (X Y Z : (y : M) → TangentSpace (𝓡 n) y) y =>
    deriv (fun s => R s X Y Z y) t
  let Btime := fun (X Y : (y : M) → TangentSpace (𝓡 n) y) y =>
    deriv (fun s => N s X Y y) t
  have hNA := contMDiffOn_connection_family_apply F.smooth F.connection hU A P hA hP
  have hNB := contMDiffOn_connection_family_apply F.smooth F.connection hU B P hB hP
  have hNC := contMDiffOn_connection_family_apply F.smooth F.connection hU C P hC hP
  have hNAd := family_tangent_time_derivative (F.metric 0) hU (fun s => N s P A) hNA ht
  have hNBd := family_tangent_time_derivative (F.metric 0) hU (fun s => N s P B) hNB ht
  have hNCd := family_tangent_time_derivative (F.metric 0) hU (fun s => N s P C) hNC ht
  have hNAs (s : ℝ) := (F.connection s).contMDiffOn_connection_apply hU P A hP hA
  have hNBs (s : ℝ) := (F.connection s).contMDiffOn_connection_apply hU P B hP hB
  have hNCs (s : ℝ) := (F.connection s).contMDiffOn_connection_apply hU P C hP hC
  have hRABC : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n))
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun p : ℝ × M => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2
        (R p.1 A B C p.2)) (J ×ˢ U) := by
    apply (contMDiffOn_family_curvature F.smooth F.connection hU A B C hA hB hC).congr
    intro p hp
    congr 1
    exact (curvature_eq_curvatureOnFields (F.connection p.1) hU A B C hA hB hC hp.2).symm
  have houter := hasDerivAt_ricciFlow_connection_moving_field F ht hU P
    (fun s => R s A B C) hP hRABC hx
  change HasDerivAt (fun s => N s P (R s A B C) x)
    (Btime P (R t A B C) x + N t P (dotR A B C) x) t at houter
  choose RL hRL using fun s => exists_curvature_continuousTrilinearMap (F.connection s) x
  have hRLsmooth : ContDiffOn ℝ ∞ RL J := by
    apply contDiffOn_clm_apply.mpr
    intro a
    apply contDiffOn_clm_apply.mpr
    intro b
    apply contDiffOn_clm_apply.mpr
    intro c
    exact (contDiffOn_family_curvature_time F.smooth F.connection x a b c).congr
      (fun s _ => hRL s a b c)
  have hRLd := ((hRLsmooth.contDiffAt (mem_interior_iff_mem_nhds.mp ht)).differentiableAt
    (by simp)).hasDerivAt
  have hcurv (s : ℝ) (X Y Z : (y : M) → TangentSpace (𝓡 n) y)
      (hX : ContMDiffOn (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) U)
      (hY : ContMDiffOn (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) U)
      (hZ : ContMDiffOn (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Z) U) :
      RL s (X x) (Y x) (Z x) = R s X Y Z x :=
    (hRL s (X x) (Y x) (Z x)).trans
      (curvature_eq_curvatureOnFields (F.connection s) hU X Y Z hX hY hZ hx)
  have hfixed (X Y Z : (y : M) → TangentSpace (𝓡 n) y)
      (hX : ContMDiffOn (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) U)
      (hY : ContMDiffOn (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) U)
      (hZ : ContMDiffOn (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Z) U) :
      (deriv RL t) (X x) (Y x) (Z x) = dotR X Y Z x := by
    have hd := ((hRLd.clm_apply (hasDerivAt_const t (X x))).clm_apply
      (hasDerivAt_const t (Y x))).clm_apply (hasDerivAt_const t (Z x))
    have hd' : HasDerivAt (fun s => R s X Y Z x)
        ((deriv RL t) (X x) (Y x) (Z x)) t := by
      simpa only [map_zero, add_apply, zero_apply, add_zero] using hd.congr_of_eventuallyEq
          (Filter.Eventually.of_forall (fun s => (hcurv s X Y Z hX hY hZ).symm))
    exact hd'.deriv.symm
  have hfirst : HasDerivAt (fun s => R s (N s P A) B C x)
      (dotR (N t P A) B C x + R t (Btime P A) B C x) t := by
    have hd := ((hRLd.clm_apply (hNAd.1 x hx)).clm_apply
      (hasDerivAt_const t (B x))).clm_apply (hasDerivAt_const t (C x))
    apply (hd.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun s =>
      (hcurv s (N s P A) B C (hNAs s) hB hC).symm))).congr_deriv
    simp only [map_zero, add_apply, add_zero]
    rw [hfixed (N t P A) B C (hNAs t) hB hC,
      hcurv t (Btime P A) B C hNAd.2 hB hC]
  have hsecond : HasDerivAt (fun s => R s A (N s P B) C x)
      (dotR A (N t P B) C x + R t A (Btime P B) C x) t := by
    have hd := ((hRLd.clm_apply (hasDerivAt_const t (A x))).clm_apply
      (hNBd.1 x hx)).clm_apply (hasDerivAt_const t (C x))
    apply (hd.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun s =>
      (hcurv s A (N s P B) C hA (hNBs s) hC).symm))).congr_deriv
    simp only [map_zero, add_apply, add_zero]
    rw [hfixed A (N t P B) C hA (hNBs t) hC,
      hcurv t A (Btime P B) C hA hNBd.2 hC]
  have hthird : HasDerivAt (fun s => R s A B (N s P C) x)
      (dotR A B (N t P C) x + R t A B (Btime P C) x) t := by
    have hd := ((hRLd.clm_apply (hasDerivAt_const t (A x))).clm_apply
      (hasDerivAt_const t (B x))).clm_apply (hNCd.1 x hx)
    apply (hd.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun s =>
      (hcurv s A B (N s P C) hA hB (hNCs s)).symm))).congr_deriv
    simp only [map_zero, add_zero]
    rw [hfixed A B (N t P C) hA hB (hNCs t),
      hcurv t A B (Btime P C) hA hB hNCd.2]
  apply (((houter.sub hfirst).sub hsecond).sub hthird).congr_deriv
  dsimp only
  module

set_option synthInstance.maxHeartbeats 200000 in

theorem hasDerivAt_ricciFlow_curvature_derivative_squared_norm_frame
    {J : Set ℝ} (F : RicciFlow n M J) {t : ℝ} (ht : t ∈ interior J)
    (x0 : M) {x : M}
    (hx : x ∈ (trivializationAt (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n)) x0).baseSet) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric 0).toRiemannianMetric⟩
    let V := EuclideanSpace ℝ (Fin n)
    let e := trivializationAt V (TangentSpace (𝓡 n)) x0
    let E := e.localFrame (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    let G := fun s : ℝ => ContinuousLinearMap.inCoordinates V
      (TangentSpace (𝓡 n)) (V →L[ℝ] ℝ)
      (fun y => TangentSpace (𝓡 n) y →L[ℝ] ℝ) x0 x x0 x ((F.metric s).inner x)
    let a := fun (s : ℝ) (i j : Fin n) =>
      (ContinuousLinearMap.inverse (G s) (EuclideanSpace.proj j)) i
    let N := fun s (A B : (y : M) → TangentSpace (𝓡 n) y) y =>
      (F.connection s).connection B y (A y)
    let R := fun s (A B C : (y : M) → TangentSpace (𝓡 n) y) y =>
      (F.connection s).curvatureOnFields A B C y
    let K := fun s (A B C D : (y : M) → TangentSpace (𝓡 n) y) y =>
      N s A (R s B C D) y - R s (N s A B) C D y -
        R s B (N s A C) D y - R s B C (N s A D) y
    let k := fun s (α : Fin 4 → Fin n) =>
      K s (E (α 0)) (E (α 1)) (E (α 2)) (E (α 3)) x
    let dotk := fun α => deriv (fun s => k s α) t
    let raised := fun i => e.symmL ℝ x ((G t).inverse (EuclideanSpace.proj i))
    let W := fun s (α β : Fin 4 → Fin n) => ∏ r, a s (α r) (β r)
    HasDerivAt
      (fun s => ∑ α, ∑ β, W s α β * (F.metric s).inner x (k s α) (k s β))
      (2 * (∑ α, ∑ β, W t α β * (F.metric t).inner x (dotk α) (k t β)) -
        2 * (∑ α, ∑ β, W t α β * (F.connection t).ricci x (k t α) (k t β)) +
        ∑ α, ∑ β, ∑ r : Fin 4,
          2 * (F.connection t).ricci x (raised (β r)) (raised (α r)) *
            (∏ s ∈ Finset.univ.erase r, a t (α s) (β s)) *
              (F.metric t).inner x (k t α) (k t β)) t := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric 0).toRiemannianMetric⟩
  let : NormedAddCommGroup (TangentSpace (𝓡 n) x →L[ℝ] ℝ) := inferInstance
  let : NormedSpace ℝ (TangentSpace (𝓡 n) x →L[ℝ] ℝ) := inferInstance
  let : NormedAddCommGroup (TangentSpace (𝓡 n) x →L[ℝ]
      TangentSpace (𝓡 n) x →L[ℝ] ℝ) := inferInstance
  let : NormedSpace ℝ (TangentSpace (𝓡 n) x →L[ℝ]
      TangentSpace (𝓡 n) x →L[ℝ] ℝ) := inferInstance
  let V := EuclideanSpace ℝ (Fin n)
  let e := trivializationAt V (TangentSpace (𝓡 n)) x0
  let E := e.localFrame (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let G := fun s : ℝ => ContinuousLinearMap.inCoordinates V
    (TangentSpace (𝓡 n)) (V →L[ℝ] ℝ)
    (fun y => TangentSpace (𝓡 n) y →L[ℝ] ℝ) x0 x x0 x ((F.metric s).inner x)
  let a := fun (s : ℝ) (i j : Fin n) =>
    (ContinuousLinearMap.inverse (G s) (EuclideanSpace.proj j)) i
  let N := fun s (A B : (y : M) → TangentSpace (𝓡 n) y) y =>
    (F.connection s).connection B y (A y)
  let R := fun s (A B C : (y : M) → TangentSpace (𝓡 n) y) y =>
    (F.connection s).curvatureOnFields A B C y
  let K := fun s (A B C D : (y : M) → TangentSpace (𝓡 n) y) y =>
    N s A (R s B C D) y - R s (N s A B) C D y -
      R s B (N s A C) D y - R s B C (N s A D) y
  let k := fun s (α : Fin 4 → Fin n) =>
    K s (E (α 0)) (E (α 1)) (E (α 2)) (E (α 3)) x
  let dotk := fun α => deriv (fun s => k s α) t
  let raised := fun i => e.symmL ℝ x ((G t).inverse (EuclideanSpace.proj i))
  let W := fun s (α β : Fin 4 → Fin n) => ∏ r, a s (α r) (β r)
  let B := fun s : ℝ => (F.metric s).inner x
  let ric := (F.connection t).ricci x
  have htJ : J ∈ 𝓝 t := mem_interior_iff_mem_nhds.mp ht
  have hB : HasDerivAt B (deriv B t) t :=
    (((contDiffOn_family_metric_inner_time F.smooth x).contDiffAt htJ).differentiableAt
      (by simp)).hasDerivAt
  have hBval (v w : TangentSpace (𝓡 n) x) : (deriv B t) v w = -2 * ric v w := by
    have hh := (hB.clm_apply (hasDerivAt_const t v)).clm_apply (hasDerivAt_const t w)
    have hh' : HasDerivAt (fun s => B s v w) ((deriv B t) v w) t := by
      simpa only [map_zero, add_zero] using hh
    exact hh'.unique ((F.equation t (interior_subset ht) x v w).hasDerivAt htJ)
  have hmetric (s : ℝ) (v w : V) :
      G s v w = B s (e.symmL ℝ x v) (e.symmL ℝ x w) := by
    dsimp only [G, B]
    rw [inCoordinates_apply_eq₂
      (F₁ := V) (F₂ := V) (F₃ := ℝ)
      (E₁ := TangentSpace (𝓡 n)) (E₂ := TangentSpace (𝓡 n))
      (E₃ := fun _ : M => ℝ) hx hx (by simp)]
    rw [← Trivialization.symmL_apply (R := ℝ) e hx v,
      ← Trivialization.symmL_apply (R := ℝ) e hx w]
    simp only [Trivial.fiberBundle_trivializationAt', Trivial.linearMapAt_trivialization,
      LinearMap.id_coe, id_eq]
  have hInv := contMDiffOn_family_metric_frame_inverse F.smooth x0
  have hGi (s : ℝ) : (G s).IsInvertible := hInv.1 (s, x) hx
  have hmap : ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
      (fun s : ℝ => (s, x)) t := contMDiffAt_id.prodMk contMDiffAt_const
  have hGd : HasDerivAt G (deriv G t) t := by
    have hh := (hInv.2.1.contMDiffAt
      (prod_mem_nhds htJ (e.open_baseSet.mem_nhds hx))).comp t hmap
    exact (hh.contDiffAt.differentiableAt (by simp)).hasDerivAt
  have hId : HasDerivAt (fun s => (G s).inverse)
      (deriv (fun s => (G s).inverse) t) t := by
    have hh := (hInv.2.2.contMDiffAt
      (prod_mem_nhds htJ (e.open_baseSet.mem_nhds hx))).comp t hmap
    exact (hh.contDiffAt.differentiableAt (by simp)).hasDerivAt
  have hGval (v w : V) :
      (deriv G t) v w = -2 * ric (e.symmL ℝ x v) (e.symmL ℝ x w) := by
    have hd := (hGd.clm_apply (hasDerivAt_const t v)).clm_apply (hasDerivAt_const t w)
    have hd' : HasDerivAt (fun s => G s v w) ((deriv G t) v w) t := by
      simpa only [map_zero, add_zero] using hd
    exact hd'.unique (((F.equation t (interior_subset ht) x
      (e.symmL ℝ x v) (e.symmL ℝ x w)).hasDerivAt htJ).congr_of_eventuallyEq
        (Filter.Eventually.of_forall (fun s => hmetric s v w)))
  have hsymG (s : ℝ) (v w : V) : G s v w = G s w v := by
    rw [hmetric, hmetric]
    exact (F.metric s).symm x _ _
  have had (i j : Fin n) :
      HasDerivAt (fun s => a s i j) (2 * ric (raised j) (raised i)) t := by
    let v := (G t).inverse (EuclideanSpace.proj i)
    let w := (G t).inverse (EuclideanSpace.proj j)
    let wd := (deriv (fun s => (G s).inverse) t) (EuclideanSpace.proj j)
    have hw : HasDerivAt (fun s => (G s).inverse (EuclideanSpace.proj j)) wd t := by
      simpa only [map_zero, add_zero] using hId.clm_apply
        (hasDerivAt_const t (EuclideanSpace.proj j))
    have hzero : (deriv G t) w v + G t wd v = 0 := by
      have hd := (hGd.clm_apply hw).clm_apply (hasDerivAt_const t v)
      have heq : (fun _ : ℝ => (EuclideanSpace.proj j) v) =ᶠ[𝓝 t]
          (fun s => G s ((G s).inverse (EuclideanSpace.proj j)) v) := by
        filter_upwards [] with s
        exact (congrArg (fun L : V →L[ℝ] ℝ => L v)
          ((hGi s).self_apply_inverse (EuclideanSpace.proj j))).symm
      have hd' : HasDerivAt (fun _ : ℝ => (EuclideanSpace.proj j) v)
          ((deriv G t) w v + G t wd v) t := by
        simpa only [w, map_zero, add_zero, add_apply] using hd.congr_of_eventuallyEq heq
      exact hd'.unique (hasDerivAt_const t _)
    have hsecond : G t wd v = wd i := by
      rw [hsymG]
      exact congrArg (fun L : V →L[ℝ] ℝ => L wd)
        ((hGi t).self_apply_inverse (EuclideanSpace.proj i))
    rw [hGval, hsecond] at hzero
    have hd : HasDerivAt (fun s => a s i j) (wd i) t := by
      have hh := (EuclideanSpace.proj i : V →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t hw
      change HasDerivAt (fun s => a s i j) (wd i) t at hh
      exact hh
    apply hd.congr_deriv
    change wd i = 2 * ric (e.symmL ℝ x w) (e.symmL ℝ x v)
    linarith
  have hasymm (i j : Fin n) : a t i j = a t j i := by
    calc
      a t i j = G t ((G t).inverse (EuclideanSpace.proj i))
          ((G t).inverse (EuclideanSpace.proj j)) := by
        rw [(hGi t).self_apply_inverse]
        rfl
      _ = G t ((G t).inverse (EuclideanSpace.proj j))
          ((G t).inverse (EuclideanSpace.proj i)) := hsymG _ _ _
      _ = a t j i := by
        rw [(hGi t).self_apply_inverse]
        rfl
  have hE (i : Fin n) : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% (E i)) e.baseSet :=
    e.contMDiffOn_localFrame_baseSet (I := 𝓡 n) ∞ _ i
  have hkd (α : Fin 4 → Fin n) : HasDerivAt (fun s => k s α) (dotk α) t :=
    (hasDerivAt_ricciFlow_curvature_derivative F ht e.open_baseSet
      (E (α 0)) (E (α 1)) (E (α 2)) (E (α 3))
      (hE _) (hE _) (hE _) (hE _) hx).differentiableAt.hasDerivAt
  have hWd (α β : Fin 4 → Fin n) : HasDerivAt (fun s => W s α β)
      (∑ r : Fin 4, (∏ s ∈ Finset.univ.erase r, a t (α s) (β s)) *
        (2 * ric (raised (β r)) (raised (α r)))) t := by
    simpa only [W, smul_eq_mul] using HasDerivAt.fun_finsetProd
      (u := (Finset.univ : Finset (Fin 4))) (fun r _ => had (α r) (β r))
  have hp (α β : Fin 4 → Fin n) : HasDerivAt
      (fun s => B s (k s α) (k s β))
      (-2 * ric (k t α) (k t β) + B t (dotk α) (k t β) +
        B t (k t α) (dotk β)) t := by
    have hd := (hB.clm_apply (hkd α)).clm_apply (hkd β)
    apply hd.congr_deriv
    simp only [add_apply, hBval]
  have hWsymm (α β : Fin 4 → Fin n) : W t α β = W t β α := by
    apply Finset.prod_congr rfl
    intro r _
    exact hasymm _ _
  have hpair : (∑ α, ∑ β, W t α β * B t (k t α) (dotk β)) =
      ∑ α, ∑ β, W t α β * B t (dotk α) (k t β) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro α _
    apply Finset.sum_congr rfl
    intro β _
    rw [hWsymm β α, (F.metric t).symm]
  have hd := HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin 4 → Fin n)))
    (fun α _ => HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin 4 → Fin n)))
      (fun β _ => (hWd α β).mul (hp α β)))
  change HasDerivAt
    (fun s => ∑ α, ∑ β, W s α β * B s (k s α) (k s β))
    (2 * (∑ α, ∑ β, W t α β * B t (dotk α) (k t β)) -
      2 * (∑ α, ∑ β, W t α β * ric (k t α) (k t β)) +
      ∑ α, ∑ β, ∑ r : Fin 4,
        2 * ric (raised (β r)) (raised (α r)) *
          (∏ s ∈ Finset.univ.erase r, a t (α s) (β s)) *
            B t (k t α) (k t β)) t
  apply hd.congr_deriv
  change (∑ α, ∑ β,
      ((∑ r : Fin 4, (∏ s ∈ Finset.univ.erase r, a t (α s) (β s)) *
          (2 * ric (raised (β r)) (raised (α r)))) * B t (k t α) (k t β) +
        W t α β * (-2 * ric (k t α) (k t β) + B t (dotk α) (k t β) +
          B t (k t α) (dotk β)))) = _
  simp only [Finset.sum_add_distrib, mul_add]
  rw [hpair]
  have htime : (∑ α, ∑ β,
      (∑ r : Fin 4, (∏ s ∈ Finset.univ.erase r, a t (α s) (β s)) *
        (2 * ric (raised (β r)) (raised (α r)))) * B t (k t α) (k t β)) =
      ∑ α, ∑ β, ∑ r : Fin 4,
        2 * ric (raised (β r)) (raised (α r)) *
          (∏ s ∈ Finset.univ.erase r, a t (α s) (β s)) * B t (k t α) (k t β) := by
    simp only [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro α _
    apply Finset.sum_congr rfl
    intro β _
    apply Finset.sum_congr rfl
    intro r _
    ring
  rw [htime]
  have hneg : (∑ α, ∑ β, W t α β * (-2 * ric (k t α) (k t β))) =
      -2 * (∑ α, ∑ β, W t α β * ric (k t α) (k t β)) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro α _
    apply Finset.sum_congr rfl
    intro β _
    ring
  rw [hneg]
  ring

open Bundle Manifold in
set_option maxHeartbeats 2400000 in
set_option synthInstance.maxHeartbeats 200000 in

theorem curvature_derivative_squared_norm_frame_eq_orthonormal
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g) (x0 : M) {x : M}
    (hx : x ∈ (trivializationAt (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n)) x0).baseSet) :
    let V := EuclideanSpace ℝ (Fin n)
    let e := trivializationAt V (TangentSpace (𝓡 n)) x0
    let E := e.localFrame (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    let G := ContinuousLinearMap.inCoordinates V (TangentSpace (𝓡 n))
      (V →L[ℝ] ℝ) (fun y => TangentSpace (𝓡 n) y →L[ℝ] ℝ)
      x0 x x0 x (g.inner x)
    let a := fun i j : Fin n => (G.inverse (EuclideanSpace.proj j)) i
    let N := fun (P Q : (y : M) → TangentSpace (𝓡 n) y) y =>
      D.connection Q y (P y)
    let R := fun (A B C : (y : M) → TangentSpace (𝓡 n) y) y =>
      D.curvatureOnFields A B C y
    let K := fun (P A B C : (y : M) → TangentSpace (𝓡 n) y) y =>
      N P (R A B C) y - R (N P A) B C y -
        R A (N P B) C y - R A B (N P C) y
    let b := g.orthonormalBasis x
    let ext := fun i => FiberBundle.extend V (b i)
    let k := fun (α : Fin 4 → Fin n) =>
      K (E (α 0)) (E (α 1)) (E (α 2)) (E (α 3)) x
    let kb := fun (γ : Fin 4 → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) =>
      K (ext (γ 0)) (ext (γ 1)) (ext (γ 2)) (ext (γ 3)) x
    (∑ α, ∑ β, (∏ r, a (α r) (β r)) * g.inner x (k α) (k β)) =
      ∑ γ, g.inner x (kb γ) (kb γ) := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let V := EuclideanSpace ℝ (Fin n)
  let e := trivializationAt V (TangentSpace (𝓡 n)) x0
  let cb := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let E := e.localFrame cb
  let theta := e.localFrameCoeff (𝓡 n) cb
  let G := ContinuousLinearMap.inCoordinates V (TangentSpace (𝓡 n))
    (V →L[ℝ] ℝ) (fun y => TangentSpace (𝓡 n) y →L[ℝ] ℝ)
    x0 x x0 x (g.inner x)
  let a := fun i j : Fin n => (G.inverse (EuclideanSpace.proj j)) i
  let N := fun (P Q : (y : M) → TangentSpace (𝓡 n) y) y =>
    D.connection Q y (P y)
  let R := fun (A B C : (y : M) → TangentSpace (𝓡 n) y) y =>
    D.curvatureOnFields A B C y
  let K := fun (P A B C : (y : M) → TangentSpace (𝓡 n) y) y =>
    N P (R A B C) y - R (N P A) B C y -
      R A (N P B) C y - R A B (N P C) y
  let b := g.orthonormalBasis x
  let ι := Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))
  let ext := fun i : ι => FiberBundle.extend V (b i)
  let k := fun (α : Fin 4 → Fin n) =>
    K (E (α 0)) (E (α 1)) (E (α 2)) (E (α 3)) x
  let kb := fun (γ : Fin 4 → ι) =>
    K (ext (γ 0)) (ext (γ 1)) (ext (γ 2)) (ext (γ 3)) x
  let W := fun (α β : Fin 4 → Fin n) => ∏ r, a (α r) (β r)
  let d := fun (γ : Fin 4 → ι) (α : Fin 4 → Fin n) =>
    ∏ r, theta (α r) x (b (γ r))
  change (∑ α, ∑ β, W α β * g.inner x (k α) (k β)) =
    ∑ γ, g.inner x (kb γ) (kb γ)
  obtain ⟨T, hT⟩ := exists_curvatureOnFields_derivative_quadrilinearMap D x
  let L : MultilinearMap ℝ (fun _ : Fin 4 => TangentSpace (𝓡 n) x)
      (TangentSpace (𝓡 n) x) :=
    MultilinearMap.mk' (fun z => T (z 0) (z 1) (z 2) (z 3))
      (by
        intro z i v w
        fin_cases i <;> simp [Function.update_apply, map_add, LinearMap.add_apply])
      (by
        intro z i c v
        fin_cases i <;> simp [Function.update_apply, map_smul, LinearMap.smul_apply])
  have hE (i : Fin n) : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% (E i)) e.baseSet :=
    e.contMDiffOn_localFrame_baseSet (I := 𝓡 n) ∞ cb i
  have hEL (α : Fin 4 → Fin n) : L (fun r => E (α r) x) = k α :=
    hT e.open_baseSet (E (α 0)) (E (α 1)) (E (α 2)) (E (α 3))
      (hE (α 0)) (hE (α 1)) (hE (α 2)) (hE (α 3)) hx
  let e0 := trivializationAt V (TangentSpace (𝓡 n)) x
  have hx0 : x ∈ e0.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  have hExt (i : ι) : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% (ext i)) e0.baseSet := by
    have hc : ContMDiffOn (𝓡 n) 𝓘(ℝ, V) ∞
        (fun _y : M => (e0 ⟨x, b i⟩).2) e0.baseSet := contMDiffOn_const
    have hec : ContMDiffOn (𝓡 n) 𝓘(ℝ, V) ∞
        (fun y => (e0 ⟨y, ext i y⟩).2) e0.baseSet := by
      apply hc.congr
      intro y hy
      change (e0 ⟨y, e0.symm y (e0 ⟨x, b i⟩).2⟩).2 = (e0 ⟨x, b i⟩).2
      simpa only using congrArg Prod.snd (e0.apply_mk_symm hy (e0 ⟨x, b i⟩).2)
    intro y hy
    rw [e0.contMDiffWithinAt_section _ hy]
    exact hec y hy
  have hBL (γ : Fin 4 → ι) : L (fun r => b (γ r)) = kb γ := by
    have hh := hT e0.open_baseSet (ext (γ 0)) (ext (γ 1)) (ext (γ 2)) (ext (γ 3))
      (hExt (γ 0)) (hExt (γ 1)) (hExt (γ 2)) (hExt (γ 3)) hx0
    change T (ext (γ 0) x) (ext (γ 1) x) (ext (γ 2) x) (ext (γ 3) x) = kb γ at hh
    change T (b (γ 0)) (b (γ 1)) (b (γ 2)) (b (γ 3)) = kb γ
    simpa only [ext, FiberBundle.extend_apply_self] using hh
  have hrec (z : TangentSpace (𝓡 n) x) :
      z = ∑ i : Fin n, theta i x z • E i x := by
    simpa only [FiberBundle.extend_apply_self] using
      e.eq_sum_localFrameCoeff_smul (I := 𝓡 n) (b := cb)
        (s := FiberBundle.extend V z) hx
  have hExpand (γ : Fin 4 → ι) :
      L (fun r => b (γ r)) = ∑ α : Fin 4 → Fin n,
        d γ α • L (fun r => E (α r) x) := by
    calc
      _ = L (fun r => ∑ i : Fin n, theta i x (b (γ r)) • E i x) :=
        congrArg L (funext fun r => hrec (b (γ r)))
      _ = ∑ α : Fin 4 → Fin n,
          L (fun r => theta (α r) x (b (γ r)) • E (α r) x) :=
        L.map_sum (fun r i => theta i x (b (γ r)) • E i x)
      _ = _ := by simp only [MultilinearMap.map_smul_univ, d]
  have htrace (i j : Fin n) : a i j =
      ∑ r, theta i x (b r) * theta j x (b r) :=
    metric_inverse_eq_sum_orthonormal_coordinates g x0 x hx i j
  have hWeight (α β : Fin 4 → Fin n) :
      W α β = ∑ γ : Fin 4 → ι, d γ α * d γ β := by
    dsimp only [W]
    simp_rw [htrace]
    rw [Fintype.prod_sum]
    simp only [d, Finset.prod_mul_distrib]
    rfl
  have hPair (v : (Fin 4 → Fin n) → TangentSpace (𝓡 n) x) :
      (∑ γ : Fin 4 → ι, g.inner x (∑ α, d γ α • v α) (∑ β, d γ β • v β)) =
        ∑ α, ∑ β, W α β * g.inner x (v α) (v β) := by
    simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro α _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro β _
    simp_rw [← mul_assoc]
    rw [← Finset.sum_mul, ← hWeight]
    rw [g.symm x (v β) (v α)]
  calc
    _ = ∑ α, ∑ β, W α β *
        g.inner x (L (fun r => E (α r) x)) (L (fun r => E (β r) x)) := by
      simp only [hEL]
    _ = ∑ γ : Fin 4 → ι,
        g.inner x (∑ α, d γ α • L (fun r => E (α r) x))
          (∑ β, d γ β • L (fun r => E (β r) x)) := (hPair _).symm
    _ = ∑ γ : Fin 4 → ι, g.inner x (L (fun r => b (γ r)))
        (L (fun r => b (γ r))) := by simp only [← hExpand]
    _ = _ := by simp only [hBL]

set_option maxHeartbeats 2400000 in
set_option synthInstance.maxHeartbeats 200000 in

theorem curvature_derivative_tangentNorm_le_orthonormal_energy
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    {U : Set M} (hU : IsOpen U)
    (P A B C : (y : M) → TangentSpace (𝓡 n) y)
    (hP : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% P) U)
    (hA : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% A) U)
    (hB : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% B) U)
    (hC : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% C) U)
    {x : M} (hx : x ∈ U) :
    let N := fun (V W : (y : M) → TangentSpace (𝓡 n) y) y =>
      D.connection W y (V y)
    let R := fun (V W Z : (y : M) → TangentSpace (𝓡 n) y) y =>
      D.curvatureOnFields V W Z y
    let K := fun (V W Z L : (y : M) → TangentSpace (𝓡 n) y) y =>
      N V (R W Z L) y - R (N V W) Z L y -
        R W (N V Z) L y - R W Z (N V L) y
    let b := g.orthonormalBasis x
    let ext := fun i => FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (b i)
    let kb := fun (γ : Fin 4 → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) =>
      K (ext (γ 0)) (ext (γ 1)) (ext (γ 2)) (ext (γ 3)) x
    g.tangentNorm x (K P A B C x) ≤
      Real.sqrt (∑ γ, g.inner x (kb γ) (kb γ)) *
        g.tangentNorm x (P x) * g.tangentNorm x (A x) *
        g.tangentNorm x (B x) * g.tangentNorm x (C x) := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let V := EuclideanSpace ℝ (Fin n)
  let N := fun (V W : (y : M) → TangentSpace (𝓡 n) y) y =>
    D.connection W y (V y)
  let R := fun (V W Z : (y : M) → TangentSpace (𝓡 n) y) y =>
    D.curvatureOnFields V W Z y
  let K := fun (V W Z L : (y : M) → TangentSpace (𝓡 n) y) y =>
    N V (R W Z L) y - R (N V W) Z L y -
      R W (N V Z) L y - R W Z (N V L) y
  let b := g.orthonormalBasis x
  let ι := Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))
  let ext := fun i : ι => FiberBundle.extend V (b i)
  let kb := fun (γ : Fin 4 → ι) =>
    K (ext (γ 0)) (ext (γ 1)) (ext (γ 2)) (ext (γ 3)) x
  let q := ∑ γ : Fin 4 → ι, g.inner x (kb γ) (kb γ)
  have hpair (z : TangentSpace (𝓡 n) x) : g.inner x z z = ‖z‖ ^ 2 :=
    real_inner_self_eq_norm_sq z
  have hnorm (z : TangentSpace (𝓡 n) x) : g.tangentNorm x z = ‖z‖ := by
    rw [RiemannianMetric.tangentNorm, hpair, Real.sqrt_sq (norm_nonneg _)]
  change g.tangentNorm x (K P A B C x) ≤ Real.sqrt q *
    g.tangentNorm x (P x) * g.tangentNorm x (A x) *
      g.tangentNorm x (B x) * g.tangentNorm x (C x)
  simp only [hnorm]
  obtain ⟨T, hT⟩ := exists_curvatureOnFields_derivative_quadrilinearMap D x
  let L : MultilinearMap ℝ (fun _ : Fin 4 => TangentSpace (𝓡 n) x)
      (TangentSpace (𝓡 n) x) :=
    MultilinearMap.mk' (fun z => T (z 0) (z 1) (z 2) (z 3))
      (by
        intro z i v w
        fin_cases i <;> simp [map_add, LinearMap.add_apply])
      (by
        intro z i c v
        fin_cases i <;> simp [map_smul, LinearMap.smul_apply])
  let v : Fin 4 → TangentSpace (𝓡 n) x := ![P x, A x, B x, C x]
  have hLv : L v = K P A B C x := hT hU P A B C hP hA hB hC hx
  let e := trivializationAt V (TangentSpace (𝓡 n)) x
  have hxe : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  have hExt (i : ι) : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% (ext i)) e.baseSet := by
    have hc : ContMDiffOn (𝓡 n) 𝓘(ℝ, V) ∞
        (fun _y : M => (e ⟨x, b i⟩).2) e.baseSet := contMDiffOn_const
    have hec : ContMDiffOn (𝓡 n) 𝓘(ℝ, V) ∞
        (fun y => (e ⟨y, ext i y⟩).2) e.baseSet := by
      apply hc.congr
      intro y hy
      change (e ⟨y, e.symm y (e ⟨x, b i⟩).2⟩).2 = (e ⟨x, b i⟩).2
      simpa only using congrArg Prod.snd (e.apply_mk_symm hy (e ⟨x, b i⟩).2)
    intro y hy
    rw [e.contMDiffWithinAt_section _ hy]
    exact hec y hy
  let tb := fun γ : Fin 4 → ι => L (fun r => b (γ r))
  have htb (γ : Fin 4 → ι) : tb γ = kb γ := by
    have hh := hT e.open_baseSet (ext (γ 0)) (ext (γ 1)) (ext (γ 2)) (ext (γ 3))
      (hExt (γ 0)) (hExt (γ 1)) (hExt (γ 2)) (hExt (γ 3)) hxe
    change T (ext (γ 0) x) (ext (γ 1) x) (ext (γ 2) x) (ext (γ 3) x) = kb γ at hh
    change T (b (γ 0)) (b (γ 1)) (b (γ 2)) (b (γ 3)) = kb γ
    simpa only [ext, FiberBundle.extend_apply_self] using hh
  let c := fun γ : Fin 4 → ι => ∏ r, b.repr (v r) (γ r)
  have hExpand : L v = ∑ γ : Fin 4 → ι, c γ • tb γ := by
    calc
      _ = L (fun r => ∑ i : ι, b.repr (v r) i • b i) :=
        congrArg L (funext fun r => (b.sum_repr (v r)).symm)
      _ = ∑ γ : Fin 4 → ι, L (fun r => b.repr (v r) (γ r) • b (γ r)) :=
        L.map_sum (fun r i => b.repr (v r) i • b i)
      _ = _ := by simp only [MultilinearMap.map_smul_univ, c, tb]
  let H := ‖P x‖ * ‖A x‖ * ‖B x‖ * ‖C x‖
  have hH : (∏ r : Fin 4, ‖v r‖) = H := by
    rw [Fin.prod_univ_four]
    rfl
  have hrepr (z : TangentSpace (𝓡 n) x) :
      ∑ i : ι, b.repr z i ^ 2 = ‖z‖ ^ 2 := by
    simpa only [OrthonormalBasis.repr_apply_apply] using b.sum_sq_inner_right z
  have hweight : (∑ γ : Fin 4 → ι, |c γ| ^ 2) = H ^ 2 := by
    calc
      _ = ∑ γ : Fin 4 → ι, ∏ r, b.repr (v r) (γ r) ^ 2 := by
        simp only [c, sq_abs, Finset.prod_pow]
      _ = ∏ r : Fin 4, ∑ i : ι, b.repr (v r) i ^ 2 :=
        (Fintype.prod_sum (fun r i => b.repr (v r) i ^ 2)).symm
      _ = ∏ r : Fin 4, ‖v r‖ ^ 2 := by simp only [hrepr]
      _ = H ^ 2 := by rw [Finset.prod_pow, hH]
  have hq : q = ∑ γ : Fin 4 → ι, ‖tb γ‖ ^ 2 := by
    simp only [q, htb, hpair]
  have hq0 : 0 ≤ q := by rw [hq]; positivity
  let S := ∑ γ : Fin 4 → ι, |c γ| * ‖tb γ‖
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin 4 → ι))
    (fun γ => |c γ|) (fun γ => ‖tb γ‖)
  change S ^ 2 ≤ _ at hcs
  rw [hweight, ← hq] at hcs
  have hbound : S ≤ Real.sqrt q * H := by
    have hS0 : 0 ≤ S := by dsimp only [S]; positivity
    have hright : 0 ≤ Real.sqrt q * H := by dsimp only [H]; positivity
    have hsquare : S ^ 2 ≤ (Real.sqrt q * H) ^ 2 := by
      calc
        _ ≤ H ^ 2 * q := hcs
        _ = _ := by rw [mul_pow (Real.sqrt q) H 2, Real.sq_sqrt hq0]; ring
    exact (sq_le_sq₀ hS0 hright).mp hsquare
  have hnormL : ‖L v‖ ≤ Real.sqrt q * H := by
    calc
      _ = ‖∑ γ : Fin 4 → ι, c γ • tb γ‖ := congrArg norm hExpand
      _ ≤ ∑ γ : Fin 4 → ι, ‖c γ • tb γ‖ := norm_sum_le _ _
      _ = S := by simp only [S, norm_smul, Real.norm_eq_abs]
      _ ≤ _ := hbound
  calc
    ‖K P A B C x‖ = ‖L v‖ := congrArg norm hLv.symm
    _ ≤ Real.sqrt q * H := hnormL
    _ = _ := by dsimp only [H]; ring

set_option synthInstance.maxHeartbeats 200000 in

theorem abs_curvature_derivative_pairing_le_orthonormal_energy
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    {U : Set M} (hU : IsOpen U)
    (P A B C : (y : M) → TangentSpace (𝓡 n) y)
    (hP : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% P) U)
    (hA : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% A) U)
    (hB : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% B) U)
    (hC : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% C) U)
    {x : M} (hx : x ∈ U) (w : TangentSpace (𝓡 n) x) :
    let N := fun (V W : (y : M) → TangentSpace (𝓡 n) y) y =>
      D.connection W y (V y)
    let R := fun (V W Z : (y : M) → TangentSpace (𝓡 n) y) y =>
      D.curvatureOnFields V W Z y
    let K := fun (V W Z L : (y : M) → TangentSpace (𝓡 n) y) y =>
      N V (R W Z L) y - R (N V W) Z L y -
        R W (N V Z) L y - R W Z (N V L) y
    let b := g.orthonormalBasis x
    let ext := fun i => FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (b i)
    let kb := fun (γ : Fin 4 → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) =>
      K (ext (γ 0)) (ext (γ 1)) (ext (γ 2)) (ext (γ 3)) x
    |g.inner x (K P A B C x) w| ≤
      Real.sqrt (∑ γ, g.inner x (kb γ) (kb γ)) *
        g.tangentNorm x (P x) * g.tangentNorm x (A x) *
        g.tangentNorm x (B x) * g.tangentNorm x (C x) * g.tangentNorm x w := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hnorm (z : TangentSpace (𝓡 n) x) : g.tangentNorm x z = ‖z‖ := by
    rw [RiemannianMetric.tangentNorm, show g.inner x z z = ‖z‖ ^ 2 from
      real_inner_self_eq_norm_sq z, Real.sqrt_sq (norm_nonneg _)]
  have hpair (z : TangentSpace (𝓡 n) x) :
      |g.inner x z w| ≤ g.tangentNorm x z * g.tangentNorm x w := by
    rw [hnorm, hnorm]
    exact abs_real_inner_le_norm z w
  have hvec := curvature_derivative_tangentNorm_le_orthonormal_energy
    D hU P A B C hP hA hB hC hx
  dsimp only at hvec ⊢
  exact (hpair _).trans
    (mul_le_mul_of_nonneg_right hvec (Real.sqrt_nonneg _))

theorem hasDerivAt_ricciFlow_iteratedCurvature_succ
    {J : Set ℝ} (F : RicciFlow n M J)
    {t : ℝ} (ht : t ∈ interior J) {U : Set M} (hU : IsOpen U) (k : ℕ)
    (P : (y : M) → TangentSpace (𝓡 n) y)
    (X : Fin (k + 3) → (y : M) → TangentSpace (𝓡 n) y)
    (hP : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% P) U)
    (hX : ∀ j, ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% (X j)) U)
    {x : M} (hx : x ∈ U) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric 0).toRiemannianMetric⟩
    let N := fun s (A C : (y : M) → TangentSpace (𝓡 n) y) y =>
      (F.connection s).connection C y (A y)
    let K := fun s => curvatureOnFields_iteratedCovariantDerivative (F.connection s) k
    let dotK := fun Z y => deriv (fun s => K s Z y) t
    let B := fun A C y => deriv (fun s => N s A C y) t
    HasDerivAt
      (fun s => curvatureOnFields_iteratedCovariantDerivative (F.connection s) (k + 1)
        (Fin.cons P X) x)
      (N t P (dotK X) x - (∑ j, dotK (Function.update X j (N t P (X j))) x) +
        B P (K t X) x - ∑ j, K t (Function.update X j (B P (X j))) x) t := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric 0).toRiemannianMetric⟩
  let N := fun s (A C : (y : M) → TangentSpace (𝓡 n) y) y =>
    (F.connection s).connection C y (A y)
  let K := fun s => curvatureOnFields_iteratedCovariantDerivative (F.connection s) k
  let dotK := fun Z y => deriv (fun s => K s Z y) t
  let B := fun A C y => deriv (fun s => N s A C y) t
  let S := fun A : (y : M) → TangentSpace (𝓡 n) y =>
    ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% A) U
  let SF := fun A : ℝ → (y : M) → TangentSpace (𝓡 n) y =>
    ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n))
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun p : ℝ × M => TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2
        (A p.1 p.2)) (J ×ˢ U)
  have hfixed (A : (y : M) → TangentSpace (𝓡 n) y) (hA : S A) :
      SF (fun _ => A) := hA.comp contMDiffOn_snd (fun _ hp => hp.2)
  have hNK (j : Fin (k + 3)) : SF (fun s => N s P (X j)) :=
    contMDiffOn_connection_family_apply F.smooth F.connection hU (X j) P (hX j) hP
  have hB (j : Fin (k + 3)) : S (B P (X j)) :=
    (family_tangent_time_derivative (F.metric 0) hU
      (fun s => N s P (X j)) (hNK j) ht).2
  have hK : SF (fun s => K s X) :=
    contMDiffOn_family_curvatureOnFields_iteratedCovariantDerivative
      F.smooth F.connection hU k (fun j _ => X j) (fun j => hfixed _ (hX j))
  have houter := hasDerivAt_ricciFlow_connection_moving_field F ht hU P
    (fun s => K s X) hP hK hx
  change HasDerivAt (fun s => N s P (K s X) x)
    (B P (K t X) x + N t P (dotK X) x) t at houter
  have hup (Z : Fin (k + 3) → (y : M) → TangentSpace (𝓡 n) y)
      (hZ : ∀ j, S (Z j)) (i : Fin (k + 3))
      (A : (y : M) → TangentSpace (𝓡 n) y) (hA : S A) :
      ∀ j, S (Function.update Z i A j) := by
    intro j
    by_cases hji : j = i
    · subst j
      simpa only [Function.update_self] using hA
    · simpa only [Function.update_of_ne hji] using hZ j
  obtain ⟨L, hL⟩ :=
    exists_curvatureOnFields_iteratedCovariantDerivative_multilinearMap (F.connection t) k x
  have hzero (Z : Fin (k + 3) → (y : M) → TangentSpace (𝓡 n) y)
      (hZ : ∀ j, S (Z j)) (i : Fin (k + 3)) :
      K t (Function.update Z i (fun y => 0)) x = 0 := by
    change curvatureOnFields_iteratedCovariantDerivative (F.connection t) k
      (Function.update Z i (fun y => 0)) x = 0
    rw [← hL hU _ (hup Z hZ i _
      (contMDiffOn_zeroSection ℝ (TangentSpace (𝓡 n)))) hx]
    apply L.map_coord_zero i
    simp only [Function.update_self]
  have hslot (j : Fin (k + 3)) :
      HasDerivAt (fun s => K s (Function.update X j (N s P (X j))) x)
        (dotK (Function.update X j (N t P (X j))) x +
          K t (Function.update X j (B P (X j))) x) t := by
    let Y := fun (i : Fin (k + 3)) s => Function.update X j (N s P (X j)) i
    have hY : ∀ i, SF (Y i) := by
      intro i
      by_cases hij : i = j
      · subst i
        simpa only [Y, Function.update_self] using hNK j
      · simpa only [Y, Function.update_of_ne hij] using hfixed _ (hX i)
    have hYt : ∀ i, S (Y i t) :=
      hup X hX j _ ((F.connection t).contMDiffOn_connection_apply hU P (X j) hP (hX j))
    have hd := hasDerivAt_ricciFlow_iteratedCurvature_moving_inputs
      F ht hU k Y hY hx
    have hdot (i : Fin (k + 3)) :
        (fun y => deriv (fun s => Y i s y) t) =
          Function.update (fun _ : Fin (k + 3) => fun y : M => (0 : TangentSpace (𝓡 n) y))
            j (B P (X j)) i := by
      funext y
      by_cases hij : i = j
      · subst i
        simp only [Y, Function.update_self]
        rfl
      · simp only [Y, Function.update_of_ne hij, deriv_const]
    apply hd.congr_deriv
    change dotK (Function.update X j (N t P (X j))) x +
      (∑ i, K t (Function.update (fun l => Y l t) i
        (fun y => deriv (fun s => Y i s y) t)) x) = _
    congr 1
    rw [Finset.sum_eq_single j]
    · rw [hdot, Function.update_self]
      change K t (Function.update (Function.update X j (N t P (X j))) j (B P (X j))) x = _
      rw [Function.update_idem]
    · intro i _ hij
      rw [hdot, Function.update_of_ne hij]
      exact hzero _ hYt i
    · simp
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => hslot j)
  have hd := houter.sub hsum
  apply (hd.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun s => by
    simp only [curvatureOnFields_iteratedCovariantDerivative, Fin.tail_cons, Fin.cons_zero,
      Fin.cons_succ]
    rfl))).congr_deriv
  simp only [Finset.sum_add_distrib]
  change (B P (K t X) x + N t P (dotK X) x) -
    ((∑ j, dotK (Function.update X j (N t P (X j))) x) +
      ∑ j, K t (Function.update X j (B P (X j))) x) = _
  abel

end PoincareConjecture.Proofs.M03
