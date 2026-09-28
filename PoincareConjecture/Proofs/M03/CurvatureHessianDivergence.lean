import PoincareConjecture.Proofs.M03.CurvatureDiffusionReaction
import PoincareConjecture.Proofs.M03.CurvatureDerivativeTensoriality
import PoincareConjecture.Proofs.M03.CurvatureDerivativeCommutator
import PoincareConjecture.Proofs.M03.CurvatureRateAlgebra
import PoincareConjecture.Proofs.M03.MetricInverse
import PoincareConjecture.Proofs.M03.FiniteCompactFourFamilyCoefficient
import PoincareConjecture.Proofs.M03.FiniteFourFamilyEnergy
import PoincareConjecture.Proofs.M03.FamilyBundleCoordinates
import PoincareConjecture.Proofs.M03.ConnectionFamily
import PoincareConjecture.Proofs.M03.CurvatureHom

set_option autoImplicit false
set_option maxHeartbeats 1800000

open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle Manifold Set

universe u

namespace PoincareConjecture.Proofs.M03

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

theorem hasDerivAt_curvature_difference
    {J J' : Set ℝ} (F : RicciFlow n M J) (F' : RicciFlow n M J')
    (hinit : F.metric 0 = F'.metric 0)
    {t : ℝ} (ht : t ∈ interior J) (ht' : t ∈ interior J')
    (x : M) (u v w : TangentSpace (𝓡 n) x) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric 0).toRiemannianMetric⟩
    letI : NormedAddCommGroup (TangentSpace (𝓡 n) x) :=
      Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal x
    letI : InnerProductSpace ℝ (TangentSpace (𝓡 n) x) :=
      Bundle.instInnerProductSpaceReal x
    @HasDerivAt ℝ _ (TangentSpace (𝓡 n) x)
      (Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal x).toAddCommGroup
      (Bundle.instInnerProductSpaceReal x).toModule
      PseudoMetricSpace.toUniformSpace.toTopologicalSpace _
      (fun s => (F.connection s).curvature x u v w -
        (F'.connection s).curvature x u v w)
      (deriv (fun s => (F.connection s).curvature x u v w) t -
        deriv (fun s => (F'.connection s).curvature x u v w) t) t := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric 0).toRiemannianMetric⟩
  have hF := hasDerivAt_ricciFlow_curvature_diffusion_reaction F ht x u v w
  have hF'raw :=
    hasDerivAt_ricciFlow_curvature_diffusion_reaction F' ht' x u v w
  have hF' := by
    simpa only [← hinit] using hF'raw
  convert hF.sub hF' using 1
  · ext s
    simp only [Pi.sub_apply]
  · rw [hF.deriv, hF'.deriv]

theorem hasDerivAt_curvature_difference_apply
    {J J' : Set ℝ} (F : RicciFlow n M J) (F' : RicciFlow n M J')
    (hinit : F.metric 0 = F'.metric 0)
    {t : ℝ} (ht : t ∈ interior J) (ht' : t ∈ interior J')
    (x : M) (u v w : TangentSpace (𝓡 n) x)
    (l : TangentSpace (𝓡 n) x →L[ℝ] ℝ) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric 0).toRiemannianMetric⟩
    letI : NormedAddCommGroup (TangentSpace (𝓡 n) x) :=
      Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal x
    letI : InnerProductSpace ℝ (TangentSpace (𝓡 n) x) :=
      Bundle.instInnerProductSpaceReal x
    HasDerivAt
      (fun s => l ((F.connection s).curvature x u v w -
        (F'.connection s).curvature x u v w))
      (l (deriv (fun s => (F.connection s).curvature x u v w) t -
        deriv (fun s => (F'.connection s).curvature x u v w) t)) t := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric 0).toRiemannianMetric⟩
  have hl : HasFDerivAt (fun y => l y) l
      ((F.connection t).curvature x u v w - (F'.connection t).curvature x u v w) :=
    l.hasFDerivAt
  simpa only [Function.comp_def] using
    HasFDerivAt.comp_hasDerivAt t hl
      (hasDerivAt_curvature_difference F F' hinit ht ht' x u v w)

theorem curvature_hessian_trace_localFrame
    {g : RiemannianMetric n M} (D : LeviCivitaData g) (x0 : M) :
    let V := EuclideanSpace ℝ (Fin n)
    let e := trivializationAt V (TangentSpace (𝓡 n)) x0
    let b0 := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    let E := e.localFrame b0
    let G := fun y : M =>
      ContinuousLinearMap.inCoordinates V (TangentSpace (𝓡 n))
        (V →L[ℝ] ℝ) (fun z => TangentSpace (𝓡 n) z →L[ℝ] ℝ)
        x0 y x0 y (g.inner y)
    let a := fun (y : M) (i j : Fin n) =>
      (ContinuousLinearMap.inverse (G y) (EuclideanSpace.proj j)) i
    let N := fun (P Q : (y : M) → TangentSpace (𝓡 n) y) (y : M) =>
      D.connection Q y (P y)
    let R := fun (A B C : (y : M) → TangentSpace (𝓡 n) y) (y : M) =>
      D.curvatureOnFields A B C y
    let K := fun (P A B C : (y : M) → TangentSpace (𝓡 n) y) (y : M) =>
      N P (R A B C) y - R (N P A) B C y -
        R A (N P B) C y - R A B (N P C) y
    let H := fun (P Q A B C : (y : M) → TangentSpace (𝓡 n) y) (y : M) =>
      N P (K Q A B C) y - K (N P Q) A B C y -
        K Q (N P A) B C y - K Q A (N P B) C y - K Q A B (N P C) y
    ∀ {x : M}, x ∈ e.baseSet →
      ∀ A B C : (y : M) → TangentSpace (𝓡 n) y,
      ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% A) e.baseSet →
      ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% B) e.baseSet →
      ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% C) e.baseSet →
      let b := g.orthonormalBasis x
      let ext := fun v : TangentSpace (𝓡 n) x => FiberBundle.extend V v
      (∑ r, H (ext (b r)) (ext (b r)) (ext (A x)) (ext (B x)) (ext (C x)) x) =
        ∑ i, ∑ j, a x i j • H (E i) (E j) A B C x := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsManifold (𝓡 n) (∞ + 1) M := by
    simpa using (inferInstance : IsManifold (𝓡 n) ∞ M)
  letI : IsManifold (𝓡 n) (minSmoothness ℝ 2) M :=
    IsManifold.of_le (n := ∞) (by
      simpa only [minSmoothness_of_isRCLikeNormedField] using
        (ENat.LEInfty.out (m := (2 : ℕ∞ω))))
  dsimp only
  let V := EuclideanSpace ℝ (Fin n)
  let e := trivializationAt V (TangentSpace (𝓡 n)) x0
  let b0 := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let E := e.localFrame b0
  let theta := e.localFrameCoeff (𝓡 n) b0
  let G := fun y : M =>
    ContinuousLinearMap.inCoordinates V (TangentSpace (𝓡 n))
      (V →L[ℝ] ℝ) (fun z => TangentSpace (𝓡 n) z →L[ℝ] ℝ)
      x0 y x0 y (g.inner y)
  let a := fun (y : M) (i j : Fin n) =>
    (ContinuousLinearMap.inverse (G y) (EuclideanSpace.proj j)) i
  let N := fun (P Q : (y : M) → TangentSpace (𝓡 n) y) (y : M) =>
    D.connection Q y (P y)
  let R := fun (A B C : (y : M) → TangentSpace (𝓡 n) y) (y : M) =>
    D.curvatureOnFields A B C y
  let K := fun (P A B C : (y : M) → TangentSpace (𝓡 n) y) (y : M) =>
    N P (R A B C) y - R (N P A) B C y -
      R A (N P B) C y - R A B (N P C) y
  let H := fun (P Q A B C : (y : M) → TangentSpace (𝓡 n) y) (y : M) =>
    N P (K Q A B C) y - K (N P Q) A B C y -
      K Q (N P A) B C y - K Q A (N P B) C y - K Q A B (N P C) y
  intro x hx A B C hA hB hC
  let b := g.orthonormalBasis x
  let ext := fun v : TangentSpace (𝓡 n) x => FiberBundle.extend V v
  change (∑ r, H (ext (b r)) (ext (b r)) (ext (A x)) (ext (B x)) (ext (C x)) x) =
    ∑ i, ∑ j, a x i j • H (E i) (E j) A B C x
  let ex := trivializationAt V (TangentSpace (𝓡 n)) x
  let U := e.baseSet ∩ ex.baseSet
  have hU : IsOpen U := e.open_baseSet.inter ex.open_baseSet
  have hxU : x ∈ U := ⟨hx, FiberBundle.mem_baseSet_trivializationAt' x⟩
  let S := fun W : (y : M) → TangentSpace (𝓡 n) y =>
    ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% W) U
  have hAS : S A := hA.mono inter_subset_left
  have hBS : S B := hB.mono inter_subset_left
  have hCS : S C := hC.mono inter_subset_left
  have hE (i : Fin n) : S (E i) :=
    (e.contMDiffOn_localFrame_baseSet (I := 𝓡 n) ∞ b0 i).mono inter_subset_left
  have hExt (v : TangentSpace (𝓡 n) x) : S (ext v) := by
    have hext : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) ∞
        (T% (ext v)) ex.baseSet := by
      rw [ex.contMDiffOn_section_baseSet_iff (IB := 𝓡 n) (n := ∞)]
      apply (contMDiffOn_const (c := (ex ⟨x, v⟩).2)).congr
      intro y hy
      change (ex ⟨y, ex.symm y (ex ⟨x, v⟩).2⟩).2 = (ex ⟨x, v⟩).2
      simpa only using congrArg Prod.snd (ex.apply_mk_symm hy (ex ⟨x, v⟩).2)
    exact hext.mono inter_subset_right
  have hExtValue (v : TangentSpace (𝓡 n) x) : ext v x = v :=
    FiberBundle.extend_apply_self _ _
  have hmd (W : (y : M) → TangentSpace (𝓡 n) y) (hW : S W)
      {y : M} (hy : y ∈ U) :
      MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) (T% W) y :=
    (hW.contMDiffAt (hU.mem_nhds hy)).mdifferentiableAt (by simp)
  have hN (P Q : (y : M) → TangentSpace (𝓡 n) y)
      (hP : S P) (hQ : S Q) : S (N P Q) :=
    D.contMDiffOn_connection_apply hU P Q hP hQ
  have hR (P Q W : (y : M) → TangentSpace (𝓡 n) y)
      (hP : S P) (hQ : S Q) (hW : S W) : S (R P Q W) := by
    have hbr : S (VectorField.mlieBracket (𝓡 n) P Q) := by
      intro y hy
      exact ((hP.contMDiffAt (hU.mem_nhds hy)).mlieBracket_vectorField
        (hQ.contMDiffAt (hU.mem_nhds hy)) (m := ⊤) (n := ⊤)
        (by simp)).contMDiffWithinAt
    exact ((hN P _ hP (hN Q W hQ hW)).sub_section
      (hN Q _ hQ (hN P W hP hW))).sub_section (hN _ W hbr hW)
  have hK (P Q W Z : (y : M) → TangentSpace (𝓡 n) y)
      (hP : S P) (hQ : S Q) (hW : S W) (hZ : S Z) : S (K P Q W Z) :=
    (((hN P _ hP (hR Q W Z hQ hW hZ)).sub_section
      (hR _ W Z (hN P Q hP hQ) hW hZ)).sub_section
      (hR Q _ Z hQ (hN P W hP hW) hZ)).sub_section
      (hR Q W _ hQ hW (hN P Z hP hZ))
  choose T hT using fun y : M => exists_curvatureOnFields_derivative_quadrilinearMap D y
  have heval (P Q W Z : (y : M) → TangentSpace (𝓡 n) y)
      (hP : S P) (hQ : S Q) (hW : S W) (hZ : S Z)
      {y : M} (hy : y ∈ U) :
      K P Q W Z y = T y (P y) (Q y) (W y) (Z y) :=
    (hT y hU P Q W Z hP hQ hW hZ hy).symm
  let q := fun (i : Fin n) (W : (y : M) → TangentSpace (𝓡 n) y) y =>
    theta i y (W y)
  have hqmd (i : Fin n) (W : (y : M) → TangentSpace (𝓡 n) y) (hW : S W) :
      MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) (q i W) x :=
    ((contMDiffOn_localFrameCoeff b0 hU inter_subset_left hW i).contMDiffAt
      (hU.mem_nhds hxU)).mdifferentiableAt (by simp)
  have hrec (W : (y : M) → TangentSpace (𝓡 n) y)
      {y : M} (hy : y ∈ U) : W y = ∑ i, q i W y • E i y :=
    e.eq_sum_localFrameCoeff_smul (I := 𝓡 n) (b := b0) hy.1
  have hlin (L : TangentSpace (𝓡 n) x →ₗ[ℝ] TangentSpace (𝓡 n) x)
      (W : (y : M) → TangentSpace (𝓡 n) y) :
      L (W x) = ∑ i, q i W x • L (E i x) := by
    rw [hrec W hxU, map_sum]
    simp only [map_smul]
  have hc := D.connection.isCovariantDerivativeOn (s := univ)
  have hnsum (W : Fin n → (y : M) → TangentSpace (𝓡 n) y)
      (hW : ∀ i, MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) (T% (W i)) x)
      (v : TangentSpace (𝓡 n) x) :
      D.connection (fun y => ∑ i, W i y) x v = ∑ i, D.connection (W i) x v := by
    have aux (s : Finset (Fin n)) :
        D.connection (fun y => ∑ i ∈ s, W i y) x v = ∑ i ∈ s, D.connection (W i) x v := by
      induction s using Finset.induction_on with
      | empty =>
        simp only [Finset.sum_empty]
        change D.connection 0 x v = 0
        rw [hc.zero, zero_apply]
      | @insert i s hi ih =>
        simp only [Finset.sum_insert hi]
        change D.connection (W i + fun y => ∑ j ∈ s, W j y) x v = _
        rw [hc.add (hW i) (MDifferentiableAt.sum_section fun j _ => hW j), add_apply, ih]
    exact aux Finset.univ
  have hframe (P Q : (y : M) → TangentSpace (𝓡 n) y)
      (Z : Fin n → (y : M) → TangentSpace (𝓡 n) y) (f : Fin n → M → ℝ)
      (hQ : S Q) (hZ : ∀ i, S (Z i))
      (hf : ∀ i, MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) (f i) x)
      (heq : ∀ y ∈ U, Q y = ∑ i, f i y • Z i y) :
      N P Q x = ∑ i, (f i x • N P (Z i) x +
        mvfderiv (𝓡 n) (f i) x (P x) • Z i x) := by
    have hs (i : Fin n) : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V))
        (T% ((f i) • Z i)) x := (hf i).smul_section (hmd _ (hZ i) hxU)
    have hloc := hc.congr_of_eventuallyEq (hmd Q hQ hxU)
      (MDifferentiableAt.sum_section fun i _ => hs i) Filter.univ_mem
      (Filter.eventuallyEq_of_mem (hU.mem_nhds hxU) heq)
    calc
      _ = D.connection (fun y => ∑ i, f i y • Z i y) x (P x) :=
        congrArg (fun L => L (P x)) hloc
      _ = ∑ i, D.connection ((f i) • Z i) x (P x) :=
        hnsum (fun i => (f i) • Z i) hs (P x)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        simpa only [N, add_apply, smul_apply, ContinuousLinearMap.smulRight_apply] using
          congrArg (fun L => L (P x)) (hc.leibniz (hmd _ (hZ i) hxU) (hf i))

  have hdiff
      (F : ((y : M) → TangentSpace (𝓡 n) y) → (y : M) → TangentSpace (𝓡 n) y)
      (L : (y : M) → TangentSpace (𝓡 n) y →ₗ[ℝ] TangentSpace (𝓡 n) y)
      (hF : ∀ Q, S Q → S (F Q))
      (hFL : ∀ Q, S Q → ∀ y ∈ U, F Q y = L y (Q y))
      (P Q : (y : M) → TangentSpace (𝓡 n) y) (hQ : S Q) :
      N P (F Q) x - L x (N P Q x) =
        ∑ i, q i Q x • (N P (F (E i)) x - L x (N P (E i) x)) := by
    have hFeq (y : M) (hy : y ∈ U) : F Q y = ∑ i, q i Q y • F (E i) y := by
      rw [hFL Q hQ y hy, hrec Q hy, map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_smul, hFL (E i) (hE i) y hy]
    rw [hframe P (F Q) (fun i => F (E i)) (fun i => q i Q)
      (hF Q hQ) (fun i => hF (E i) (hE i)) (fun i => hqmd i Q hQ) hFeq,
      hframe P Q E (fun i => q i Q) hQ hE (fun i => hqmd i Q hQ)
        (fun y hy => hrec Q hy), map_sum]
    simp only [map_add, map_smul]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [hFL (E i) (hE i) x hxU, smul_sub]
    module
  have hHP (P Q A B C : (y : M) → TangentSpace (𝓡 n) y)
      (hP : S P) (hQ : S Q) (hA : S A) (hB : S B) (hC : S C) :
      H P Q A B C x = ∑ i, q i P x • H (E i) Q A B C x := by
    let L : TangentSpace (𝓡 n) x →ₗ[ℝ] TangentSpace (𝓡 n) x :=
      (D.connection (K Q A B C) x).toLinearMap -
        ((((T x).flip (A x)).flip (B x)).flip (C x)).comp (D.connection Q x).toLinearMap -
        (((T x (Q x)).flip (B x)).flip (C x)).comp (D.connection A x).toLinearMap -
        ((T x (Q x) (A x)).flip (C x)).comp (D.connection B x).toLinearMap -
        (T x (Q x) (A x) (B x)).comp (D.connection C x).toLinearMap
    have hform (W : (y : M) → TangentSpace (𝓡 n) y) (hW : S W) :
        H W Q A B C x = L (W x) := by
      dsimp only [H]
      rw [heval (N W Q) A B C (hN W Q hW hQ) hA hB hC hxU,
        heval Q (N W A) B C hQ (hN W A hW hA) hB hC hxU,
        heval Q A (N W B) C hQ hA (hN W B hW hB) hC hxU,
        heval Q A B (N W C) hQ hA hB (hN W C hW hC) hxU]
      rfl
    rw [hform P hP, hlin L P]
    apply Finset.sum_congr rfl
    intro i _
    rw [hform (E i) (hE i)]
  have hHQ (P Q A B C : (y : M) → TangentSpace (𝓡 n) y)
      (hP : S P) (hQ : S Q) (hA : S A) (hB : S B) (hC : S C) :
      H P Q A B C x = ∑ i, q i Q x • H P (E i) A B C x := by
    let L := fun y => (((T y).flip (A y)).flip (B y)).flip (C y)
    let La := (((T x).flip (N P A x)).flip (B x)).flip (C x)
    let Lb := (((T x).flip (A x)).flip (N P B x)).flip (C x)
    let Lc := (((T x).flip (A x)).flip (B x)).flip (N P C x)
    have hform (W : (y : M) → TangentSpace (𝓡 n) y) (hW : S W) :
        H P W A B C x = (N P (K W A B C) x - L x (N P W x)) -
          La (W x) - Lb (W x) - Lc (W x) := by
      dsimp only [H]
      rw [heval (N P W) A B C (hN P W hP hW) hA hB hC hxU,
        heval W (N P A) B C hW (hN P A hP hA) hB hC hxU,
        heval W A (N P B) C hW hA (hN P B hP hB) hC hxU,
        heval W A B (N P C) hW hA hB (hN P C hP hC) hxU]
      rfl
    rw [hform Q hQ, hdiff (fun W => K W A B C) L
      (fun W hW => hK W A B C hW hA hB hC)
      (fun W hW y hy => heval W A B C hW hA hB hC hy) P Q hQ,
      hlin La Q, hlin Lb Q, hlin Lc Q,
      ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [hform (E i) (hE i)]
    simp only [smul_sub]
  have hHA (P Q A B C : (y : M) → TangentSpace (𝓡 n) y)
      (hP : S P) (hQ : S Q) (hA : S A) (hB : S B) (hC : S C) :
      H P Q A B C x = ∑ i, q i A x • H P Q (E i) B C x := by
    let L := fun y => ((T y (Q y)).flip (B y)).flip (C y)
    let Lq := ((T x (N P Q x)).flip (B x)).flip (C x)
    let Lb := ((T x (Q x)).flip (N P B x)).flip (C x)
    let Lc := ((T x (Q x)).flip (B x)).flip (N P C x)
    have hform (W : (y : M) → TangentSpace (𝓡 n) y) (hW : S W) :
        H P Q W B C x = (N P (K Q W B C) x - L x (N P W x)) -
          Lq (W x) - Lb (W x) - Lc (W x) := by
      dsimp only [H]
      rw [heval (N P Q) W B C (hN P Q hP hQ) hW hB hC hxU,
        heval Q (N P W) B C hQ (hN P W hP hW) hB hC hxU,
        heval Q W (N P B) C hQ hW (hN P B hP hB) hC hxU,
        heval Q W B (N P C) hQ hW hB (hN P C hP hC) hxU]
      dsimp only [L, Lq, Lb, Lc, LinearMap.flip_apply]
      module
    rw [hform A hA, hdiff (fun W => K Q W B C) L
      (fun W hW => hK Q W B C hQ hW hB hC)
      (fun W hW y hy => heval Q W B C hQ hW hB hC hy) P A hA,
      hlin Lq A, hlin Lb A, hlin Lc A,
      ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [hform (E i) (hE i)]
    simp only [smul_sub]
  have hHB (P Q A B C : (y : M) → TangentSpace (𝓡 n) y)
      (hP : S P) (hQ : S Q) (hA : S A) (hB : S B) (hC : S C) :
      H P Q A B C x = ∑ i, q i B x • H P Q A (E i) C x := by
    let L := fun y => (T y (Q y) (A y)).flip (C y)
    let Lq := (T x (N P Q x) (A x)).flip (C x)
    let La := (T x (Q x) (N P A x)).flip (C x)
    let Lc := (T x (Q x) (A x)).flip (N P C x)
    have hform (W : (y : M) → TangentSpace (𝓡 n) y) (hW : S W) :
        H P Q A W C x = (N P (K Q A W C) x - L x (N P W x)) -
          Lq (W x) - La (W x) - Lc (W x) := by
      dsimp only [H]
      rw [heval (N P Q) A W C (hN P Q hP hQ) hA hW hC hxU,
        heval Q (N P A) W C hQ (hN P A hP hA) hW hC hxU,
        heval Q A (N P W) C hQ hA (hN P W hP hW) hC hxU,
        heval Q A W (N P C) hQ hA hW (hN P C hP hC) hxU]
      dsimp only [L, Lq, La, Lc, LinearMap.flip_apply]
      module
    rw [hform B hB, hdiff (fun W => K Q A W C) L
      (fun W hW => hK Q A W C hQ hA hW hC)
      (fun W hW y hy => heval Q A W C hQ hA hW hC hy) P B hB,
      hlin Lq B, hlin La B, hlin Lc B,
      ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [hform (E i) (hE i)]
    simp only [smul_sub]
  have hHC (P Q A B C : (y : M) → TangentSpace (𝓡 n) y)
      (hP : S P) (hQ : S Q) (hA : S A) (hB : S B) (hC : S C) :
      H P Q A B C x = ∑ i, q i C x • H P Q A B (E i) x := by
    let L := fun y => T y (Q y) (A y) (B y)
    let Lq := T x (N P Q x) (A x) (B x)
    let La := T x (Q x) (N P A x) (B x)
    let Lb := T x (Q x) (A x) (N P B x)
    have hform (W : (y : M) → TangentSpace (𝓡 n) y) (hW : S W) :
        H P Q A B W x = (N P (K Q A B W) x - L x (N P W x)) -
          Lq (W x) - La (W x) - Lb (W x) := by
      dsimp only [H]
      rw [heval (N P Q) A B W (hN P Q hP hQ) hA hB hW hxU,
        heval Q (N P A) B W hQ (hN P A hP hA) hB hW hxU,
        heval Q A (N P B) W hQ hA (hN P B hP hB) hW hxU,
        heval Q A B (N P W) hQ hA hB (hN P W hP hW) hxU]
      dsimp only [L, Lq, La, Lb]
      module
    rw [hform C hC, hdiff (fun W => K Q A B W) L
      (fun W hW => hK Q A B W hQ hA hB hW)
      (fun W hW y hy => heval Q A B W hQ hA hB hW hy) P C hC,
      hlin Lq C, hlin La C, hlin Lb C,
      ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [hform (E i) (hE i)]
    simp only [smul_sub]
  have hinputs (i j : Fin n) :
      H (E i) (E j) (ext (A x)) (ext (B x)) (ext (C x)) x =
        H (E i) (E j) A B C x := by
    rw [hHA _ _ _ _ _ (hE i) (hE j) (hExt _) (hExt _) (hExt _),
      hHA _ _ _ _ _ (hE i) (hE j) hAS hBS hCS]
    apply Finset.sum_congr rfl
    intro k _
    simp only [q, hExtValue]
    congr 1
    rw [hHB _ _ _ _ _ (hE i) (hE j) (hE k) (hExt _) (hExt _),
      hHB _ _ _ _ _ (hE i) (hE j) (hE k) hBS hCS]
    apply Finset.sum_congr rfl
    intro l _
    simp only [q, hExtValue]
    congr 1
    rw [hHC _ _ _ _ _ (hE i) (hE j) (hE k) (hE l) (hExt _),
      hHC _ _ _ _ _ (hE i) (hE j) (hE k) (hE l) hCS]
    simp only [q, hExtValue]
  have hcontract (i j : Fin n) :
      (∑ r, theta i x (b r) * theta j x (b r)) = a x i j := by
    exact (metric_inverse_eq_sum_orthonormal_coordinates g x0 x hx i j).symm
  have htraceTerm (r) :
      H (ext (b r)) (ext (b r)) (ext (A x)) (ext (B x)) (ext (C x)) x =
        ∑ i, ∑ j, (theta i x (b r) * theta j x (b r)) • H (E i) (E j) A B C x := by
    rw [hHP _ _ _ _ _ (hExt _) (hExt _) (hExt _) (hExt _) (hExt _)]
    apply Finset.sum_congr rfl
    intro i _
    rw [hHQ _ _ _ _ _ (hE i) (hExt _) (hExt _) (hExt _) (hExt _), Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [hinputs i j]
    simp only [q, hExtValue, smul_smul]
  simp_rw [htraceTerm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Finset.sum_smul, hcontract]

theorem curvature_hessian_contraction_eq_covariant_divergence
    {g : RiemannianMetric n M} (D : LeviCivitaData g) (x0 : M) :
    let V := EuclideanSpace ℝ (Fin n)
    let c := chartAt V x0
    let e := trivializationAt V (TangentSpace (𝓡 n)) x0
    let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    let E := e.localFrame b
    let theta := e.localFrameCoeff (𝓡 n) b
    let G := fun y : M =>
      ContinuousLinearMap.inCoordinates V (TangentSpace (𝓡 n))
        (V →L[ℝ] ℝ) (fun z => TangentSpace (𝓡 n) z →L[ℝ] ℝ)
        x0 y x0 y (g.inner y)
    let a := fun (y : M) (i j : Fin n) =>
      (ContinuousLinearMap.inverse (G y) (EuclideanSpace.proj j)) i
    let N := fun (P Q : (y : M) → TangentSpace (𝓡 n) y) (y : M) =>
      D.connection Q y (P y)
    let R := fun (A B C : (y : M) → TangentSpace (𝓡 n) y) (y : M) =>
      D.curvatureOnFields A B C y
    let K := fun (P A B C : (y : M) → TangentSpace (𝓡 n) y) (y : M) =>
      N P (R A B C) y - R (N P A) B C y -
        R A (N P B) C y - R A B (N P C) y
    let H := fun (P Q A B C : (y : M) → TangentSpace (𝓡 n) y) (y : M) =>
      N P (K Q A B C) y - K (N P Q) A B C y -
        K Q (N P A) B C y - K Q A (N P B) C y - K Q A B (N P C) y
    let W := fun (i : Fin n) (A B C : (y : M) → TangentSpace (𝓡 n) y) (y : M) =>
      ∑ j, a y i j • K (E j) A B C y
    let Gamma := fun (y : M) (i j l : Fin n) => theta l y (N (E i) (E j) y)
    ∀ z ∈ c.target, ∀ A B C : (y : M) → TangentSpace (𝓡 n) y,
      ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% A) e.baseSet →
      ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% B) e.baseSet →
      ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% C) e.baseSet →
      let x := c.symm z
      (∑ i, ∑ j, a x i j • H (E i) (E j) A B C x) =
        ∑ i, (N (E i) (W i A B C) x - W i (N (E i) A) B C x -
          W i A (N (E i) B) C x - W i A B (N (E i) C) x +
          ∑ p, Gamma x i p i • W p A B C x) := by
  classical
  letI : IsManifold (𝓡 n) (∞ + 1) M := by
    simpa using (inferInstance : IsManifold (𝓡 n) ∞ M)
  letI : IsManifold (𝓡 n) (minSmoothness ℝ 2) M :=
    IsManifold.of_le (n := ∞) (by
      simpa only [minSmoothness_of_isRCLikeNormedField] using
        (ENat.LEInfty.out (m := (2 : ℕ∞ω))))
  dsimp only
  let V := EuclideanSpace ℝ (Fin n)
  let c := chartAt V x0
  let e := trivializationAt V (TangentSpace (𝓡 n)) x0
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let E := e.localFrame b
  let theta := e.localFrameCoeff (𝓡 n) b
  let G := fun y : M =>
    ContinuousLinearMap.inCoordinates V (TangentSpace (𝓡 n))
      (V →L[ℝ] ℝ) (fun z => TangentSpace (𝓡 n) z →L[ℝ] ℝ)
      x0 y x0 y (g.inner y)
  let a := fun (y : M) (i j : Fin n) =>
    (ContinuousLinearMap.inverse (G y) (EuclideanSpace.proj j)) i
  let N := fun (P Q : (y : M) → TangentSpace (𝓡 n) y) (y : M) =>
    D.connection Q y (P y)
  let R := fun (A B C : (y : M) → TangentSpace (𝓡 n) y) (y : M) =>
    D.curvatureOnFields A B C y
  let K := fun (P A B C : (y : M) → TangentSpace (𝓡 n) y) (y : M) =>
    N P (R A B C) y - R (N P A) B C y -
      R A (N P B) C y - R A B (N P C) y
  let H := fun (P Q A B C : (y : M) → TangentSpace (𝓡 n) y) (y : M) =>
    N P (K Q A B C) y - K (N P Q) A B C y -
      K Q (N P A) B C y - K Q A (N P B) C y - K Q A B (N P C) y
  let W := fun (i : Fin n) (A B C : (y : M) → TangentSpace (𝓡 n) y) (y : M) =>
    ∑ j, a y i j • K (E j) A B C y
  let Gamma := fun (y : M) (i j l : Fin n) => theta l y (N (E i) (E j) y)
  let S := fun Y : (y : M) → TangentSpace (𝓡 n) y =>
    ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% Y) e.baseSet
  have hE (i : Fin n) : S (E i) :=
    e.contMDiffOn_localFrame_baseSet (I := 𝓡 n) ∞ b i
  have hN (P Q : (y : M) → TangentSpace (𝓡 n) y)
      (hP : S P) (hQ : S Q) : S (N P Q) :=
    D.contMDiffOn_connection_apply e.open_baseSet P Q hP hQ
  have hR (P Q Y : (y : M) → TangentSpace (𝓡 n) y)
      (hP : S P) (hQ : S Q) (hY : S Y) : S (R P Q Y) := by
    have hbr : S (VectorField.mlieBracket (𝓡 n) P Q) := by
      intro y hy
      exact ((hP.contMDiffAt (e.open_baseSet.mem_nhds hy)).mlieBracket_vectorField
        (hQ.contMDiffAt (e.open_baseSet.mem_nhds hy)) (m := ⊤) (n := ⊤)
        (by simp)).contMDiffWithinAt
    exact ((hN P _ hP (hN Q Y hQ hY)).sub_section
      (hN Q _ hQ (hN P Y hP hY))).sub_section (hN _ Y hbr hY)
  have hK (P Q Y Z : (y : M) → TangentSpace (𝓡 n) y)
      (hP : S P) (hQ : S Q) (hY : S Y) (hZ : S Z) : S (K P Q Y Z) :=
    (((hN P _ hP (hR Q Y Z hQ hY hZ)).sub_section
      (hR _ Y Z (hN P Q hP hQ) hY hZ)).sub_section
      (hR Q _ Z hQ (hN P Y hP hY) hZ)).sub_section
      (hR Q Y _ hQ hY (hN P Z hP hZ))
  have hainv (i j : Fin n) : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun y => a y i j) e.baseSet := by
    have hf : RiemannianMetric.IsSmoothFamilyOn (fun _ : ℝ => g) univ :=
      (g.contMDiff.comp contMDiff_snd).contMDiffOn
    have hi := (contMDiffOn_family_metric_frame_inverse hf x0).2.2
    have hs := hi.comp
      (show ContMDiffOn (𝓡 n) (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
        (fun y : M => ((0 : ℝ), y)) e.baseSet from
        contMDiffOn_const.prodMk contMDiffOn_id)
      (fun y hy => ⟨mem_univ (0 : ℝ), hy⟩)
    exact (contMDiffOn_const (c := EuclideanSpace.proj i)).clm_apply
      (hs.clm_apply (contMDiffOn_const (c := EuclideanSpace.proj j)))
  intro z hz A B C hA hB hC
  let x := c.symm z
  have hx : x ∈ e.baseSet := by
    simpa only [e, TangentBundle.trivializationAt_baseSet] using c.map_target hz
  let da := fun i j => mvfderiv (𝓡 n) (fun y => a y i j) x (E i x)
  have hmd (Y : (y : M) → TangentSpace (𝓡 n) y) (hY : S Y) :
      MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) (T% Y) x :=
    (hY.contMDiffAt (e.open_baseSet.mem_nhds hx)).mdifferentiableAt (by simp)
  have hchart (f : M → ℝ) (hf : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f e.baseSet)
      (i : Fin n) : mvfderiv (𝓡 n) f x (E i x) =
      fderiv ℝ (fun w => f (c.symm w)) z (EuclideanSpace.single i 1) := by
    have hcs : MDifferentiableAt 𝓘(ℝ, V) (𝓡 n) c.symm z :=
      ((contMDiffOn_chart_symm (I := 𝓡 n) (n := ∞) (x := x0)).contMDiffAt
        (c.open_target.mem_nhds hz)).mdifferentiableAt (by simp)
    have he : e.symmL ℝ x = mfderiv 𝓘(ℝ, V) (𝓡 n) c.symm z := by
      have hh := TangentBundle.symmL_trivializationAt (I := 𝓡 n) (x₀ := x0)
        (c.map_target hz)
      simp only [extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
        modelWithCornersSelf_coe_symm, Function.comp_def, id_eq, Set.range_id,
        mfderivWithin_univ] at hh
      change e.symmL ℝ x = mfderiv 𝓘(ℝ, V) (𝓡 n) c.symm (c x) at hh
      rwa [c.right_inv hz] at hh
    have hframe : E i x = e.symmL ℝ x (EuclideanSpace.single i 1) := by
      calc
        E i x = e.basisAt b hx i := e.localFrame_apply_of_mem_baseSet b hx
        _ = e.symm x (EuclideanSpace.single i 1) := by
          simp only [Trivialization.basisAt, Module.Basis.map_apply, b,
            OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
            Trivialization.linearEquivAt_symm_apply]
        _ = e.symmL ℝ x (EuclideanSpace.single i 1) := (e.symmL_apply hx _).symm
    have hfd : fderiv ℝ (fun w => f (c.symm w)) z (EuclideanSpace.single i 1) =
        mvfderiv (𝓡 n) f x (e.symmL ℝ x (EuclideanSpace.single i 1)) := by
      rw [← mfderiv_eq_fderiv]
      change mvfderiv 𝓘(ℝ, V) (f ∘ c.symm) z (EuclideanSpace.single i 1) = _
      have hff : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f (c.symm z) :=
        (hf.contMDiffAt (e.open_baseSet.mem_nhds hx)).mdifferentiableAt (by simp)
      rw [mvfderiv_comp_apply z hff hcs (EuclideanSpace.single i 1), ← he]
      rfl
    exact (congrArg (mvfderiv (𝓡 n) f x) hframe).trans hfd.symm
  have hda (i j : Fin n) : da i j =
      -(∑ p, (Gamma x i p i * a x p j + Gamma x i p j * a x i p)) := by
    rw [show da i j = fderiv ℝ (fun w => a (c.symm w) i j) z
      (EuclideanSpace.single i 1) from hchart _ (hainv i j) i]
    exact metric_inverse_covariant_derivative_coordinates D x0 z hz i i j
  have hc := D.connection.isCovariantDerivativeOn (s := univ)
  have hnsum (Y : Fin n → (y : M) → TangentSpace (𝓡 n) y)
      (hY : ∀ j, MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) (T% (Y j)) x)
      (v : TangentSpace (𝓡 n) x) :
      D.connection (fun y => ∑ j, Y j y) x v = ∑ j, D.connection (Y j) x v := by
    have aux (s : Finset (Fin n)) :
        D.connection (fun y => ∑ j ∈ s, Y j y) x v = ∑ j ∈ s, D.connection (Y j) x v := by
      induction s using Finset.induction_on with
      | empty =>
        simp only [Finset.sum_empty]
        change D.connection 0 x v = 0
        rw [hc.zero, zero_apply]
      | @insert j s hj ih =>
        simp only [Finset.sum_insert hj]
        change D.connection (Y j + fun y => ∑ k ∈ s, Y k y) x v = _
        rw [hc.add (hY j) (MDifferentiableAt.sum_section fun k _ => hY k), add_apply, ih]
    exact aux Finset.univ
  have hNK (i : Fin n) : N (E i) (W i A B C) x =
      ∑ j, (a x i j • N (E i) (K (E j) A B C) x + da i j • K (E j) A B C x) := by
    have has (j : Fin n) : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) (fun y => a y i j) x :=
      ((hainv i j).contMDiffAt (e.open_baseSet.mem_nhds hx)).mdifferentiableAt (by simp)
    have hks (j : Fin n) := hmd _ (hK (E j) A B C (hE j) hA hB hC)
    calc
      _ = ∑ j, D.connection ((fun y => a y i j) • K (E j) A B C) x (E i x) :=
        hnsum (fun j => (fun y => a y i j) • K (E j) A B C)
          (fun j => (has j).smul_section (hks j)) (E i x)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j _
        simpa only [N, da, add_apply, smul_apply, ContinuousLinearMap.smulRight_apply] using
          congrArg (fun L => L (E i x)) (hc.leibniz (hks j) (has j))
  obtain ⟨T, hT⟩ := exists_curvatureOnFields_derivative_quadrilinearMap D x
  have heval (P Q Y Z : (y : M) → TangentSpace (𝓡 n) y)
      (hP : S P) (hQ : S Q) (hY : S Y) (hZ : S Z) :
      K P Q Y Z x = T (P x) (Q x) (Y x) (Z x) :=
    (hT e.open_baseSet P Q Y Z hP hQ hY hZ hx).symm
  have hdir (i j : Fin n) : K (N (E i) (E j)) A B C x =
      ∑ p, Gamma x i j p • K (E p) A B C x := by
    have hrec : N (E i) (E j) x = ∑ p, Gamma x i j p • E p x :=
      e.eq_sum_localFrameCoeff_smul (I := 𝓡 n) (b := b) hx
    rw [heval _ _ _ _ (hN _ _ (hE i) (hE j)) hA hB hC, hrec]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
    apply Finset.sum_congr rfl
    intro p _
    rw [heval _ _ _ _ (hE p) hA hB hC]
  let B0 := fun i : Fin n => ∑ j, a x i j •
    (N (E i) (K (E j) A B C) x - K (E j) (N (E i) A) B C x -
      K (E j) A (N (E i) B) C x - K (E j) A B (N (E i) C) x)
  let C0 := fun i : Fin n => ∑ j, a x i j • K (N (E i) (E j)) A B C x
  let D0 := fun i : Fin n => ∑ j, da i j • K (E j) A B C x
  let G0 := fun i : Fin n => ∑ p, Gamma x i p i • W p A B C x
  have hbase (i : Fin n) : (∑ j, a x i j • H (E i) (E j) A B C x) = B0 i - C0 i := by
    dsimp only [B0, C0]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [H]
    simp only [smul_sub]
    module
  have hCform (i : Fin n) : C0 i =
      ∑ j, (∑ p, Gamma x i p j * a x i p) • K (E j) A B C x := by
    dsimp only [C0]
    simp_rw [hdir, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro p _
    rw [mul_comm]
  have hGform (i : Fin n) : G0 i =
      ∑ j, (∑ p, Gamma x i p i * a x p j) • K (E j) A B C x := by
    dsimp only [G0, W]
    simp_rw [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_smul]
  have hcancel (i : Fin n) : D0 i + G0 i = -C0 i := by
    rw [hGform, hCform]
    dsimp only [D0]
    rw [← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [← add_smul, ← neg_smul]
    congr 1
    have hd := hda i j
    rw [Finset.sum_add_distrib] at hd
    linarith
  have hdiv (i : Fin n) :
      N (E i) (W i A B C) x - W i (N (E i) A) B C x -
        W i A (N (E i) B) C x - W i A B (N (E i) C) x +
        (∑ p, Gamma x i p i • W p A B C x) = B0 i + D0 i + G0 i := by
    rw [hNK]
    dsimp only [W, B0, D0, G0]
    simp only [Finset.sum_add_distrib, smul_sub, Finset.sum_sub_distrib]
    module
  change (∑ i, ∑ j, a x i j • H (E i) (E j) A B C x) =
    ∑ i, (N (E i) (W i A B C) x - W i (N (E i) A) B C x -
      W i A (N (E i) B) C x - W i A B (N (E i) C) x +
      ∑ p, Gamma x i p i • W p A B C x)
  apply Finset.sum_congr rfl
  intro i _
  rw [hbase, hdiv, add_assoc, hcancel]
  module

end PoincareConjecture.Proofs.M03
