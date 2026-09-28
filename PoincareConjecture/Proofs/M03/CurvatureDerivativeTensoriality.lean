import PoincareConjecture.Proofs.M03.CurvatureDerivativeQuadrilinear

set_option autoImplicit false
set_option maxHeartbeats 1800000

open scoped Manifold ContDiff Bundle Topology BigOperators
open Set

universe u

namespace PoincareConjecture.Proofs.M03

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

open Bundle Manifold in
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 200000 in

theorem curvature_derivative_bochner_local_frame
    {g : RiemannianMetric n M} (D : LeviCivitaData g) (x0 : M) :
    let V := EuclideanSpace ℝ (Fin n)
    let e := trivializationAt V (TangentSpace (𝓡 n)) x0
    let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    let E := e.localFrame b
    let G := fun y : M => ContinuousLinearMap.inCoordinates V
      (TangentSpace (𝓡 n)) (V →L[ℝ] ℝ)
      (fun z => TangentSpace (𝓡 n) z →L[ℝ] ℝ) x0 y x0 y (g.inner y)
    let a := fun (y : M) (i j : Fin n) =>
      (ContinuousLinearMap.inverse (G y) (EuclideanSpace.proj j)) i
    let N := fun (P Q : (y : M) → TangentSpace (𝓡 n) y) y => D.connection Q y (P y)
    let R := fun (A B C : (y : M) → TangentSpace (𝓡 n) y) y => D.curvatureOnFields A B C y
    let K := fun (P A B C : (y : M) → TangentSpace (𝓡 n) y) y =>
      N P (R A B C) y - R (N P A) B C y - R A (N P B) C y - R A B (N P C) y
    let H := fun (P Q A B C : (y : M) → TangentSpace (𝓡 n) y) y =>
      N P (K Q A B C) y - K (N P Q) A B C y -
        K Q (N P A) B C y - K Q A (N P B) C y - K Q A B (N P C) y
    let J := fun (P Q A B C W : (y : M) → TangentSpace (𝓡 n) y) y =>
      N P (H Q A B C W) y - H (N P Q) A B C W y -
        H Q (N P A) B C W y - H Q A (N P B) C W y -
        H Q A B (N P C) W y - H Q A B C (N P W) y
    let pair := fun (y : M) (S T : (Fin 4 → Fin n) → TangentSpace (𝓡 n) y) =>
      ∑ α : Fin 4 → Fin n, ∑ β : Fin 4 → Fin n,
        (∏ r : Fin 4, a y (α r) (β r)) * g.inner y (S α) (T β)
    let k0 := fun (α : Fin 4 → Fin n) =>
      K (E (α 0)) (E (α 1)) (E (α 2)) (E (α 3))
    let k1 := fun i (α : Fin 4 → Fin n) =>
      H (E i) (E (α 0)) (E (α 1)) (E (α 2)) (E (α 3))
    let k2 := fun i j (α : Fin 4 → Fin n) =>
      J (E i) (E j) (E (α 0)) (E (α 1)) (E (α 2)) (E (α 3))
    let q := fun y => pair y (fun α => k0 α y) (fun α => k0 α y)
    let d := fun (P : (y : M) → TangentSpace (𝓡 n) y) (f : M → ℝ) y =>
      mvfderiv (𝓡 n) f y (P y)
    ∀ {x : M}, x ∈ e.baseSet →
      (∑ i, ∑ j, a x i j * (d (E i) (d (E j) q) x - d (N (E i) (E j)) q x)) =
        2 * (∑ i, ∑ j, a x i j * pair x (fun α => k1 i α x) (fun α => k1 j α x)) +
        2 * (∑ i, ∑ j, a x i j * pair x (fun α => k2 i j α x) (fun α => k0 α x)) := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsManifold (𝓡 n) (∞ + 1) M := by
    simpa using (inferInstance : IsManifold (𝓡 n) ∞ M)
  let : IsManifold (𝓡 n) (minSmoothness ℝ 2) M :=
    IsManifold.of_le (n := ∞) (by
      simpa only [minSmoothness_of_isRCLikeNormedField] using
        (ENat.LEInfty.out (m := (2 : ℕ∞ω))))
  let : ContMDiffMul 𝓘(ℝ, ℝ) ∞ ℝ :=
    { contMDiff_mul := by
        rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
        exact contDiff_mul.contMDiff }
  let V := EuclideanSpace ℝ (Fin n)
  let c := chartAt V x0
  let e := trivializationAt V (TangentSpace (𝓡 n)) x0
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let E := e.localFrame b
  let theta := e.localFrameCoeff (𝓡 n) b
  let G := fun y : M => ContinuousLinearMap.inCoordinates V
    (TangentSpace (𝓡 n)) (V →L[ℝ] ℝ)
    (fun z => TangentSpace (𝓡 n) z →L[ℝ] ℝ) x0 y x0 y (g.inner y)
  let a := fun (y : M) (i j : Fin n) =>
    (ContinuousLinearMap.inverse (G y) (EuclideanSpace.proj j)) i
  let N := fun (P Q : (y : M) → TangentSpace (𝓡 n) y) y =>
    D.connection Q y (P y)
  let R := fun (A B C : (y : M) → TangentSpace (𝓡 n) y) y =>
    D.curvatureOnFields A B C y
  let K := fun (P A B C : (y : M) → TangentSpace (𝓡 n) y) y =>
    N P (R A B C) y - R (N P A) B C y -
      R A (N P B) C y - R A B (N P C) y
  let H := fun (P Q A B C : (y : M) → TangentSpace (𝓡 n) y) y =>
    N P (K Q A B C) y - K (N P Q) A B C y -
      K Q (N P A) B C y - K Q A (N P B) C y - K Q A B (N P C) y
  let J := fun (P Q A B C W : (y : M) → TangentSpace (𝓡 n) y) y =>
    N P (H Q A B C W) y - H (N P Q) A B C W y -
      H Q (N P A) B C W y - H Q A (N P B) C W y -
      H Q A B (N P C) W y - H Q A B C (N P W) y
  let Gamma := fun y i j p => theta p y (N (E i) (E j) y)
  let d := fun (P : (y : M) → TangentSpace (𝓡 n) y) (f : M → ℝ) y =>
    mvfderiv (𝓡 n) f y (P y)
  let S := fun W : (y : M) → TangentSpace (𝓡 n) y =>
    ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% W) e.baseSet
  let C := fun f : M → ℝ => ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f e.baseSet
  have hmd (W : (y : M) → TangentSpace (𝓡 n) y) (hW : S W)
      {y : M} (hy : y ∈ e.baseSet) :
      MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) (T% W) y :=
    (hW.contMDiffAt (e.open_baseSet.mem_nhds hy)).mdifferentiableAt (by simp)
  have hcmd (f : M → ℝ) (hf : C f) {y : M} (hy : y ∈ e.baseSet) :
      MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f y :=
    (hf.contMDiffAt (e.open_baseSet.mem_nhds hy)).mdifferentiableAt (by simp)
  have hE (i : Fin n) : S (E i) :=
    e.contMDiffOn_localFrame_baseSet (I := 𝓡 n) ∞ b i
  have hN (P Q : (y : M) → TangentSpace (𝓡 n) y)
      (hP : S P) (hQ : S Q) : S (N P Q) :=
    D.contMDiffOn_connection_apply e.open_baseSet P Q hP hQ
  have hR (P Q W : (y : M) → TangentSpace (𝓡 n) y)
      (hP : S P) (hQ : S Q) (hW : S W) : S (R P Q W) := by
    have hbr : S (VectorField.mlieBracket (𝓡 n) P Q) := by
      intro y hy
      exact ((hP.contMDiffAt (e.open_baseSet.mem_nhds hy)).mlieBracket_vectorField
        (hQ.contMDiffAt (e.open_baseSet.mem_nhds hy)) (m := ⊤) (n := ⊤)
        (by simp)).contMDiffWithinAt
    exact ((hN P _ hP (hN Q W hQ hW)).sub_section
      (hN Q _ hQ (hN P W hP hW))).sub_section (hN _ W hbr hW)
  have hK (P Q A B : (y : M) → TangentSpace (𝓡 n) y)
      (hP : S P) (hQ : S Q) (hA : S A) (hB : S B) : S (K P Q A B) :=
    (((hN P _ hP (hR Q A B hQ hA hB)).sub_section
      (hR _ A B (hN P Q hP hQ) hA hB)).sub_section
      (hR Q _ B hQ (hN P A hP hA) hB)).sub_section
      (hR Q A _ hQ hA (hN P B hP hB))
  have hH (P Q A B C : (y : M) → TangentSpace (𝓡 n) y)
      (hP : S P) (hQ : S Q) (hA : S A) (hB : S B) (hC : S C) :
      S (H P Q A B C) :=
    ((((hN P _ hP (hK Q A B C hQ hA hB hC)).sub_section
      (hK _ A B C (hN P Q hP hQ) hA hB hC)).sub_section
      (hK Q _ B C hQ (hN P A hP hA) hB hC)).sub_section
      (hK Q A _ C hQ hA (hN P B hP hB) hC)).sub_section
      (hK Q A B _ hQ hA hB (hN P C hP hC))
  have hinner (A B : (y : M) → TangentSpace (𝓡 n) y) (hA : S A) (hB : S B) :
      C (fun y => g.inner y (A y) (B y)) := by
    exact hA.inner_bundle hB
  have ha (i j : Fin n) : C (fun y => a y i j) := by
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
  have hchart (f : M → ℝ) (hf : C f) {z : V} (hz : z ∈ c.target) (i : Fin n) :
      d (E i) f (c.symm z) =
        fderiv ℝ (fun w => f (c.symm w)) z (EuclideanSpace.single i 1) := by
    let x := c.symm z
    have hx : x ∈ e.baseSet := by
      simpa only [e, TangentBundle.trivializationAt_baseSet] using c.map_target hz
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
      erw [mvfderiv_comp_apply z (hcmd f hf hx) hcs (EuclideanSpace.single i 1), ← he]
      rfl
    exact (congrArg (mvfderiv (𝓡 n) f x) hframe).trans hfd.symm
  have hda {x : M} (hx : x ∈ e.baseSet) (i j k : Fin n) :
      d (E i) (fun y => a y j k) x =
        -(∑ p, (Gamma x i p j * a x p k + Gamma x i p k * a x j p)) := by
    have hxc : x ∈ c.source := by
      simpa only [e, TangentBundle.trivializationAt_baseSet] using hx
    have hh := metric_inverse_covariant_derivative_coordinates D x0 (c x) (c.map_source hxc) i j k
    have he := hchart (fun y => a y j k) (ha j k) (c.map_source hxc) i
    rw [c.left_inv hxc] at hh he
    exact he.trans hh
  have hasymm {x : M} (hx : x ∈ e.baseSet) (i j : Fin n) : a x i j = a x j i := by
    have hi := metric_inverse_eq_sum_orthonormal_coordinates g x0 x hx i j
    have hj := metric_inverse_eq_sum_orthonormal_coordinates g x0 x hx j i
    change a x i j = _ at hi
    change a x j i = _ at hj
    rw [hi, hj]
    apply Finset.sum_congr rfl
    intro r _
    exact mul_comm _ _

  choose T hT using fun y : M => exists_curvatureOnFields_derivative_quadrilinearMap D y
  have heval (P Q A B : (y : M) → TangentSpace (𝓡 n) y)
      (hP : S P) (hQ : S Q) (hA : S A) (hB : S B)
      {y : M} (hy : y ∈ e.baseSet) :
      K P Q A B y = T y (P y) (Q y) (A y) (B y) :=
    (hT y e.open_baseSet P Q A B hP hQ hA hB hy).symm
  let coeff := fun (i : Fin n) (W : (y : M) → TangentSpace (𝓡 n) y) y =>
    theta i y (W y)
  have hcoeff (i : Fin n) (W : (y : M) → TangentSpace (𝓡 n) y) (hW : S W) :
      C (coeff i W) := contMDiffOn_localFrameCoeff b e.open_baseSet subset_rfl hW i
  have hrec (W : (y : M) → TangentSpace (𝓡 n) y)
      {y : M} (hy : y ∈ e.baseSet) : W y = ∑ i, coeff i W y • E i y :=
    e.eq_sum_localFrameCoeff_smul (I := 𝓡 n) (b := b) hy
  have hlin {y : M} (hy : y ∈ e.baseSet)
      (L : TangentSpace (𝓡 n) y →ₗ[ℝ] TangentSpace (𝓡 n) y)
      (W : (y : M) → TangentSpace (𝓡 n) y) :
      L (W y) = ∑ i, coeff i W y • L (E i y) := by
    rw [hrec W hy, map_sum]
    simp only [map_smul]
  have hc := D.connection.isCovariantDerivativeOn (s := univ)
  have hnsum {y : M} (hy : y ∈ e.baseSet)
      (W : Fin n → (y : M) → TangentSpace (𝓡 n) y)
      (hW : ∀ i, S (W i)) (v : TangentSpace (𝓡 n) y) :
      D.connection (fun y => ∑ i, W i y) y v = ∑ i, D.connection (W i) y v := by
    have aux (s : Finset (Fin n)) :
        D.connection (fun y => ∑ i ∈ s, W i y) y v =
          ∑ i ∈ s, D.connection (W i) y v := by
      induction s using Finset.induction_on with
      | empty =>
        simp only [Finset.sum_empty]
        change D.connection 0 y v = 0
        rw [hc.zero, zero_apply]
      | @insert i s hi ih =>
        simp only [Finset.sum_insert hi]
        change D.connection (W i + fun y => ∑ j ∈ s, W j y) y v = _
        rw [hc.add (hmd _ (hW i) hy)
          (MDifferentiableAt.sum_section fun j _ => hmd _ (hW j) hy), add_apply, ih]
    exact aux Finset.univ
  have hframe {x : M} (hx : x ∈ e.baseSet)
      (P Q : (y : M) → TangentSpace (𝓡 n) y)
      (Z : Fin n → (y : M) → TangentSpace (𝓡 n) y) (f : Fin n → M → ℝ)
      (hQ : S Q) (hZ : ∀ i, S (Z i)) (hf : ∀ i, C (f i))
      (heq : ∀ y ∈ e.baseSet, Q y = ∑ i, f i y • Z i y) :
      N P Q x = ∑ i, (f i x • N P (Z i) x + d P (f i) x • Z i x) := by
    have hs (i : Fin n) : S ((f i) • Z i) := (hf i).smul_section (hZ i)
    have hloc := hc.congr_of_eventuallyEq (hmd Q hQ hx)
      (MDifferentiableAt.sum_section fun i _ => hmd _ (hs i) hx) Filter.univ_mem
      (Filter.eventuallyEq_of_mem (e.open_baseSet.mem_nhds hx) heq)
    calc
      _ = D.connection (fun y => ∑ i, f i y • Z i y) x (P x) :=
        congrArg (fun L => L (P x)) hloc
      _ = ∑ i, D.connection ((f i) • Z i) x (P x) :=
        hnsum hx (fun i => (f i) • Z i) hs (P x)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        simpa only [N, d, add_apply, smul_apply, ContinuousLinearMap.smulRight_apply] using
          congrArg (fun L => L (P x)) (hc.leibniz (hmd _ (hZ i) hx) (hcmd _ (hf i) hx))
  have hdiff {x : M} (hx : x ∈ e.baseSet)
      (F : ((y : M) → TangentSpace (𝓡 n) y) → (y : M) → TangentSpace (𝓡 n) y)
      (L : (y : M) → TangentSpace (𝓡 n) y →ₗ[ℝ] TangentSpace (𝓡 n) y)
      (hF : ∀ Q, S Q → S (F Q))
      (hFL : ∀ Q, S Q → ∀ y ∈ e.baseSet, F Q y = L y (Q y))
      (P Q : (y : M) → TangentSpace (𝓡 n) y) (hQ : S Q) :
      N P (F Q) x - L x (N P Q x) =
        ∑ i, coeff i Q x • (N P (F (E i)) x - L x (N P (E i) x)) := by
    have hFeq (y : M) (hy : y ∈ e.baseSet) : F Q y = ∑ i, coeff i Q y • F (E i) y := by
      rw [hFL Q hQ y hy, hrec Q hy, map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_smul, hFL (E i) (hE i) y hy]
    rw [hframe hx P (F Q) (fun i => F (E i)) (fun i => coeff i Q)
      (hF Q hQ) (fun i => hF (E i) (hE i)) (fun i => hcoeff i Q hQ) hFeq,
      hframe hx P Q E (fun i => coeff i Q) hQ hE (fun i => hcoeff i Q hQ)
        (fun y hy => hrec Q hy), map_sum]
    simp only [map_add, map_smul]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [hFL (E i) (hE i) x hx, smul_sub]
    module

  have hHP {x : M} (hx : x ∈ e.baseSet)
      (P Q A B C : (y : M) → TangentSpace (𝓡 n) y)
      (hP : S P) (hQ : S Q) (hA : S A) (hB : S B) (hC : S C) :
      H P Q A B C x = ∑ i, coeff i P x • H (E i) Q A B C x := by
    let L : TangentSpace (𝓡 n) x →ₗ[ℝ] TangentSpace (𝓡 n) x :=
      (D.connection (K Q A B C) x).toLinearMap -
        ((((T x).flip (A x)).flip (B x)).flip (C x)).comp (D.connection Q x).toLinearMap -
        (((T x (Q x)).flip (B x)).flip (C x)).comp (D.connection A x).toLinearMap -
        ((T x (Q x) (A x)).flip (C x)).comp (D.connection B x).toLinearMap -
        (T x (Q x) (A x) (B x)).comp (D.connection C x).toLinearMap
    have hform (W : (y : M) → TangentSpace (𝓡 n) y) (hW : S W) :
        H W Q A B C x = L (W x) := by
      dsimp only [H]
      rw [heval (N W Q) A B C (hN W Q hW hQ) hA hB hC hx,
        heval Q (N W A) B C hQ (hN W A hW hA) hB hC hx,
        heval Q A (N W B) C hQ hA (hN W B hW hB) hC hx,
        heval Q A B (N W C) hQ hA hB (hN W C hW hC) hx]
      rfl
    rw [hform P hP, hlin hx L P]
    apply Finset.sum_congr rfl
    intro i _
    rw [hform (E i) (hE i)]
  have hHQ {x : M} (hx : x ∈ e.baseSet)
      (P Q A B C : (y : M) → TangentSpace (𝓡 n) y)
      (hP : S P) (hQ : S Q) (hA : S A) (hB : S B) (hC : S C) :
      H P Q A B C x = ∑ i, coeff i Q x • H P (E i) A B C x := by
    let L := fun y => (((T y).flip (A y)).flip (B y)).flip (C y)
    let La := (((T x).flip (N P A x)).flip (B x)).flip (C x)
    let Lb := (((T x).flip (A x)).flip (N P B x)).flip (C x)
    let Lc := (((T x).flip (A x)).flip (B x)).flip (N P C x)
    have hform (W : (y : M) → TangentSpace (𝓡 n) y) (hW : S W) :
        H P W A B C x = (N P (K W A B C) x - L x (N P W x)) -
          La (W x) - Lb (W x) - Lc (W x) := by
      dsimp only [H]
      rw [heval (N P W) A B C (hN P W hP hW) hA hB hC hx,
        heval W (N P A) B C hW (hN P A hP hA) hB hC hx,
        heval W A (N P B) C hW hA (hN P B hP hB) hC hx,
        heval W A B (N P C) hW hA hB (hN P C hP hC) hx]
      rfl
    rw [hform Q hQ, hdiff hx (fun W => K W A B C) L
      (fun W hW => hK W A B C hW hA hB hC)
      (fun W hW y hy => heval W A B C hW hA hB hC hy) P Q hQ,
      hlin hx La Q, hlin hx Lb Q, hlin hx Lc Q,
      ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [hform (E i) (hE i)]
    simp only [smul_sub]
  have hHA {x : M} (hx : x ∈ e.baseSet)
      (P Q A B C : (y : M) → TangentSpace (𝓡 n) y)
      (hP : S P) (hQ : S Q) (hA : S A) (hB : S B) (hC : S C) :
      H P Q A B C x = ∑ i, coeff i A x • H P Q (E i) B C x := by
    let L := fun y => ((T y (Q y)).flip (B y)).flip (C y)
    let Lq := ((T x (N P Q x)).flip (B x)).flip (C x)
    let Lb := ((T x (Q x)).flip (N P B x)).flip (C x)
    let Lc := ((T x (Q x)).flip (B x)).flip (N P C x)
    have hform (W : (y : M) → TangentSpace (𝓡 n) y) (hW : S W) :
        H P Q W B C x = (N P (K Q W B C) x - L x (N P W x)) -
          Lq (W x) - Lb (W x) - Lc (W x) := by
      dsimp only [H]
      rw [heval (N P Q) W B C (hN P Q hP hQ) hW hB hC hx,
        heval Q (N P W) B C hQ (hN P W hP hW) hB hC hx,
        heval Q W (N P B) C hQ hW (hN P B hP hB) hC hx,
        heval Q W B (N P C) hQ hW hB (hN P C hP hC) hx]
      dsimp only [L, Lq, Lb, Lc, LinearMap.flip_apply]
      module
    rw [hform A hA, hdiff hx (fun W => K Q W B C) L
      (fun W hW => hK Q W B C hQ hW hB hC)
      (fun W hW y hy => heval Q W B C hQ hW hB hC hy) P A hA,
      hlin hx Lq A, hlin hx Lb A, hlin hx Lc A,
      ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [hform (E i) (hE i)]
    simp only [smul_sub]
  have hHB {x : M} (hx : x ∈ e.baseSet)
      (P Q A B C : (y : M) → TangentSpace (𝓡 n) y)
      (hP : S P) (hQ : S Q) (hA : S A) (hB : S B) (hC : S C) :
      H P Q A B C x = ∑ i, coeff i B x • H P Q A (E i) C x := by
    let L := fun y => (T y (Q y) (A y)).flip (C y)
    let Lq := (T x (N P Q x) (A x)).flip (C x)
    let La := (T x (Q x) (N P A x)).flip (C x)
    let Lc := (T x (Q x) (A x)).flip (N P C x)
    have hform (W : (y : M) → TangentSpace (𝓡 n) y) (hW : S W) :
        H P Q A W C x = (N P (K Q A W C) x - L x (N P W x)) -
          Lq (W x) - La (W x) - Lc (W x) := by
      dsimp only [H]
      rw [heval (N P Q) A W C (hN P Q hP hQ) hA hW hC hx,
        heval Q (N P A) W C hQ (hN P A hP hA) hW hC hx,
        heval Q A (N P W) C hQ hA (hN P W hP hW) hC hx,
        heval Q A W (N P C) hQ hA hW (hN P C hP hC) hx]
      dsimp only [L, Lq, La, Lc, LinearMap.flip_apply]
      module
    rw [hform B hB, hdiff hx (fun W => K Q A W C) L
      (fun W hW => hK Q A W C hQ hA hW hC)
      (fun W hW y hy => heval Q A W C hQ hA hW hC hy) P B hB,
      hlin hx Lq B, hlin hx La B, hlin hx Lc B,
      ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [hform (E i) (hE i)]
    simp only [smul_sub]
  have hHC {x : M} (hx : x ∈ e.baseSet)
      (P Q A B C : (y : M) → TangentSpace (𝓡 n) y)
      (hP : S P) (hQ : S Q) (hA : S A) (hB : S B) (hC : S C) :
      H P Q A B C x = ∑ i, coeff i C x • H P Q A B (E i) x := by
    let L := fun y => T y (Q y) (A y) (B y)
    let Lq := T x (N P Q x) (A x) (B x)
    let La := T x (Q x) (N P A x) (B x)
    let Lb := T x (Q x) (A x) (N P B x)
    have hform (W : (y : M) → TangentSpace (𝓡 n) y) (hW : S W) :
        H P Q A B W x = (N P (K Q A B W) x - L x (N P W x)) -
          Lq (W x) - La (W x) - Lb (W x) := by
      dsimp only [H]
      rw [heval (N P Q) A B W (hN P Q hP hQ) hA hB hW hx,
        heval Q (N P A) B W hQ (hN P A hP hA) hB hW hx,
        heval Q A (N P B) W hQ hA (hN P B hP hB) hW hx,
        heval Q A B (N P W) hQ hA hB (hN P W hP hW) hx]
      dsimp only [L, Lq, La, Lb]
      module
    rw [hform C hC, hdiff hx (fun W => K Q A B W) L
      (fun W hW => hK Q A B W hQ hA hB hW)
      (fun W hW y hy => heval Q A B W hQ hA hB hW hy) P C hC,
      hlin hx Lq C, hlin hx La C, hlin hx Lb C,
      ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [hform (E i) (hE i)]
    simp only [smul_sub]
  let k0 := fun (α : Fin 4 → Fin n) =>
    K (E (α 0)) (E (α 1)) (E (α 2)) (E (α 3))
  let k1 := fun i (α : Fin 4 → Fin n) =>
    H (E i) (E (α 0)) (E (α 1)) (E (α 2)) (E (α 3))
  let k2 := fun i j (α : Fin 4 → Fin n) =>
    J (E i) (E j) (E (α 0)) (E (α 1)) (E (α 2)) (E (α 3))
  let act := fun (x : M) (i : Fin n)
      (U : (Fin 4 → Fin n) → TangentSpace (𝓡 n) x) α =>
    ∑ r : Fin 4, ∑ p, Gamma x i (α r) p • U (Function.update α r p)
  have hKfirst {x : M} (hx : x ∈ e.baseSet)
      (P Q A B : (y : M) → TangentSpace (𝓡 n) y)
      (hP : S P) (hQ : S Q) (hA : S A) (hB : S B) :
      K P Q A B x = ∑ i, coeff i P x • K (E i) Q A B x := by
    rw [heval P Q A B hP hQ hA hB hx]
    change ((((T x).flip (Q x)).flip (A x)).flip (B x)) (P x) = _
    rw [hlin hx]
    apply Finset.sum_congr rfl
    intro i _
    rw [heval (E i) Q A B (hE i) hQ hA hB hx]
    rfl
  have hKsecond {x : M} (hx : x ∈ e.baseSet)
      (P Q A B : (y : M) → TangentSpace (𝓡 n) y)
      (hP : S P) (hQ : S Q) (hA : S A) (hB : S B) :
      K P Q A B x = ∑ i, coeff i Q x • K P (E i) A B x := by
    rw [heval P Q A B hP hQ hA hB hx]
    change (((T x (P x)).flip (A x)).flip (B x)) (Q x) = _
    rw [hlin hx]
    apply Finset.sum_congr rfl
    intro i _
    rw [heval P (E i) A B hP (hE i) hA hB hx]
    rfl
  have hKthird {x : M} (hx : x ∈ e.baseSet)
      (P Q A B : (y : M) → TangentSpace (𝓡 n) y)
      (hP : S P) (hQ : S Q) (hA : S A) (hB : S B) :
      K P Q A B x = ∑ i, coeff i A x • K P Q (E i) B x := by
    rw [heval P Q A B hP hQ hA hB hx]
    change ((T x (P x) (Q x)).flip (B x)) (A x) = _
    rw [hlin hx]
    apply Finset.sum_congr rfl
    intro i _
    rw [heval P Q (E i) B hP hQ (hE i) hB hx]
    rfl
  have hKfourth {x : M} (hx : x ∈ e.baseSet)
      (P Q A B : (y : M) → TangentSpace (𝓡 n) y)
      (hP : S P) (hQ : S Q) (hA : S A) (hB : S B) :
      K P Q A B x = ∑ i, coeff i B x • K P Q A (E i) x := by
    rw [heval P Q A B hP hQ hA hB hx, hlin hx]
    apply Finset.sum_congr rfl
    intro i _
    rw [heval P Q A (E i) hP hQ hA (hE i) hx]
  have hk0 {x : M} (hx : x ∈ e.baseSet) (i : Fin n) (α : Fin 4 → Fin n) :
      N (E i) (k0 α) x = k1 i α x + act x i (fun β => k0 β x) α := by
    have h0 := hKfirst hx (N (E i) (E (α 0))) (E (α 1)) (E (α 2)) (E (α 3))
      (hN _ _ (hE _) (hE _)) (hE _) (hE _) (hE _)
    have h1 := hKsecond hx (E (α 0)) (N (E i) (E (α 1))) (E (α 2)) (E (α 3))
      (hE _) (hN _ _ (hE _) (hE _)) (hE _) (hE _)
    have h2 := hKthird hx (E (α 0)) (E (α 1)) (N (E i) (E (α 2))) (E (α 3))
      (hE _) (hE _) (hN _ _ (hE _) (hE _)) (hE _)
    have h3 := hKfourth hx (E (α 0)) (E (α 1)) (E (α 2)) (N (E i) (E (α 3)))
      (hE _) (hE _) (hE _) (hN _ _ (hE _) (hE _))
    dsimp only [k1, H]
    rw [h0, h1, h2, h3]
    simp [act, Fin.sum_univ_four, k0, coeff, Gamma]
  have hk1 {x : M} (hx : x ∈ e.baseSet) (i j : Fin n) (α : Fin 4 → Fin n) :
      N (E i) (k1 j α) x = k2 i j α x +
        (∑ p, Gamma x i j p • k1 p α x) + act x i (fun β => k1 j β x) α := by
    have hp := hHP hx (N (E i) (E j)) (E (α 0)) (E (α 1)) (E (α 2)) (E (α 3))
      (hN _ _ (hE _) (hE _)) (hE _) (hE _) (hE _) (hE _)
    have h0 := hHQ hx (E j) (N (E i) (E (α 0))) (E (α 1)) (E (α 2)) (E (α 3))
      (hE _) (hN _ _ (hE _) (hE _)) (hE _) (hE _) (hE _)
    have h1 := hHA hx (E j) (E (α 0)) (N (E i) (E (α 1))) (E (α 2)) (E (α 3))
      (hE _) (hE _) (hN _ _ (hE _) (hE _)) (hE _) (hE _)
    have h2 := hHB hx (E j) (E (α 0)) (E (α 1)) (N (E i) (E (α 2))) (E (α 3))
      (hE _) (hE _) (hE _) (hN _ _ (hE _) (hE _)) (hE _)
    have h3 := hHC hx (E j) (E (α 0)) (E (α 1)) (E (α 2)) (N (E i) (E (α 3)))
      (hE _) (hE _) (hE _) (hE _) (hN _ _ (hE _) (hE _))
    dsimp only [k2, J]
    rw [hp, h0, h1, h2, h3]
    simp [act, Fin.sum_univ_four, k1, coeff, Gamma]
    module
  let w := fun (y : M) (α β : Fin 4 → Fin n) => ∏ r, a y (α r) (β r)
  let pair := fun (y : M) (U W : (Fin 4 → Fin n) → TangentSpace (𝓡 n) y) =>
    ∑ α, ∑ β, w y α β * g.inner y (U α) (W β)
  have hw (α β : Fin 4 → Fin n) : C (fun y => w y α β) :=
    contMDiffOn_finsetProd fun r _ => ha (α r) (β r)
  have hpair (U W : (Fin 4 → Fin n) → (y : M) → TangentSpace (𝓡 n) y)
      (hU : ∀ α, S (U α)) (hW : ∀ α, S (W α)) :
      C (fun y => pair y (fun α => U α y) (fun α => W α y)) :=
    contMDiffOn_finsetSum fun α _ => contMDiffOn_finsetSum fun β _ =>
      (hw α β).mul (hinner (U α) (W β) (hU α) (hW β))
  have hdsum {ι : Type} [Fintype ι] {x : M} (hx : x ∈ e.baseSet)
      (P : (y : M) → TangentSpace (𝓡 n) y) (f : ι → M → ℝ) (hf : ∀ i, C (f i)) :
      d P (fun y => ∑ i, f i y) x = ∑ i, d P (f i) x := by
    have aux (s : Finset ι) :
        d P (fun y => ∑ i ∈ s, f i y) x = ∑ i ∈ s, d P (f i) x := by
      induction s using Finset.induction_on with
      | empty => simp only [Finset.sum_empty, d, mvfderiv_const, zero_apply]
      | @insert i s hi ih =>
        simp only [Finset.sum_insert hi]
        dsimp only [d] at ih ⊢
        rw [mvfderiv_fun_add (hcmd _ (hf i) hx)
          (hcmd _ (contMDiffOn_finsetSum fun j _ => hf j) hx), add_apply, ih]
    exact aux Finset.univ
  have hdprod {x : M} (hx : x ∈ e.baseSet) (i : Fin n) (α β : Fin 4 → Fin n) :
      d (E i) (fun y => w y α β) x =
        ∑ r : Fin 4, (∏ s ∈ Finset.univ.erase r, a x (α s) (β s)) *
          d (E i) (fun y => a y (α r) (β r)) x := by
    have aux (s : Finset (Fin 4)) :
        d (E i) (fun y => ∏ r ∈ s, a y (α r) (β r)) x =
          ∑ r ∈ s, (∏ t ∈ s.erase r, a x (α t) (β t)) *
            d (E i) (fun y => a y (α r) (β r)) x := by
      induction s using Finset.induction_on with
      | empty => simp only [Finset.prod_empty, Finset.sum_empty, d, mvfderiv_const, zero_apply]
      | @insert r s hr ih =>
        simp only [Finset.prod_insert hr, Finset.sum_insert hr, Finset.erase_insert hr]
        have hmul := congrArg (fun L => L (E i x)) (mvfderiv_fun_mul
          (hcmd _ (ha (α r) (β r)) hx)
          (hcmd _ (contMDiffOn_finsetProd (t := s) fun t _ => ha (α t) (β t)) hx))
        change d (E i) (fun y => a y (α r) (β r) * ∏ t ∈ s, a y (α t) (β t)) x = _
        simp only [add_apply, smul_apply, smul_eq_mul] at hmul
        change d (E i) (fun y => a y (α r) (β r) * ∏ t ∈ s, a y (α t) (β t)) x =
          a x (α r) (β r) * d (E i) (fun y => ∏ t ∈ s, a y (α t) (β t)) x +
            (∏ t ∈ s, a x (α t) (β t)) * d (E i) (fun y => a y (α r) (β r)) x at hmul
        rw [hmul, ih, add_comm, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro t ht
        rw [Finset.erase_insert_of_ne (ne_of_mem_of_not_mem ht hr).symm,
          Finset.prod_insert (by simp [hr])]
        ring
    exact aux Finset.univ
  have hdpair {x : M} (hx : x ∈ e.baseSet) (i : Fin n)
      (U W : (Fin 4 → Fin n) → (y : M) → TangentSpace (𝓡 n) y)
      (hU : ∀ α, S (U α)) (hW : ∀ α, S (W α)) :
      d (E i) (fun y => pair y (fun α => U α y) (fun α => W α y)) x =
        ∑ α, ∑ β, (
          w x α β * (g.inner x (N (E i) (U α) x) (W β x) +
            g.inner x (U α x) (N (E i) (W β) x)) +
          d (E i) (fun y => w y α β) x * g.inner x (U α x) (W β x)) := by
    dsimp only [pair]
    rw [hdsum hx (E i) (fun α y => ∑ β, w y α β * g.inner y (U α y) (W β y))
      (fun α => contMDiffOn_finsetSum (t := Finset.univ) fun β _ =>
      (hw α β).mul (hinner (U α) (W β) (hU α) (hW β)))]
    apply Finset.sum_congr rfl
    intro α _
    rw [hdsum hx (E i) (fun β y => w y α β * g.inner y (U α y) (W β y))
      (fun β => (hw α β).mul
      (hinner (U α) (W β) (hU α) (hW β)))]
    apply Finset.sum_congr rfl
    intro β _
    have hh := congrArg (fun L => L (E i x)) (mvfderiv_fun_mul
      (hcmd _ (hw α β) hx) (hcmd _ (hinner (U α) (W β) (hU α) (hW β)) hx))
    dsimp only [d, N]
    simpa only [add_apply, smul_apply, smul_eq_mul,
      D.mvfderiv_inner (E i) (U α) (W β) (hmd _ (hU α) hx) (hmd _ (hW β) hx),
      mul_comm] using hh

  have slotSwap (r : Fin 4) (f : (Fin 4 → Fin n) → Fin n → ℝ) :
      (∑ α, ∑ p, f α p) = ∑ α, ∑ p, f (Function.update α r p) (α r) := by
    let swap := fun q : (Fin 4 → Fin n) × Fin n => (Function.update q.1 r q.2, q.1 r)
    have hs : Function.Involutive swap := by
      intro q
      apply Prod.ext
      · funext j
        by_cases hj : j = r
        · subst j
          simp [swap]
        · simp [swap, Function.update_of_ne hj]
      · simp [swap]
    let eqv : ((Fin 4 → Fin n) × Fin n) ≃ ((Fin 4 → Fin n) × Fin n) :=
      { toFun := swap, invFun := swap, left_inv := hs, right_inv := hs }
    have hh := (eqv.sum_comp (fun q => f q.1 q.2)).symm
    change (∑ q : (Fin 4 → Fin n) × Fin n, f q.1 q.2) =
      ∑ q : (Fin 4 → Fin n) × Fin n, f (Function.update q.1 r q.2) (q.1 r) at hh
    simpa only [Fintype.sum_prod_type] using hh
  have weightCancellation (a G : Fin n → Fin n → ℝ)
      (F : (Fin 4 → Fin n) → (Fin 4 → Fin n) → ℝ) :
      let W := fun α β : Fin 4 → Fin n => ∏ r, a (α r) (β r)
      let w := fun r (α β : Fin 4 → Fin n) =>
        ∏ s ∈ Finset.univ.erase r, a (α s) (β s)
      (∑ α, ∑ β, ∑ r, w r α β *
        (∑ p, (G p (α r) * a p (β r) + G p (β r) * a (α r) p)) * F α β) =
        ∑ α, ∑ β, W α β *
          ((∑ r, ∑ p, G (α r) p * F (Function.update α r p) β) +
            ∑ r, ∑ p, G (β r) p * F α (Function.update β r p)) := by
    dsimp only
    let W := fun α β : Fin 4 → Fin n => ∏ r, a (α r) (β r)
    let w := fun r (α β : Fin 4 → Fin n) =>
      ∏ s ∈ Finset.univ.erase r, a (α s) (β s)
    have hWL (r : Fin 4) (α β : Fin 4 → Fin n) (p : Fin n) :
        W (Function.update α r p) β = w r α β * a p (β r) := by
      dsimp only [W, w]
      rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ r)]
      simp only [Function.update_self]
      congr 1
      apply Finset.prod_congr rfl
      intro s hs
      rw [Function.update_of_ne (Finset.mem_erase.mp hs).1]
    have hWR (r : Fin 4) (α β : Fin 4 → Fin n) (p : Fin n) :
        W α (Function.update β r p) = w r α β * a (α r) p := by
      dsimp only [W, w]
      rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ r)]
      simp only [Function.update_self]
      congr 1
      apply Finset.prod_congr rfl
      intro s hs
      rw [Function.update_of_ne (Finset.mem_erase.mp hs).1]
    have hL (r : Fin 4) (β : Fin 4 → Fin n) :
        (∑ α, ∑ p, W α β * (G (α r) p * F (Function.update α r p) β)) =
          ∑ α, ∑ p, w r α β * (G p (α r) * a p (β r)) * F α β := by
      rw [slotSwap r]
      apply Finset.sum_congr rfl
      intro α _
      apply Finset.sum_congr rfl
      intro p _
      rw [hWL]
      simp only [Function.update_self, Function.update_idem, Function.update_eq_self]
      ring
    have hR (r : Fin 4) (α : Fin 4 → Fin n) :
        (∑ β, ∑ p, W α β * (G (β r) p * F α (Function.update β r p))) =
          ∑ β, ∑ p, w r α β * (G p (β r) * a (α r) p) * F α β := by
      rw [slotSwap r]
      apply Finset.sum_congr rfl
      intro β _
      apply Finset.sum_congr rfl
      intro p _
      rw [hWR]
      simp only [Function.update_self, Function.update_idem, Function.update_eq_self]
      ring
    have reorder (f : (Fin 4 → Fin n) → (Fin 4 → Fin n) → Fin 4 → Fin n → ℝ) :
        (∑ α, ∑ β, ∑ r, ∑ p, f α β r p) = ∑ r, ∑ β, ∑ α, ∑ p, f α β r p := by
      calc
        _ = ∑ β, ∑ α, ∑ r, ∑ p, f α β r p := Finset.sum_comm
        _ = ∑ β, ∑ r, ∑ α, ∑ p, f α β r p := by
          apply Finset.sum_congr rfl
          intro β _
          exact Finset.sum_comm
        _ = _ := Finset.sum_comm
    change (∑ α, ∑ β, ∑ r, w r α β *
        (∑ p, (G p (α r) * a p (β r) + G p (β r) * a (α r) p)) * F α β) =
      ∑ α, ∑ β, W α β *
        ((∑ r, ∑ p, G (α r) p * F (Function.update α r p) β) +
          ∑ r, ∑ p, G (β r) p * F α (Function.update β r p))
    simp only [Finset.mul_sum, Finset.sum_mul, mul_add, add_mul, Finset.sum_add_distrib]
    congr 1
    · calc
        _ = ∑ r, ∑ β, ∑ α, ∑ p,
            w r α β * (G p (α r) * a p (β r)) * F α β := reorder _
        _ = ∑ r, ∑ β, ∑ α, ∑ p,
            W α β * (G (α r) p * F (Function.update α r p) β) := by
          apply Finset.sum_congr rfl
          intro r _
          apply Finset.sum_congr rfl
          intro β _
          exact (hL r β).symm
        _ = _ := (reorder _).symm
    · calc
        _ = ∑ α, ∑ r, ∑ β, ∑ p,
            w r α β * (G p (β r) * a (α r) p) * F α β := by
          apply Finset.sum_congr rfl
          intro α _
          exact Finset.sum_comm
        _ = ∑ α, ∑ r, ∑ β, ∑ p,
            W α β * (G (β r) p * F α (Function.update β r p)) := by
          apply Finset.sum_congr rfl
          intro α _
          apply Finset.sum_congr rfl
          intro r _
          exact (hR r α).symm
        _ = _ := by
          apply Finset.sum_congr rfl
          intro α _
          exact Finset.sum_comm
  have hpairD {x : M} (hx : x ∈ e.baseSet) (i : Fin n)
      (U W : (Fin 4 → Fin n) → (y : M) → TangentSpace (𝓡 n) y)
      (U' W' : (Fin 4 → Fin n) → TangentSpace (𝓡 n) x)
      (hU : ∀ α, S (U α)) (hW : ∀ α, S (W α))
      (hNU : ∀ α, N (E i) (U α) x = U' α + act x i (fun β => U β x) α)
      (hNW : ∀ α, N (E i) (W α) x = W' α + act x i (fun β => W β x) α) :
      d (E i) (fun y => pair y (fun α => U α y) (fun α => W α y)) x =
        pair x U' (fun α => W α x) + pair x (fun α => U α x) W' := by
    have hweight := weightCancellation (a x) (Gamma x i)
      (fun α β => g.inner x (U α x) (W β x))
    have hcancel : (∑ α, ∑ β, d (E i) (fun y => w y α β) x *
        g.inner x (U α x) (W β x)) =
        -(pair x (act x i (fun α => U α x)) (fun α => W α x) +
          pair x (fun α => U α x) (act x i (fun α => W α x))) := by
      simp_rw [hdprod hx i, hda hx i]
      simp only [mul_neg, Finset.sum_neg_distrib, neg_mul, Finset.sum_mul]
      rw [hweight]
      simp only [pair, w, act, map_sum, sum_apply, map_smul, smul_apply, smul_eq_mul,
        mul_add, Finset.sum_add_distrib]
    rw [hdpair hx i U W hU hW]
    simp only [Finset.sum_add_distrib]
    rw [hcancel]
    simp only [hNU, hNW, pair, map_add, add_apply, mul_add, Finset.sum_add_distrib]
    ring
  have hpairSym {x : M} (hx : x ∈ e.baseSet)
      (U W : (Fin 4 → Fin n) → TangentSpace (𝓡 n) x) :
      pair x U W = pair x W U := by
    dsimp only [pair]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro α _
    apply Finset.sum_congr rfl
    intro β _
    rw [g.symm]
    congr 1
    exact Finset.prod_congr rfl (fun r _ => hasymm hx _ _)
  have hpairAdd (x : M) (U V W : (Fin 4 → Fin n) → TangentSpace (𝓡 n) x) :
      pair x (fun α => U α + V α) W = pair x U W + pair x V W := by
    simp only [pair, map_add, add_apply, mul_add, Finset.sum_add_distrib]
  have hpairSum (x : M) (f : Fin n → ℝ)
      (U : Fin n → (Fin 4 → Fin n) → TangentSpace (𝓡 n) x)
      (W : (Fin 4 → Fin n) → TangentSpace (𝓡 n) x) :
      pair x (fun α => ∑ p, f p • U p α) W = ∑ p, f p * pair x (U p) W := by
    simp only [pair, map_sum, sum_apply, map_smul, smul_apply, smul_eq_mul,
      Finset.mul_sum]
    calc
      _ = ∑ α, ∑ p, ∑ β, w x α β * (f p * g.inner x (U p α) (W β)) := by
        apply Finset.sum_congr rfl
        intro α _
        exact Finset.sum_comm
      _ = ∑ p, ∑ α, ∑ β, w x α β * (f p * g.inner x (U p α) (W β)) :=
        Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro p _
        apply Finset.sum_congr rfl
        intro α _
        apply Finset.sum_congr rfl
        intro β _
        ring
  have hS0 (α : Fin 4 → Fin n) : S (k0 α) :=
    hK _ _ _ _ (hE _) (hE _) (hE _) (hE _)
  have hS1 (i : Fin n) (α : Fin 4 → Fin n) : S (k1 i α) :=
    hH _ _ _ _ _ (hE _) (hE _) (hE _) (hE _) (hE _)
  let q := fun y => pair y (fun α => k0 α y) (fun α => k0 α y)
  have hfirst {x : M} (hx : x ∈ e.baseSet) (i : Fin n) :
      d (E i) q x = 2 * pair x (fun α => k1 i α x) (fun α => k0 α x) := by
    change d (E i) (fun y => pair y (fun α => k0 α y) (fun α => k0 α y)) x = _
    rw [hpairD hx i k0 k0 _ _ hS0 hS0 (hk0 hx i) (hk0 hx i),
      hpairSym hx (fun α => k0 α x) (fun α => k1 i α x)]
    ring
  have hsecond {x : M} (hx : x ∈ e.baseSet) (i j : Fin n) :
      d (E i) (fun y => pair y (fun α => k1 j α y) (fun α => k0 α y)) x =
        pair x (fun α => k2 i j α x) (fun α => k0 α x) +
          (∑ p, Gamma x i j p * pair x (fun α => k1 p α x) (fun α => k0 α x)) +
          pair x (fun α => k1 j α x) (fun α => k1 i α x) := by
    rw [hpairD hx i (k1 j) k0 _ _ (hS1 j) hS0 (hk1 hx i j) (hk0 hx i),
      hpairAdd, hpairSum]
  have htwice {x : M} (hx : x ∈ e.baseSet)
      (P : (y : M) → TangentSpace (𝓡 n) y) (f : M → ℝ) (hf : C f) :
      d P (fun y => 2 * f y) x = 2 * d P f x := by
    have heq : (fun y => 2 * f y) = f + f := by
      funext y
      exact two_mul _
    rw [heq]
    dsimp only [d]
    rw [mvfderiv_add (hcmd f hf hx) (hcmd f hf hx)]
    simp only [add_apply, two_mul]
  have hhessian {x : M} (hx : x ∈ e.baseSet) (i j : Fin n) :
      d (E i) (d (E j) q) x - d (N (E i) (E j)) q x =
        2 * pair x (fun α => k1 i α x) (fun α => k1 j α x) +
          2 * pair x (fun α => k2 i j α x) (fun α => k0 α x) := by
    have heq : d (E j) q =ᶠ[𝓝 x]
        (fun y => 2 * pair y (fun α => k1 j α y) (fun α => k0 α y)) :=
      Filter.eventuallyEq_of_mem (e.open_baseSet.mem_nhds hx) (fun y hy => hfirst hy j)
    have hd : d (E i) (d (E j) q) x =
        d (E i) (fun y => 2 * pair y (fun α => k1 j α y) (fun α => k0 α y)) x := by
      change (mfderiv (𝓡 n) 𝓘(ℝ, ℝ) (d (E j) q) x) (E i x) =
        (mfderiv (𝓡 n) 𝓘(ℝ, ℝ)
          (fun y => 2 * pair y (fun α => k1 j α y) (fun α => k0 α y)) x) (E i x)
      exact congrArg (fun L => L (E i x)) (heq.mfderiv_eq (I := 𝓡 n) (I' := 𝓘(ℝ, ℝ)))
    have hdir : d (N (E i) (E j)) q x =
        2 * ∑ p, Gamma x i j p * pair x (fun α => k1 p α x) (fun α => k0 α x) := by
      dsimp only [d]
      rw [hrec (N (E i) (E j)) hx, map_sum]
      simp only [map_smul, smul_eq_mul]
      change (∑ p, Gamma x i j p * d (E p) q x) = _
      simp_rw [hfirst hx]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      ring
    rw [hd, htwice hx (E i) _ (hpair (k1 j) k0 (hS1 j) hS0), hsecond hx i j, hdir,
      hpairSym hx (fun α => k1 j α x) (fun α => k1 i α x)]
    ring
  change ∀ {x : M}, x ∈ e.baseSet →
    (∑ i, ∑ j, a x i j * (d (E i) (d (E j) q) x - d (N (E i) (E j)) q x)) =
      2 * (∑ i, ∑ j, a x i j * pair x (fun α => k1 i α x) (fun α => k1 j α x)) +
      2 * (∑ i, ∑ j, a x i j * pair x (fun α => k2 i j α x) (fun α => k0 α x))
  intro x hx
  simp_rw [hhessian hx]
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;>
    apply Finset.sum_congr rfl <;> intro j _ <;> ring

end PoincareConjecture.Proofs.M03
