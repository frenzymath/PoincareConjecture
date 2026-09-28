import PoincareConjecture.Proofs.M03.CurvatureDifferenceFlux

set_option autoImplicit false
set_option maxHeartbeats 1800000

open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle Manifold Set

universe u

namespace PoincareConjecture.Proofs.M03

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 200000 in
set_option maxRecDepth 2000 in

theorem ricciFlow_curvature_derivative_diffusion_reaction_localFrame
    {I : Set ℝ} (F : RicciFlow n M I) {t : ℝ} (ht : t ∈ interior I) (x0 : M) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric 0).toRiemannianMetric⟩
    let V := EuclideanSpace ℝ (Fin n)
    let g := F.metric t
    let e := trivializationAt V (TangentSpace (𝓡 n)) x0
    let E := e.localFrame (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    let G := fun y : M => ContinuousLinearMap.inCoordinates V
      (TangentSpace (𝓡 n)) (V →L[ℝ] ℝ)
      (fun z => TangentSpace (𝓡 n) z →L[ℝ] ℝ) x0 y x0 y (g.inner y)
    let a := fun (y : M) (i j : Fin n) =>
      (ContinuousLinearMap.inverse (G y) (EuclideanSpace.proj j)) i
    let Nt := fun s (P Q : (y : M) → TangentSpace (𝓡 n) y) y =>
      (F.connection s).connection Q y (P y)
    let Rt := fun s (A B C : (y : M) → TangentSpace (𝓡 n) y) y =>
      (F.connection s).curvatureOnFields A B C y
    let Kt := fun s (P A B C : (y : M) → TangentSpace (𝓡 n) y) y =>
      Nt s P (Rt s A B C) y - Rt s (Nt s P A) B C y -
        Rt s A (Nt s P B) C y - Rt s A B (Nt s P C) y
    let N := Nt t
    let R := Rt t
    let K := Kt t
    let H := fun (P Q A B C : (y : M) → TangentSpace (𝓡 n) y) y =>
      N P (K Q A B C) y - K (N P Q) A B C y -
        K Q (N P A) B C y - K Q A (N P B) C y - K Q A B (N P C) y
    let J := fun (P Q A B C W : (y : M) → TangentSpace (𝓡 n) y) y =>
      N P (H Q A B C W) y - H (N P Q) A B C W y -
        H Q (N P A) B C W y - H Q A (N P B) C W y -
        H Q A B (N P C) W y - H Q A B C (N P W) y
    let Co := fun (P X Y A B C : (y : M) → TangentSpace (𝓡 n) y) y =>
      R P X (K Y A B C) y - K (R P X Y) A B C y -
        K Y (R P X A) B C y - K Y A (R P X B) C y - K Y A B (R P X C) y +
        K X P Y (R A B C) y + R P Y (K X A B C) y -
        K X (R P Y A) B C y - R (K X P Y A) B C y -
        K X A (R P Y B) C y - R A (K X P Y B) C y -
        K X A B (R P Y C) y - R A B (K X P Y C) y
    let DZ := fun (P A B C X Y : (y : M) → TangentSpace (𝓡 n) y) y =>
      K P (R A B X) Y C y + R (K P A B X) Y C y -
        (2 : ℝ) • K P B X (R Y A C) y - (2 : ℝ) • R B X (K P Y A C) y +
        (2 : ℝ) • K P X A (R B Y C) y + (2 : ℝ) • R X A (K P B Y C) y +
        K P (R A B C) X Y y + R (K P A B C) X Y y -
        K P (R A X Y) B C y - R (K P A X Y) B C y -
        K P A (R B X Y) C y - R A (K P B X Y) C y -
        K P A B (R C X Y) y - R A B (K P C X Y) y
    let Btime := fun (P Q : (y : M) → TangentSpace (𝓡 n) y) y =>
      deriv (fun s => Nt s P Q y) t
    ∀ {x : M}, x ∈ e.baseSet → ∀ P A B C : (y : M) → TangentSpace (𝓡 n) y,
      ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% P) e.baseSet →
      ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% A) e.baseSet →
      ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% B) e.baseSet →
      ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% C) e.baseSet →
      deriv (fun s => Kt s P A B C x) t -
        (∑ i, ∑ j, a x i j • J (E i) (E j) P A B C x) =
        (∑ i, ∑ j, a x i j • (Co P (E i) (E j) A B C x + DZ P A B C (E i) (E j) x)) +
          Btime P (R A B C) x - R (Btime P A) B C x -
          R A (Btime P B) C x - R A B (Btime P C) x := by
  classical
  let g := F.metric t
  let D := F.connection t
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric 0).toRiemannianMetric⟩
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
  let GP := fun (P : (y : M) → TangentSpace (𝓡 n) y) y i p => coeff p (N P (E i)) y
  have hGP {x : M} (hx : x ∈ e.baseSet)
      (P : (y : M) → TangentSpace (𝓡 n) y) (i p : Fin n) :
      GP P x i p = ∑ k, coeff k P x * Gamma x k i p := by
    have hh := congrArg (fun v => theta p x (D.connection (E i) x v)) (hrec P hx)
    simpa only [GP, coeff, N, Gamma, map_sum, map_smul, smul_eq_mul] using hh
  have hdir {x : M} (hx : x ∈ e.baseSet)
      (P : (y : M) → TangentSpace (𝓡 n) y) (f : M → ℝ) :
      d P f x = ∑ k, coeff k P x * d (E k) f x := by
    have hh := congrArg (mvfderiv (𝓡 n) f x) (hrec P hx)
    simpa only [d, map_sum, map_smul, smul_eq_mul] using hh
  have hdaP {x : M} (hx : x ∈ e.baseSet)
      (P : (y : M) → TangentSpace (𝓡 n) y) (i j : Fin n) :
      d P (fun y => a y i j) x =
        -(∑ p, (GP P x p i * a x p j + GP P x p j * a x i p)) := by
    rw [hdir hx P]
    simp_rw [hda hx, hGP hx P]
    simp only [mul_neg, Finset.sum_neg_distrib, Finset.mul_sum, Finset.sum_mul,
      mul_add, Finset.sum_add_distrib]
    congr 1
    congr 1
    all_goals
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro k _
      ring
  let Tr := fun (T : ((y : M) → TangentSpace (𝓡 n) y) →
      ((y : M) → TangentSpace (𝓡 n) y) → (y : M) → TangentSpace (𝓡 n) y) y =>
    ∑ i, ∑ j, a y i j • T (E i) (E j) y
  have hTr (T : ((y : M) → TangentSpace (𝓡 n) y) →
      ((y : M) → TangentSpace (𝓡 n) y) → (y : M) → TangentSpace (𝓡 n) y)
      (hT : ∀ i j, S (T (E i) (E j))) : S (Tr T) :=
    ContMDiffOn.sum_section fun i _ => ContMDiffOn.sum_section fun j _ =>
      (ha i j).smul_section (hT i j)
  have htrace {x : M} (hx : x ∈ e.baseSet)
      (P : (y : M) → TangentSpace (𝓡 n) y)
      (T : ((y : M) → TangentSpace (𝓡 n) y) →
        ((y : M) → TangentSpace (𝓡 n) y) → (y : M) → TangentSpace (𝓡 n) y)
      (hT : ∀ i j, S (T (E i) (E j)))
      (hL : ∀ i j, T (N P (E i)) (E j) x = ∑ p, GP P x i p • T (E p) (E j) x)
      (hR : ∀ i j, T (E i) (N P (E j)) x = ∑ p, GP P x j p • T (E i) (E p) x) :
      N P (Tr T) x = ∑ i, ∑ j, a x i j •
        (N P (T (E i) (E j)) x - T (N P (E i)) (E j) x - T (E i) (N P (E j)) x) := by
    have hd : N P (Tr T) x = ∑ i, ∑ j,
        (a x i j • N P (T (E i) (E j)) x +
          d P (fun y => a y i j) x • T (E i) (E j) x) := by
      dsimp only [N, Tr]
      rw [hnsum hx (fun i y => ∑ j, a y i j • T (E i) (E j) y)
        (fun i => ContMDiffOn.sum_section fun j _ => (ha i j).smul_section (hT i j)) (P x)]
      apply Finset.sum_congr rfl
      intro i _
      rw [hnsum hx (fun j y => a y i j • T (E i) (E j) y)
        (fun j => (ha i j).smul_section (hT i j)) (P x)]
      apply Finset.sum_congr rfl
      intro j _
      simpa only [d, Pi.smul_def', add_apply, smul_apply,
        ContinuousLinearMap.smulRight_apply] using
        congrArg (fun L => L (P x)) (hc.leibniz (hmd _ (hT i j) hx) (hcmd _ (ha i j) hx))
    have hneg : (∑ i, ∑ j, d P (fun y => a y i j) x • T (E i) (E j) x) =
        -((∑ i, ∑ j, a x i j • T (N P (E i)) (E j) x) +
          ∑ i, ∑ j, a x i j • T (E i) (N P (E j)) x) := by
      simp_rw [hdaP hx P, hL, hR]
      simp only [neg_smul, Finset.sum_neg_distrib, Finset.sum_smul, add_smul,
        Finset.smul_sum, Finset.sum_add_distrib, mul_smul]
      congr 1
      congr 1
      · calc
          _ = ∑ j, ∑ i, ∑ p, GP P x p i • a x p j • T (E i) (E j) x :=
            Finset.sum_comm
          _ = ∑ j, ∑ p, ∑ i, GP P x p i • a x p j • T (E i) (E j) x := by
            apply Finset.sum_congr rfl
            intro j _
            exact Finset.sum_comm
          _ = ∑ p, ∑ j, ∑ i, GP P x p i • a x p j • T (E i) (E j) x :=
            Finset.sum_comm
          _ = _ := by
            apply Finset.sum_congr rfl
            intro p _
            apply Finset.sum_congr rfl
            intro j _
            apply Finset.sum_congr rfl
            intro i _
            exact smul_comm _ _ _
      · apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro p _
        apply Finset.sum_congr rfl
        intro j _
        exact smul_comm _ _ _
    rw [hd]
    simp only [Finset.sum_add_distrib]
    rw [hneg]
    simp only [smul_sub, Finset.sum_sub_distrib]
    module
  let Z := fun (A B C X Y : (y : M) → TangentSpace (𝓡 n) y) y =>
    R (R A B X) Y C y - (2 : ℝ) • R B X (R Y A C) y +
      (2 : ℝ) • R X A (R B Y C) y + R (R A B C) X Y y -
      R (R A X Y) B C y - R A (R B X Y) C y - R A B (R C X Y) y
  let DZ := fun (P A B C X Y : (y : M) → TangentSpace (𝓡 n) y) y =>
    K P (R A B X) Y C y + R (K P A B X) Y C y -
      (2 : ℝ) • K P B X (R Y A C) y - (2 : ℝ) • R B X (K P Y A C) y +
      (2 : ℝ) • K P X A (R B Y C) y + (2 : ℝ) • R X A (K P B Y C) y +
      K P (R A B C) X Y y + R (K P A B C) X Y y -
      K P (R A X Y) B C y - R (K P A X Y) B C y -
      K P A (R B X Y) C y - R A (K P B X Y) C y -
      K P A B (R C X Y) y - R A B (K P C X Y) y
  have hZ (A B C X Y : (y : M) → TangentSpace (𝓡 n) y)
      (hA : S A) (hB : S B) (hC : S C) (hX : S X) (hY : S Y) : S (Z A B C X Y) :=
    ((((((hR _ Y C (hR A B X hA hB hX) hY hC).sub_section
      ((hR B X _ hB hX (hR Y A C hY hA hC)).const_smul_section (a := (2 : ℝ)))).add_section
      ((hR X A _ hX hA (hR B Y C hB hY hC)).const_smul_section (a := (2 : ℝ)))).add_section
      (hR _ X Y (hR A B C hA hB hC) hX hY)).sub_section
      (hR _ B C (hR A X Y hA hX hY) hB hC)).sub_section
      (hR A _ C hA (hR B X Y hB hX hY) hC)).sub_section
      (hR A B _ hA hB (hR C X Y hC hX hY))
  choose T0 hT0 using fun y : M => exists_curvature_trilinearMap D y
  have hReval (A B C : (y : M) → TangentSpace (𝓡 n) y)
      (hA : S A) (hB : S B) (hC : S C) {y : M} (hy : y ∈ e.baseSet) :
      R A B C y = T0 y (A y) (B y) (C y) :=
    ((hT0 y (A y) (B y) (C y)).trans
      (curvature_eq_curvatureOnFields D e.open_baseSet A B C hA hB hC hy)).symm
  have hZbilin {x : M} (hx : x ∈ e.baseSet)
      (A B C : (y : M) → TangentSpace (𝓡 n) y) (hA : S A) (hB : S B) (hC : S C) :
      ∃ L : TangentSpace (𝓡 n) x →ₗ[ℝ]
          TangentSpace (𝓡 n) x →ₗ[ℝ] TangentSpace (𝓡 n) x,
        ∀ X Y : (y : M) → TangentSpace (𝓡 n) y, S X → S Y →
          Z A B C X Y x = L (X x) (Y x) := by
    let f := fun (v w : TangentSpace (𝓡 n) x) =>
      T0 x (T0 x (A x) (B x) v) w (C x) -
        (2 : ℝ) • T0 x (B x) v (T0 x w (A x) (C x)) +
        (2 : ℝ) • T0 x v (A x) (T0 x (B x) w (C x)) +
        T0 x (T0 x (A x) (B x) (C x)) v w -
        T0 x (T0 x (A x) v w) (B x) (C x) -
        T0 x (A x) (T0 x (B x) v w) (C x) - T0 x (A x) (B x) (T0 x (C x) v w)
    let L := LinearMap.mk₂ ℝ f
      (by
        intro v v' w
        simp only [f, map_add, LinearMap.add_apply, smul_add]
        module)
      (by
        intro c v w
        simp only [f, map_smul, LinearMap.smul_apply, smul_sub, smul_add, smul_smul]
        module)
      (by
        intro v w w'
        simp only [f, map_add, LinearMap.add_apply, smul_add]
        module)
      (by
        intro c v w
        simp only [f, map_smul, LinearMap.smul_apply, smul_sub, smul_add, smul_smul]
        module)
    refine ⟨L, ?_⟩
    intro X Y hX hY
    change Z A B C X Y x = f (X x) (Y x)
    dsimp only [Z, f]
    simp (disch := solve_by_elim (maxDepth := 12) only [hA, hB, hC, hX, hY, hR, hx]) only [hReval]
  let LH := fun (A B C : (y : M) → TangentSpace (𝓡 n) y) =>
    Tr (fun X Y => H X Y A B C)
  let LZ := fun (A B C : (y : M) → TangentSpace (𝓡 n) y) =>
    Tr (fun X Y => Z A B C X Y)
  have hLH (A B C : (y : M) → TangentSpace (𝓡 n) y)
      (hA : S A) (hB : S B) (hC : S C) : S (LH A B C) :=
    hTr (fun X Y => H X Y A B C)
      (fun i j => hH (E i) (E j) A B C (hE i) (hE j) hA hB hC)
  have hLZ (A B C : (y : M) → TangentSpace (𝓡 n) y)
      (hA : S A) (hB : S B) (hC : S C) : S (LZ A B C) :=
    hTr (fun X Y => Z A B C X Y)
      (fun i j => hZ A B C (E i) (E j) hA hB hC (hE i) (hE j))
  have hsumSub3 {x : M} (u v w z : Fin n → Fin n → TangentSpace (𝓡 n) x) :
      (∑ i, ∑ j, a x i j • u i j) - (∑ i, ∑ j, a x i j • v i j) -
        (∑ i, ∑ j, a x i j • w i j) - (∑ i, ∑ j, a x i j • z i j) =
        ∑ i, ∑ j, a x i j • (u i j - v i j - w i j - z i j) := by
    simp only [smul_sub, Finset.sum_sub_distrib]
  have hsumSub {x : M} (u v : Fin n → Fin n → TangentSpace (𝓡 n) x) :
      (∑ i, ∑ j, a x i j • u i j) - (∑ i, ∑ j, a x i j • v i j) =
        ∑ i, ∑ j, a x i j • (u i j - v i j) := by
    simp only [smul_sub, Finset.sum_sub_distrib]
  have hsumAdd {x : M} (u v : Fin n → Fin n → TangentSpace (𝓡 n) x) :
      (∑ i, ∑ j, a x i j • (u i j + v i j)) =
        (∑ i, ∑ j, a x i j • u i j) + (∑ i, ∑ j, a x i j • v i j) := by
    simp only [smul_add, Finset.sum_add_distrib]
  have hDH {x : M} (hx : x ∈ e.baseSet)
      (P A B C : (y : M) → TangentSpace (𝓡 n) y)
      (hP : S P) (hA : S A) (hB : S B) (hC : S C) :
      N P (LH A B C) x - LH (N P A) B C x - LH A (N P B) C x - LH A B (N P C) x =
        Tr (fun X Y => J P X Y A B C) x := by
    have hleft (i j : Fin n) : H (N P (E i)) (E j) A B C x =
        ∑ p, GP P x i p • H (E p) (E j) A B C x :=
      hHP hx (N P (E i)) (E j) A B C (hN P (E i) hP (hE i)) (hE j) hA hB hC
    have hright (i j : Fin n) : H (E i) (N P (E j)) A B C x =
        ∑ p, GP P x j p • H (E i) (E p) A B C x :=
      hHQ hx (E i) (N P (E j)) A B C (hE i) (hN P (E j) hP (hE j)) hA hB hC
    have hh := htrace hx P (fun X Y => H X Y A B C)
      (fun i j => hH (E i) (E j) A B C (hE i) (hE j) hA hB hC) hleft hright
    change N P (LH A B C) x = _ at hh
    calc
      _ = ∑ i, ∑ j, a x i j •
          (N P (H (E i) (E j) A B C) x - H (N P (E i)) (E j) A B C x -
            H (E i) (N P (E j)) A B C x - H (E i) (E j) (N P A) B C x -
            H (E i) (E j) A (N P B) C x - H (E i) (E j) A B (N P C) x) := by
        rw [hh]
        exact hsumSub3
          (fun i j => N P (H (E i) (E j) A B C) x - H (N P (E i)) (E j) A B C x -
            H (E i) (N P (E j)) A B C x)
          (fun i j => H (E i) (E j) (N P A) B C x)
          (fun i j => H (E i) (E j) A (N P B) C x)
          (fun i j => H (E i) (E j) A B (N P C) x)
      _ = _ := rfl
  have hDZ {x : M} (hx : x ∈ e.baseSet)
      (P A B C : (y : M) → TangentSpace (𝓡 n) y)
      (hP : S P) (hA : S A) (hB : S B) (hC : S C) :
      N P (LZ A B C) x - LZ (N P A) B C x - LZ A (N P B) C x - LZ A B (N P C) x =
        Tr (fun X Y => DZ P A B C X Y) x := by
    obtain ⟨L, hL⟩ := hZbilin hx A B C hA hB hC
    have hleft (i j : Fin n) :
        Z A B C (N P (E i)) (E j) x = ∑ p, GP P x i p • Z A B C (E p) (E j) x := by
      rw [hL _ _ (hN _ _ hP (hE i)) (hE j)]
      change (L.flip (E j x)) (N P (E i) x) = _
      rw [hlin hx]
      apply Finset.sum_congr rfl
      intro p _
      rw [hL _ _ (hE p) (hE j)]
      rfl
    have hright (i j : Fin n) :
        Z A B C (E i) (N P (E j)) x = ∑ p, GP P x j p • Z A B C (E i) (E p) x := by
      rw [hL _ _ (hE i) (hN _ _ hP (hE j)), hlin hx]
      apply Finset.sum_congr rfl
      intro p _
      rw [hL _ _ (hE i) (hE p)]
    have hh := htrace hx P (fun X Y => Z A B C X Y)
      (fun i j => hZ A B C _ _ hA hB hC (hE i) (hE j)) hleft hright
    change N P (LZ A B C) x = _ at hh
    calc
      _ = ∑ i, ∑ j, a x i j •
          (N P (Z A B C (E i) (E j)) x - Z A B C (N P (E i)) (E j) x -
            Z A B C (E i) (N P (E j)) x - Z (N P A) B C (E i) (E j) x -
            Z A (N P B) C (E i) (E j) x - Z A B (N P C) (E i) (E j) x) := by
        rw [hh]
        exact hsumSub3
          (fun i j => N P (Z A B C (E i) (E j)) x - Z A B C (N P (E i)) (E j) x -
            Z A B C (E i) (N P (E j)) x)
          (fun i j => Z (N P A) B C (E i) (E j) x)
          (fun i j => Z A (N P B) C (E i) (E j) x)
          (fun i j => Z A B (N P C) (E i) (E j) x)
      _ = _ := by
        dsimp only [Tr]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        congr 1
        have hr := curvatureOnFields_reaction_covariant_derivative D e.open_baseSet
          P A B C (E i) (E j) hP hA hB hC (hE i) (hE j) hx
        change N P (Z A B C (E i) (E j)) x - Z (N P A) B C (E i) (E j) x -
          Z A (N P B) C (E i) (E j) x - Z A B (N P C) (E i) (E j) x -
          Z A B C (N P (E i)) (E j) x - Z A B C (E i) (N P (E j)) x =
          DZ P A B C (E i) (E j) x at hr
        have hperm (v a b c d e : TangentSpace (𝓡 n) x) :
            v - d - e - a - b - c = v - a - b - c - d - e := by module
        exact (hperm _ _ _ _ _ _).trans hr
  let Nt := fun s (P Q : (y : M) → TangentSpace (𝓡 n) y) y =>
    (F.connection s).connection Q y (P y)
  let Rt := fun s (A B C : (y : M) → TangentSpace (𝓡 n) y) y =>
    (F.connection s).curvatureOnFields A B C y
  let Kt := fun s (P A B C : (y : M) → TangentSpace (𝓡 n) y) y =>
    Nt s P (Rt s A B C) y - Rt s (Nt s P A) B C y -
      Rt s A (Nt s P B) C y - Rt s A B (Nt s P C) y
  let dotR := fun (A B C : (y : M) → TangentSpace (𝓡 n) y) y =>
    deriv (fun s => Rt s A B C y) t
  let Btime := fun (P Q : (y : M) → TangentSpace (𝓡 n) y) y =>
    deriv (fun s => Nt s P Q y) t
  have hrate (A B C : (y : M) → TangentSpace (𝓡 n) y)
      (hA : S A) (hB : S B) (hC : S C) {x : M} (hx : x ∈ e.baseSet) :
      dotR A B C x = LH A B C x + LZ A B C x := by
    let bn := g.orthonormalBasis x
    let ext := fun v : TangentSpace (𝓡 n) x => FiberBundle.extend V v
    let Rp := D.curvature x
    let Ps := fun v : TangentSpace (𝓡 n) x => ∑ r, D.ricci x v (bn r) • bn r
    let Q := (∑ r, (Rp (Rp (A x) (B x) (bn r)) (bn r) (C x) -
        (2 : ℝ) • Rp (B x) (bn r) (Rp (bn r) (A x) (C x)) +
        (2 : ℝ) • Rp (bn r) (A x) (Rp (B x) (bn r) (C x)))) +
      Ps (Rp (A x) (B x) (C x)) - Rp (Ps (A x)) (B x) (C x) -
      Rp (A x) (Ps (B x)) (C x) - Rp (A x) (B x) (Ps (C x))
    have hHess : (∑ r, H (ext (bn r)) (ext (bn r))
        (ext (A x)) (ext (B x)) (ext (C x)) x) = LH A B C x :=
      curvature_hessian_trace_localFrame D x0 hx A B C hA hB hC
    have hQ : Q = LZ A B C x := by
      have hh := curvature_reaction_eq_pure_inverse_frame_sum D x0 x hx (A x) (B x) (C x)
      change Q = _ at hh
      rw [hh]
      dsimp only [LZ, Tr]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      congr 1
      dsimp only [Z]
      simp (disch := solve_by_elim (maxDepth := 12) only
        [hA, hB, hC, hE, hR, hx]) only [hReval]
      simp only [hT0, E, e, b, V]
    have hd := hasDerivAt_ricciFlow_curvature_diffusion_reaction F ht x (A x) (B x) (C x)
    change HasDerivAt (fun s => (F.connection s).curvature x (A x) (B x) (C x))
      ((∑ r, H (ext (bn r)) (ext (bn r))
        (ext (A x)) (ext (B x)) (ext (C x)) x) + Q) t at hd
    rw [hHess, hQ] at hd
    have hd' : HasDerivAt (fun s => Rt s A B C x)
        (LH A B C x + LZ A B C x) t :=
      hd.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun s =>
        (curvature_eq_curvatureOnFields (F.connection s) e.open_baseSet A B C hA hB hC hx).symm))
    exact hd'.deriv
  have hdotR (A B C : (y : M) → TangentSpace (𝓡 n) y)
      (hA : S A) (hB : S B) (hC : S C) : S (dotR A B C) := by
    apply ((hLH A B C hA hB hC).add_section (hLZ A B C hA hB hC)).congr
    intro y hy
    congr 1
    exact hrate A B C hA hB hC hy
  have hNdot {x : M} (hx : x ∈ e.baseSet)
      (P A B C : (y : M) → TangentSpace (𝓡 n) y)
      (hA : S A) (hB : S B) (hC : S C) :
      N P (dotR A B C) x = N P (LH A B C) x + N P (LZ A B C) x := by
    have hs := (hLH A B C hA hB hC).add_section (hLZ A B C hA hB hC)
    have hloc := hc.congr_of_eventuallyEq (hmd _ (hdotR A B C hA hB hC) hx)
      (hmd _ hs hx) Filter.univ_mem
      (Filter.eventuallyEq_of_mem (e.open_baseSet.mem_nhds hx)
        (fun y hy => hrate A B C hA hB hC hy))
    calc
      _ = D.connection (LH A B C + LZ A B C) x (P x) :=
        congrArg (fun L => L (P x)) hloc
      _ = _ := by
        simpa only [add_apply] using congrArg (fun L => L (P x))
          (hc.add (hmd _ (hLH A B C hA hB hC) hx) (hmd _ (hLZ A B C hA hB hC) hx))
  have hnabla {x : M} (hx : x ∈ e.baseSet)
      (P A B C : (y : M) → TangentSpace (𝓡 n) y)
      (hP : S P) (hA : S A) (hB : S B) (hC : S C) :
      N P (dotR A B C) x - dotR (N P A) B C x -
        dotR A (N P B) C x - dotR A B (N P C) x =
        Tr (fun X Y => J P X Y A B C) x + Tr (fun X Y => DZ P A B C X Y) x := by
    rw [hNdot hx P A B C hA hB hC,
      hrate _ B C (hN P A hP hA) hB hC hx,
      hrate A _ C hA (hN P B hP hB) hC hx,
      hrate A B _ hA hB (hN P C hP hC) hx]
    have hadd (u v a b c d e f : TangentSpace (𝓡 n) x) :
        (u + v) - (a + b) - (c + d) - (e + f) =
          (u - a - c - e) + (v - b - d - f) := by module
    exact (hadd (N P (LH A B C) x) (N P (LZ A B C) x)
      (LH (N P A) B C x) (LZ (N P A) B C x)
      (LH A (N P B) C x) (LZ A (N P B) C x)
      (LH A B (N P C) x) (LZ A B (N P C) x)).trans
        (congrArg₂ (· + ·) (hDH hx P A B C hP hA hB hC) (hDZ hx P A B C hP hA hB hC))
  let Co := fun (P X Y A B C : (y : M) → TangentSpace (𝓡 n) y) y =>
    R P X (K Y A B C) y - K (R P X Y) A B C y -
      K Y (R P X A) B C y - K Y A (R P X B) C y - K Y A B (R P X C) y +
      K X P Y (R A B C) y + R P Y (K X A B C) y -
      K X (R P Y A) B C y - R (K X P Y A) B C y -
      K X A (R P Y B) C y - R A (K X P Y B) C y -
      K X A B (R P Y C) y - R A B (K X P Y C) y
  have hCo {x : M} (hx : x ∈ e.baseSet)
      (P X Y A B C : (y : M) → TangentSpace (𝓡 n) y)
      (hP : S P) (hX : S X) (hY : S Y) (hA : S A) (hB : S B) (hC : S C) :
      J P X Y A B C x - J X Y P A B C x = Co P X Y A B C x := by
    have ho := curvatureOnFields_third_derivative_commutator D e.open_baseSet
      P X Y A B C hP hX hY hA hB hC hx
    have hi := curvatureOnFields_third_derivative_inner_commutator D e.open_baseSet
      X P Y A B C hX hP hY hA hB hC hx
    change J P X Y A B C x - J X P Y A B C x =
      R P X (K Y A B C) x - K (R P X Y) A B C x -
        K Y (R P X A) B C x - K Y A (R P X B) C x - K Y A B (R P X C) x at ho
    change J X P Y A B C x - J X Y P A B C x =
      K X P Y (R A B C) x + R P Y (K X A B C) x -
        K X (R P Y A) B C x - R (K X P Y A) B C x -
        K X A (R P Y B) C x - R A (K X P Y B) C x -
        K X A B (R P Y C) x - R A B (K X P Y C) x at hi
    rw [← sub_add_sub_cancel (J P X Y A B C x) (J X P Y A B C x)
      (J X Y P A B C x), ho, hi]
    have hadd (a b c d e f g h i j k l m : TangentSpace (𝓡 n) x) :
        (a - b - c - d - e) + (f + g - h - i - j - k - l - m) =
          a - b - c - d - e + f + g - h - i - j - k - l - m := by module
    exact hadd _ _ _ _ _ _ _ _ _ _ _ _ _
  have hPDE {x : M} (hx : x ∈ e.baseSet)
      (P A B C : (y : M) → TangentSpace (𝓡 n) y)
      (hP : S P) (hA : S A) (hB : S B) (hC : S C) :
      deriv (fun s => Kt s P A B C x) t - Tr (fun X Y => J X Y P A B C) x =
        Tr (fun X Y => Co P X Y A B C + DZ P A B C X Y) x +
          Btime P (R A B C) x - R (Btime P A) B C x -
          R A (Btime P B) C x - R A B (Btime P C) x := by
    have htime := (hasDerivAt_ricciFlow_curvature_derivative F ht e.open_baseSet
      P A B C hP hA hB hC hx).deriv
    change deriv (fun s => Kt s P A B C x) t =
      (N P (dotR A B C) x - dotR (N P A) B C x -
        dotR A (N P B) C x - dotR A B (N P C) x) +
      Btime P (R A B C) x - R (Btime P A) B C x -
      R A (Btime P B) C x - R A B (Btime P C) x at htime
    rw [hnabla hx P A B C hP hA hB hC] at htime
    have hcomm : Tr (fun X Y => J P X Y A B C) x -
        Tr (fun X Y => J X Y P A B C) x = Tr (fun X Y => Co P X Y A B C) x := by
      calc
        _ = ∑ i, ∑ j, a x i j •
            (J P (E i) (E j) A B C x - J (E i) (E j) P A B C x) := by
          exact hsumSub (fun i j => J P (E i) (E j) A B C x)
            (fun i j => J (E i) (E j) P A B C x)
        _ = _ := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          rw [hCo hx P (E i) (E j) A B C hP (hE i) (hE j) hA hB hC]
    have hadd : Tr (fun X Y => Co P X Y A B C + DZ P A B C X Y) x =
        Tr (fun X Y => Co P X Y A B C) x + Tr (fun X Y => DZ P A B C X Y) x :=
      hsumAdd (fun i j => Co P (E i) (E j) A B C x)
        (fun i j => DZ P A B C (E i) (E j) x)
    have hcancel (u v w c d e f g : TangentSpace (𝓡 n) x) (heq : u - v = w) :
        (u + c + d - e - f - g) - v = w + c + d - e - f - g := by
      linear_combination (norm := module) heq
    rw [htime, hadd]
    exact hcancel _ _ _ _ _ _ _ _ hcomm
  exact @hPDE

end PoincareConjecture.Proofs.M03
