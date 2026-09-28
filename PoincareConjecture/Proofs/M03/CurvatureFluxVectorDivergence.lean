import PoincareConjecture.Proofs.M03.CurvatureFrameCoordinate
import PoincareConjecture.Proofs.M03.CurvatureConnectionDifference
import PoincareConjecture.Proofs.M03.CurvatureDerivativeTensoriality
import PoincareConjecture.Proofs.M03.MetricInverse

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle Manifold Set

universe u

namespace PoincareConjecture.Proofs.M03

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

theorem localFrame_covariant_divergence_coordinate
    {g : RiemannianMetric n M} (D : LeviCivitaData g) (x₀ : M)
    (W : (y : M) → TangentSpace (𝓡 n) y) :
    let V := EuclideanSpace ℝ (Fin n)
    let e := trivializationAt V (TangentSpace (𝓡 n)) x₀
    let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    let E := e.localFrame b
    let theta := fun (i : Fin n) (y : M) =>
      e.localFrameCoeff (𝓡 n) b i y
    ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% W) e.baseSet →
    ∀ {x : M} (hx : x ∈ e.baseSet) (l : Fin n),
      (∑ i, theta l x (D.connection W x (E i x))) =
        ∑ i, (mvfderiv (𝓡 n) (fun y => theta l y (W y)) x (E i x) +
          ∑ p, theta l x (D.connection (E p) x (E i x)) *
            theta p x (W x)) := by
  dsimp only
  intro hW x hx l
  apply Finset.sum_congr rfl
  intro i hi
  exact localFrame_covariant_derivative_coordinate D x₀ W hW hx i l

theorem curvature_difference_flux_divergence_coordinates
    {g g' : RiemannianMetric n M}
    (D : LeviCivitaData g) (D' : LeviCivitaData g') (x0 : M) :
    let V := EuclideanSpace ℝ (Fin n)
    let c := chartAt V x0
    let e := trivializationAt V (TangentSpace (𝓡 n)) x0
    let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    let E := e.localFrame b
    let theta := fun (i : Fin n) (y : M) =>
      e.localFrameCoeff (𝓡 n) b i y
    let N := fun
        (P Q : (y : M) → TangentSpace (𝓡 n) y) (y : M) =>
      D.connection Q y (P y)
    let N' := fun
        (P Q : (y : M) → TangentSpace (𝓡 n) y) (y : M) =>
      D'.connection Q y (P y)
    let R' := fun
        (A B C : (y : M) → TangentSpace (𝓡 n) y) (y : M) =>
      D'.curvatureOnFields A B C y
    let K := fun
        (P A B C : (y : M) → TangentSpace (𝓡 n) y) (y : M) =>
      N P (R' A B C) y - R' (N P A) B C y -
        R' A (N P B) C y - R' A B (N P C) y
    let K' := fun
        (P A B C : (y : M) → TangentSpace (𝓡 n) y) (y : M) =>
      N' P (R' A B C) y - R' (N' P A) B C y -
        R' A (N' P B) C y - R' A B (N' P C) y
    let G := fun (h : RiemannianMetric n M) (y : M) =>
      ContinuousLinearMap.inCoordinates V (TangentSpace (𝓡 n))
        (V →L[ℝ] ℝ) (fun z => TangentSpace (𝓡 n) z →L[ℝ] ℝ)
        x0 y x0 y (h.inner y)
    let a := fun (y : M) (i j : Fin n) =>
      (ContinuousLinearMap.inverse (G g y) (EuclideanSpace.proj j)) i
    let a' := fun (y : M) (i j : Fin n) =>
      (ContinuousLinearMap.inverse (G g' y) (EuclideanSpace.proj j)) i
    let Uflux := fun (i : Fin n)
        (A B C : (y : M) → TangentSpace (𝓡 n) y) (y : M) =>
      ∑ j, (a y i j • K (E j) A B C y -
        a' y i j • K' (E j) A B C y)
    let Gamma := fun (y : M) (i j l : Fin n) =>
      theta l y (N (E i) (E j) y)
    let Div := fun
        (A B C : (y : M) → TangentSpace (𝓡 n) y) (y : M) =>
      ∑ i, (N (E i) (Uflux i A B C) y -
        Uflux i (N (E i) A) B C y -
        Uflux i A (N (E i) B) C y -
        Uflux i A B (N (E i) C) y +
        ∑ p, Gamma y i p i • Uflux p A B C y)
    let uFlux := fun (z : V) (i l j k m : Fin n) =>
      theta l (c.symm z)
        (Uflux i (E j) (E k) (E m) (c.symm z))
    ∀ z ∈ c.target, ∀ l j k m : Fin n,
      let x := c.symm z
      theta l x (Div (E j) (E k) (E m) x) =
        ∑ i, (fderiv ℝ (fun w => uFlux w i l j k m)
            z (EuclideanSpace.single i 1) +
          ∑ p,
            (Gamma x i p i * uFlux z p l j k m +
            Gamma x i p l * uFlux z i p j k m -
            Gamma x i j p * uFlux z i l p k m -
            Gamma x i k p * uFlux z i l j p m -
            Gamma x i m p * uFlux z i l j k p)) := by
  classical
  dsimp only
  let V := EuclideanSpace ℝ (Fin n)
  let c := chartAt V x0
  let e := trivializationAt V (TangentSpace (𝓡 n)) x0
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let E := e.localFrame b
  let theta := e.localFrameCoeff (𝓡 n) b
  let N := fun (P Q : (y : M) → TangentSpace (𝓡 n) y) (y : M) =>
    D.connection Q y (P y)
  let N' := fun (P Q : (y : M) → TangentSpace (𝓡 n) y) (y : M) =>
    D'.connection Q y (P y)
  let R' := fun (A B C : (y : M) → TangentSpace (𝓡 n) y) (y : M) =>
    D'.curvatureOnFields A B C y
  let K := fun (P A B C : (y : M) → TangentSpace (𝓡 n) y) (y : M) =>
    N P (R' A B C) y - R' (N P A) B C y -
      R' A (N P B) C y - R' A B (N P C) y
  let K' := fun (P A B C : (y : M) → TangentSpace (𝓡 n) y) (y : M) =>
    N' P (R' A B C) y - R' (N' P A) B C y -
      R' A (N' P B) C y - R' A B (N' P C) y
  let G := fun (h : RiemannianMetric n M) (y : M) =>
    ContinuousLinearMap.inCoordinates V (TangentSpace (𝓡 n))
      (V →L[ℝ] ℝ) (fun z => TangentSpace (𝓡 n) z →L[ℝ] ℝ)
      x0 y x0 y (h.inner y)
  let a := fun (y : M) (i j : Fin n) =>
    (ContinuousLinearMap.inverse (G g y) (EuclideanSpace.proj j)) i
  let a' := fun (y : M) (i j : Fin n) =>
    (ContinuousLinearMap.inverse (G g' y) (EuclideanSpace.proj j)) i
  let Uflux := fun (i : Fin n)
      (A B C : (y : M) → TangentSpace (𝓡 n) y) (y : M) =>
    ∑ j, (a y i j • K (E j) A B C y -
      a' y i j • K' (E j) A B C y)
  let Gamma := fun (y : M) (i j l : Fin n) => theta l y (N (E i) (E j) y)
  let uFlux := fun (z : V) (i l j k m : Fin n) =>
    theta l (c.symm z) (Uflux i (E j) (E k) (E m) (c.symm z))
  let S := fun W : (y : M) → TangentSpace (𝓡 n) y =>
    ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% W) e.baseSet
  have hE (i : Fin n) : S (E i) :=
    e.contMDiffOn_localFrame_baseSet (I := 𝓡 n) ∞ b i
  have hN (P Q : (y : M) → TangentSpace (𝓡 n) y)
      (hP : S P) (hQ : S Q) : S (N P Q) :=
    D.contMDiffOn_connection_apply e.open_baseSet P Q hP hQ
  have hN' (P Q : (y : M) → TangentSpace (𝓡 n) y)
      (hP : S P) (hQ : S Q) : S (N' P Q) :=
    D'.contMDiffOn_connection_apply e.open_baseSet P Q hP hQ
  letI : IsManifold (𝓡 n) (∞ + 1) M := by
    simpa using (inferInstance : IsManifold (𝓡 n) ∞ M)
  letI : IsManifold (𝓡 n) (minSmoothness ℝ 2) M :=
    IsManifold.of_le (n := ∞) (by
      simpa only [minSmoothness_of_isRCLikeNormedField] using
        (ENat.LEInfty.out (m := (2 : ℕ∞ω))))
  have hR (A B C : (y : M) → TangentSpace (𝓡 n) y)
      (hA : S A) (hB : S B) (hC : S C) : S (R' A B C) := by
    have hbr : S (VectorField.mlieBracket (𝓡 n) A B) := by
      intro y hy
      exact ((hA.contMDiffAt (e.open_baseSet.mem_nhds hy)).mlieBracket_vectorField
        (hB.contMDiffAt (e.open_baseSet.mem_nhds hy)) (m := ⊤) (n := ⊤)
        (by simp)).contMDiffWithinAt
    exact ((hN' A _ hA (hN' B C hB hC)).sub_section
      (hN' B _ hB (hN' A C hA hC))).sub_section (hN' _ C hbr hC)
  have hK (P A B C : (y : M) → TangentSpace (𝓡 n) y)
      (hP : S P) (hA : S A) (hB : S B) (hC : S C) : S (K P A B C) :=
    (((hN P _ hP (hR A B C hA hB hC)).sub_section
      (hR _ B C (hN P A hP hA) hB hC)).sub_section
      (hR A _ C hA (hN P B hP hB) hC)).sub_section
      (hR A B _ hA hB (hN P C hP hC))
  have hK' (P A B C : (y : M) → TangentSpace (𝓡 n) y)
      (hP : S P) (hA : S A) (hB : S B) (hC : S C) : S (K' P A B C) :=
    (((hN' P _ hP (hR A B C hA hB hC)).sub_section
      (hR _ B C (hN' P A hP hA) hB hC)).sub_section
      (hR A _ C hA (hN' P B hP hB) hC)).sub_section
      (hR A B _ hA hB (hN' P C hP hC))
  have hainv (h : RiemannianMetric n M) (i j : Fin n) :
      ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞
        (fun y => (ContinuousLinearMap.inverse (G h y) (EuclideanSpace.proj j)) i)
        e.baseSet := by
    have hh : RiemannianMetric.IsSmoothFamilyOn (fun _ : ℝ => h) Set.univ :=
      (h.contMDiff.comp contMDiff_snd).contMDiffOn
    have hi := (contMDiffOn_family_metric_frame_inverse hh x0).2.2
    have hs := hi.comp
      (show ContMDiffOn (𝓡 n) (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
        (fun y : M => ((0 : ℝ), y)) e.baseSet from
        contMDiffOn_const.prodMk contMDiffOn_id)
      (fun y hy => ⟨Set.mem_univ (0 : ℝ), hy⟩)
    have hv := hs.clm_apply (contMDiffOn_const (c := EuclideanSpace.proj j))
    exact ((contMDiffOn_const (c := EuclideanSpace.proj i)).clm_apply hv)
  have hU (i : Fin n) (A B C : (y : M) → TangentSpace (𝓡 n) y)
      (hA : S A) (hB : S B) (hC : S C) : S (Uflux i A B C) := by
    apply ContMDiffOn.sum_section
    intro j _
    exact ((hainv g i j).smul_section (hK (E j) A B C (hE j) hA hB hC)).sub_section
      ((hainv g' i j).smul_section (hK' (E j) A B C (hE j) hA hB hC))
  intro z hz l j k m
  let x := c.symm z
  have hx : x ∈ e.baseSet := by
    simpa only [e, TangentBundle.trivializationAt_baseSet] using c.map_target hz
  have hcx : c x = z := c.right_inv hz
  have hrec (W : (y : M) → TangentSpace (𝓡 n) y) :
      W x = ∑ p, theta p x (W x) • E p x :=
    e.eq_sum_localFrameCoeff_smul (I := 𝓡 n) (b := b) hx
  have hFrame (i : Fin n) : E i x = e.symmL ℝ x (EuclideanSpace.single i 1) := by
    calc
      E i x = e.basisAt b hx i := e.localFrame_apply_of_mem_baseSet b hx
      _ = e.symm x (EuclideanSpace.single i 1) := by
        simp only [Trivialization.basisAt, Module.Basis.map_apply, b,
          OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
          Trivialization.linearEquivAt_symm_apply]
      _ = e.symmL ℝ x (EuclideanSpace.single i 1) := (e.symmL_apply hx _).symm

  obtain ⟨TR, hTR⟩ := exists_curvature_trilinearMap D' x
  obtain ⟨TK, hTK⟩ := exists_curvatureOnFields_derivative_quadrilinearMap D' x
  let Cdiff := CovariantDerivative.difference D.connection D'.connection x
  let L (p : TangentSpace (𝓡 n) x) :
      TangentSpace (𝓡 n) x →ₗ[ℝ] TangentSpace (𝓡 n) x := {
    toFun := fun v => Cdiff v p
    map_add' := fun v w => by simp only [map_add, ContinuousLinearMap.add_apply]
    map_smul' := fun r v => by
      simp only [map_smul, ContinuousLinearMap.smul_apply, RingHom.id_apply] }
  let T (p : TangentSpace (𝓡 n) x) :=
    TK p + TR.compr₂ (LinearMap.llcomp ℝ _ _ _ (L p)) -
      TR.comp (L p) - TR.compl₂ (L p) -
      TR.compr₂ ((LinearMap.llcomp ℝ _ _ _).flip (L p))
  have hT (P A B C : (y : M) → TangentSpace (𝓡 n) y)
      (hP : S P) (hA : S A) (hB : S B) (hC : S C) :
      T (P x) (A x) (B x) (C x) = K P A B C x := by
    have hd := curvature_covariant_derivative_connection_change D D' e.open_baseSet
      P A B C hP hA hB hC hx
    change K P A B C x - K' P A B C x =
      Cdiff (D'.curvature x (A x) (B x) (C x)) (P x) -
        D'.curvature x (Cdiff (A x) (P x)) (B x) (C x) -
        D'.curvature x (A x) (Cdiff (B x) (P x)) (C x) -
        D'.curvature x (A x) (B x) (Cdiff (C x) (P x)) at hd
    have hk : TK (P x) (A x) (B x) (C x) = K' P A B C x :=
      hTK e.open_baseSet P A B C hP hA hB hC hx
    simp only [T, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.compr₂_apply,
      LinearMap.llcomp_apply, LinearMap.comp_apply, LinearMap.compl₂_apply,
      LinearMap.flip_apply, L, LinearMap.coe_mk, AddHom.coe_mk, hk, hTR]
    rw [sub_eq_iff_eq_add.mp hd]
    module
  let TU (i : Fin n) := ∑ p : Fin n,
    (a x i p • T (E p x) - a' x i p • TK (E p x))
  have hTU (i : Fin n) (A B C : (y : M) → TangentSpace (𝓡 n) y)
      (hA : S A) (hB : S B) (hC : S C) :
      Uflux i A B C x = TU i (A x) (B x) (C x) := by
    simp only [Uflux, TU, LinearMap.sum_apply, LinearMap.sub_apply, LinearMap.smul_apply]
    apply Finset.sum_congr rfl
    intro p _
    rw [hT (E p) A B C (hE p) hA hB hC,
      hTK e.open_baseSet (E p) A B C (hE p) hA hB hC hx]
  have hin1 (i : Fin n) :
      theta l x (Uflux i (N (E i) (E j)) (E k) (E m) x) =
        ∑ p, Gamma x i j p * uFlux z i l p k m := by
    rw [hTU i _ _ _ (hN _ _ (hE i) (hE j)) (hE k) (hE m), hrec (N (E i) (E j))]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro p _
    rw [← hTU i _ _ _ (hE p) (hE k) (hE m)]
  have hin2 (i : Fin n) :
      theta l x (Uflux i (E j) (N (E i) (E k)) (E m) x) =
        ∑ p, Gamma x i k p * uFlux z i l j p m := by
    rw [hTU i _ _ _ (hE j) (hN _ _ (hE i) (hE k)) (hE m), hrec (N (E i) (E k))]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro p _
    rw [← hTU i _ _ _ (hE j) (hE p) (hE m)]
  have hin3 (i : Fin n) :
      theta l x (Uflux i (E j) (E k) (N (E i) (E m)) x) =
        ∑ p, Gamma x i m p * uFlux z i l j k p := by
    rw [hTU i _ _ _ (hE j) (hE k) (hN _ _ (hE i) (hE m)), hrec (N (E i) (E m))]
    simp only [map_sum, map_smul, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro p _
    rw [← hTU i _ _ _ (hE j) (hE k) (hE p)]
  have hchart (f : M → ℝ)
      (hf : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f e.baseSet) (i : Fin n) :
      mvfderiv (𝓡 n) f x (E i x) =
        fderiv ℝ (fun w => f (c.symm w)) z (EuclideanSpace.single i 1) := by
    have hc : MDifferentiableAt 𝓘(ℝ, V) (𝓡 n) c.symm z :=
      ((contMDiffOn_chart_symm (I := 𝓡 n) (n := ∞) (x := x0)).contMDiffAt
        (c.open_target.mem_nhds hz)).mdifferentiableAt (by simp)
    have he : e.symmL ℝ x = mfderiv 𝓘(ℝ, V) (𝓡 n) c.symm z := by
      have hh := TangentBundle.symmL_trivializationAt (I := 𝓡 n) (x₀ := x0)
        (c.map_target hz)
      simp only [extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
        modelWithCornersSelf_coe_symm, Function.comp_def, id_eq, Set.range_id,
        mfderivWithin_univ] at hh
      change e.symmL ℝ x = mfderiv 𝓘(ℝ, V) (𝓡 n) c.symm (c x) at hh
      rwa [hcx] at hh
    have hfd : fderiv ℝ (fun w => f (c.symm w)) z (EuclideanSpace.single i 1) =
        mvfderiv (𝓡 n) f x (e.symmL ℝ x (EuclideanSpace.single i 1)) := by
      rw [← mfderiv_eq_fderiv]
      change mvfderiv 𝓘(ℝ, V) (f ∘ c.symm) z (EuclideanSpace.single i 1) = _
      have hff : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f (c.symm z) :=
        (hf.contMDiffAt (e.open_baseSet.mem_nhds hx)).mdifferentiableAt (by simp)
      rw [mvfderiv_comp_apply z hff hc (EuclideanSpace.single i 1), ← he]
      rfl
    exact (congrArg (mvfderiv (𝓡 n) f x) (hFrame i)).trans hfd.symm
  have hout (i : Fin n) :
      theta l x (N (E i) (Uflux i (E j) (E k) (E m)) x) =
        fderiv ℝ (fun w => uFlux w i l j k m) z (EuclideanSpace.single i 1) +
          ∑ p, Gamma x i p l * uFlux z i p j k m := by
    have hh := localFrame_covariant_derivative_coordinate D x0
      (Uflux i (E j) (E k) (E m)) (hU i _ _ _ (hE j) (hE k) (hE m)) hx i l
    change theta l x (N (E i) (Uflux i (E j) (E k) (E m)) x) =
      mvfderiv (𝓡 n)
        (fun y => theta l y (Uflux i (E j) (E k) (E m) y)) x (E i x) +
        ∑ p, Gamma x i p l * theta p x (Uflux i (E j) (E k) (E m) x) at hh
    have hcf : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞
        (fun y => theta l y (Uflux i (E j) (E k) (E m) y)) e.baseSet :=
      contMDiffOn_localFrameCoeff b e.open_baseSet subset_rfl
        (hU i _ _ _ (hE j) (hE k) (hE m)) l
    exact hh.trans (congrArg (fun r : ℝ => r +
      ∑ p, Gamma x i p l * theta p x (Uflux i (E j) (E k) (E m) x))
        (hchart _ hcf i))
  have hraised (i : Fin n) :
      theta l x (∑ p, Gamma x i p i • Uflux p (E j) (E k) (E m) x) =
        ∑ p, Gamma x i p i * uFlux z p l j k m := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro p _
    rw [map_smul]
    rfl
  change theta l x (∑ i, (N (E i) (Uflux i (E j) (E k) (E m)) x -
    Uflux i (N (E i) (E j)) (E k) (E m) x -
    Uflux i (E j) (N (E i) (E k)) (E m) x -
    Uflux i (E j) (E k) (N (E i) (E m)) x +
    ∑ p, Gamma x i p i • Uflux p (E j) (E k) (E m) x)) =
      ∑ i, (fderiv ℝ (fun w => uFlux w i l j k m) z (EuclideanSpace.single i 1) +
        ∑ p, (Gamma x i p i * uFlux z p l j k m +
          Gamma x i p l * uFlux z i p j k m -
          Gamma x i j p * uFlux z i l p k m -
          Gamma x i k p * uFlux z i l j p m -
          Gamma x i m p * uFlux z i l j k p))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_add, map_sub, map_sub, map_sub, hout i, hin1 i, hin2 i, hin3 i, hraised i]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring

theorem curvature_raised_divergence_coordinates
    {g : RiemannianMetric n M} (D : LeviCivitaData g) (x0 : M) :
    let V := EuclideanSpace ℝ (Fin n)
    let c := chartAt V x0
    let e := trivializationAt V (TangentSpace (𝓡 n)) x0
    let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    let E := e.localFrame b
    let theta := e.localFrameCoeff (𝓡 n) b
    let N := fun (P Q : (y : M) → TangentSpace (𝓡 n) y) (y : M) =>
      D.connection Q y (P y)
    let R := fun (A B C : (y : M) → TangentSpace (𝓡 n) y) (y : M) =>
      D.curvatureOnFields A B C y
    let K := fun (P A B C : (y : M) → TangentSpace (𝓡 n) y) (y : M) =>
      N P (R A B C) y - R (N P A) B C y -
        R A (N P B) C y - R A B (N P C) y
    let G := fun y : M =>
      ContinuousLinearMap.inCoordinates V (TangentSpace (𝓡 n))
        (V →L[ℝ] ℝ) (fun z => TangentSpace (𝓡 n) z →L[ℝ] ℝ)
        x0 y x0 y (g.inner y)
    let a := fun (y : M) (i d : Fin n) =>
      (ContinuousLinearMap.inverse (G y) (EuclideanSpace.proj d)) i
    let W := fun (i : Fin n) (A B C : (y : M) → TangentSpace (𝓡 n) y) (y : M) =>
      ∑ d, a y i d • K (E d) A B C y
    let Gamma := fun (y : M) (i j l : Fin n) => theta l y (N (E i) (E j) y)
    let Div := fun (A B C : (y : M) → TangentSpace (𝓡 n) y) (y : M) =>
      ∑ i, (N (E i) (W i A B C) y - W i (N (E i) A) B C y -
        W i A (N (E i) B) C y - W i A B (N (E i) C) y +
        ∑ p, Gamma y i p i • W p A B C y)
    let v := fun (z : V) (i l j k m : Fin n) =>
      theta l (c.symm z) (W i (E j) (E k) (E m) (c.symm z))
    ∀ z ∈ c.target, ∀ l j k m : Fin n,
      let x := c.symm z
      theta l x (Div (E j) (E k) (E m) x) =
        ∑ i, (fderiv ℝ (fun w => v w i l j k m) z (EuclideanSpace.single i 1) +
          ∑ p, (Gamma x i p i * v z p l j k m +
            Gamma x i p l * v z i p j k m - Gamma x i j p * v z i l p k m -
            Gamma x i k p * v z i l j p m - Gamma x i m p * v z i l j k p)) := by
  classical
  dsimp only
  let V := EuclideanSpace ℝ (Fin n)
  let c := chartAt V x0
  let e := trivializationAt V (TangentSpace (𝓡 n)) x0
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let E := e.localFrame b
  let theta := e.localFrameCoeff (𝓡 n) b
  let N := fun (P Q : (y : M) → TangentSpace (𝓡 n) y) (y : M) =>
    D.connection Q y (P y)
  let R := fun (A B C : (y : M) → TangentSpace (𝓡 n) y) (y : M) =>
    D.curvatureOnFields A B C y
  let K := fun (P A B C : (y : M) → TangentSpace (𝓡 n) y) (y : M) =>
    N P (R A B C) y - R (N P A) B C y -
      R A (N P B) C y - R A B (N P C) y
  let G := fun y : M =>
    ContinuousLinearMap.inCoordinates V (TangentSpace (𝓡 n))
      (V →L[ℝ] ℝ) (fun z => TangentSpace (𝓡 n) z →L[ℝ] ℝ)
      x0 y x0 y (g.inner y)
  let a := fun (y : M) (i d : Fin n) =>
    (ContinuousLinearMap.inverse (G y) (EuclideanSpace.proj d)) i
  let W := fun (i : Fin n) (A B C : (y : M) → TangentSpace (𝓡 n) y) (y : M) =>
    ∑ d, a y i d • K (E d) A B C y
  let Gamma := fun (y : M) (i j l : Fin n) => theta l y (N (E i) (E j) y)
  let v := fun (z : V) (i l j k m : Fin n) =>
    theta l (c.symm z) (W i (E j) (E k) (E m) (c.symm z))
  let S := fun Y : (y : M) → TangentSpace (𝓡 n) y =>
    ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% Y) e.baseSet
  have hE (i : Fin n) : S (E i) :=
    e.contMDiffOn_localFrame_baseSet (I := 𝓡 n) ∞ b i
  have hN (P Q : (y : M) → TangentSpace (𝓡 n) y)
      (hP : S P) (hQ : S Q) : S (N P Q) :=
    D.contMDiffOn_connection_apply e.open_baseSet P Q hP hQ
  letI : IsManifold (𝓡 n) (∞ + 1) M := by
    simpa using (inferInstance : IsManifold (𝓡 n) ∞ M)
  letI : IsManifold (𝓡 n) (minSmoothness ℝ 2) M :=
    IsManifold.of_le (n := ∞) (by
      simpa only [minSmoothness_of_isRCLikeNormedField] using
        (ENat.LEInfty.out (m := (2 : ℕ∞ω))))
  have hR (A B C : (y : M) → TangentSpace (𝓡 n) y)
      (hA : S A) (hB : S B) (hC : S C) : S (R A B C) := by
    have hbr : S (VectorField.mlieBracket (𝓡 n) A B) := by
      intro y hy
      exact ((hA.contMDiffAt (e.open_baseSet.mem_nhds hy)).mlieBracket_vectorField
        (hB.contMDiffAt (e.open_baseSet.mem_nhds hy)) (m := ⊤) (n := ⊤)
        (by simp)).contMDiffWithinAt
    exact ((hN A _ hA (hN B C hB hC)).sub_section
      (hN B _ hB (hN A C hA hC))).sub_section (hN _ C hbr hC)
  have hK (P A B C : (y : M) → TangentSpace (𝓡 n) y)
      (hP : S P) (hA : S A) (hB : S B) (hC : S C) : S (K P A B C) :=
    (((hN P _ hP (hR A B C hA hB hC)).sub_section
      (hR _ B C (hN P A hP hA) hB hC)).sub_section
      (hR A _ C hA (hN P B hP hB) hC)).sub_section
      (hR A B _ hA hB (hN P C hP hC))
  have hainv (i d : Fin n) : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun y => a y i d) e.baseSet := by
    have hf : RiemannianMetric.IsSmoothFamilyOn (fun _ : ℝ => g) univ :=
      (g.contMDiff.comp contMDiff_snd).contMDiffOn
    have hi := (contMDiffOn_family_metric_frame_inverse hf x0).2.2
    have hs := hi.comp
      (show ContMDiffOn (𝓡 n) (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
        (fun y : M => ((0 : ℝ), y)) e.baseSet from
        contMDiffOn_const.prodMk contMDiffOn_id)
      (fun y hy => ⟨mem_univ (0 : ℝ), hy⟩)
    exact (contMDiffOn_const (c := EuclideanSpace.proj i)).clm_apply
      (hs.clm_apply (contMDiffOn_const (c := EuclideanSpace.proj d)))
  have hW (i : Fin n) (A B C : (y : M) → TangentSpace (𝓡 n) y)
      (hA : S A) (hB : S B) (hC : S C) : S (W i A B C) :=
    ContMDiffOn.sum_section fun d _ =>
      (hainv i d).smul_section (hK (E d) A B C (hE d) hA hB hC)
  intro z hz l j k m
  let x := c.symm z
  have hx : x ∈ e.baseSet := by
    simpa only [e, TangentBundle.trivializationAt_baseSet] using c.map_target hz
  obtain ⟨TK, hTK⟩ := exists_curvatureOnFields_derivative_quadrilinearMap D x
  let TW (i : Fin n) := ∑ d : Fin n, a x i d • TK (E d x)
  have hTW (i : Fin n) (A B C : (y : M) → TangentSpace (𝓡 n) y)
      (hA : S A) (hB : S B) (hC : S C) : W i A B C x = TW i (A x) (B x) (C x) := by
    simp only [W, TW, LinearMap.sum_apply, LinearMap.smul_apply]
    apply Finset.sum_congr rfl
    intro d _
    rw [hTK e.open_baseSet (E d) A B C (hE d) hA hB hC hx]
  have hrec (Y : (y : M) → TangentSpace (𝓡 n) y) :
      Y x = ∑ p, theta p x (Y x) • E p x :=
    e.eq_sum_localFrameCoeff_smul (I := 𝓡 n) (b := b) hx
  have hin1 (i : Fin n) :
      theta l x (W i (N (E i) (E j)) (E k) (E m) x) =
        ∑ p, Gamma x i j p * v z i l p k m := by
    rw [hTW i _ _ _ (hN _ _ (hE i) (hE j)) (hE k) (hE m), hrec (N (E i) (E j))]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro p _
    rw [← hTW i _ _ _ (hE p) (hE k) (hE m)]
  have hin2 (i : Fin n) :
      theta l x (W i (E j) (N (E i) (E k)) (E m) x) =
        ∑ p, Gamma x i k p * v z i l j p m := by
    rw [hTW i _ _ _ (hE j) (hN _ _ (hE i) (hE k)) (hE m), hrec (N (E i) (E k))]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro p _
    rw [← hTW i _ _ _ (hE j) (hE p) (hE m)]
  have hin3 (i : Fin n) :
      theta l x (W i (E j) (E k) (N (E i) (E m)) x) =
        ∑ p, Gamma x i m p * v z i l j k p := by
    rw [hTW i _ _ _ (hE j) (hE k) (hN _ _ (hE i) (hE m)), hrec (N (E i) (E m))]
    simp only [map_sum, map_smul, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro p _
    rw [← hTW i _ _ _ (hE j) (hE k) (hE p)]
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
  have hout (i : Fin n) :
      theta l x (N (E i) (W i (E j) (E k) (E m)) x) =
        fderiv ℝ (fun w => v w i l j k m) z (EuclideanSpace.single i 1) +
          ∑ p, Gamma x i p l * v z i p j k m := by
    have hh := localFrame_covariant_derivative_coordinate D x0 (W i (E j) (E k) (E m))
      (hW i _ _ _ (hE j) (hE k) (hE m)) hx i l
    change theta l x (N (E i) (W i (E j) (E k) (E m)) x) =
      mvfderiv (𝓡 n) (fun y => theta l y (W i (E j) (E k) (E m) y)) x (E i x) +
        ∑ p, Gamma x i p l * theta p x (W i (E j) (E k) (E m) x) at hh
    exact hh.trans (congrArg (fun r : ℝ => r +
      ∑ p, Gamma x i p l * theta p x (W i (E j) (E k) (E m) x))
        (hchart _ (contMDiffOn_localFrameCoeff b e.open_baseSet subset_rfl
          (hW i _ _ _ (hE j) (hE k) (hE m)) l) i))
  have hraised (i : Fin n) :
      theta l x (∑ p, Gamma x i p i • W p (E j) (E k) (E m) x) =
        ∑ p, Gamma x i p i * v z p l j k m := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro p _
    rw [map_smul]
    rfl
  change theta l x (∑ i, (N (E i) (W i (E j) (E k) (E m)) x -
    W i (N (E i) (E j)) (E k) (E m) x - W i (E j) (N (E i) (E k)) (E m) x -
    W i (E j) (E k) (N (E i) (E m)) x +
    ∑ p, Gamma x i p i • W p (E j) (E k) (E m) x)) =
      ∑ i, (fderiv ℝ (fun w => v w i l j k m) z (EuclideanSpace.single i 1) +
        ∑ p, (Gamma x i p i * v z p l j k m +
          Gamma x i p l * v z i p j k m - Gamma x i j p * v z i l p k m -
          Gamma x i k p * v z i l j p m - Gamma x i m p * v z i l j k p))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_add, map_sub, map_sub, map_sub, hout i, hin1 i, hin2 i, hin3 i, hraised i]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring

theorem curvature_covariant_derivative_coordinates
    {g : RiemannianMetric n M} (D : LeviCivitaData g) (x0 : M) :
    let V := EuclideanSpace ℝ (Fin n)
    let c := chartAt V x0
    let e := trivializationAt V (TangentSpace (𝓡 n)) x0
    let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    let E := e.localFrame b
    let theta := e.localFrameCoeff (𝓡 n) b
    let N := fun (P Q : (y : M) → TangentSpace (𝓡 n) y) (y : M) =>
      D.connection Q y (P y)
    let R := fun (A B C : (y : M) → TangentSpace (𝓡 n) y) (y : M) =>
      D.curvatureOnFields A B C y
    let K := fun (P A B C : (y : M) → TangentSpace (𝓡 n) y) (y : M) =>
      N P (R A B C) y - R (N P A) B C y -
        R A (N P B) C y - R A B (N P C) y
    let Gamma := fun (y : M) (i j l : Fin n) => theta l y (N (E i) (E j) y)
    let rho := fun (z : V) (l j k m : Fin n) =>
      theta l (c.symm z) (R (E j) (E k) (E m) (c.symm z))
    ∀ z ∈ c.target, ∀ d l j k m : Fin n,
      let x := c.symm z
      theta l x (K (E d) (E j) (E k) (E m) x) =
        fderiv ℝ (fun w => rho w l j k m) z (EuclideanSpace.single d 1) +
          ∑ p, (Gamma x d p l * rho z p j k m - Gamma x d j p * rho z l p k m -
            Gamma x d k p * rho z l j p m - Gamma x d m p * rho z l j k p) := by
  classical
  dsimp only
  let V := EuclideanSpace ℝ (Fin n)
  let c := chartAt V x0
  let e := trivializationAt V (TangentSpace (𝓡 n)) x0
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let E := e.localFrame b
  let theta := e.localFrameCoeff (𝓡 n) b
  let N := fun (P Q : (y : M) → TangentSpace (𝓡 n) y) (y : M) =>
    D.connection Q y (P y)
  let R := fun (A B C : (y : M) → TangentSpace (𝓡 n) y) (y : M) =>
    D.curvatureOnFields A B C y
  let K := fun (P A B C : (y : M) → TangentSpace (𝓡 n) y) (y : M) =>
    N P (R A B C) y - R (N P A) B C y -
      R A (N P B) C y - R A B (N P C) y
  let Gamma := fun (y : M) (i j l : Fin n) => theta l y (N (E i) (E j) y)
  let rho := fun (z : V) (l j k m : Fin n) =>
    theta l (c.symm z) (R (E j) (E k) (E m) (c.symm z))
  let S := fun Y : (y : M) → TangentSpace (𝓡 n) y =>
    ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% Y) e.baseSet
  have hE (i : Fin n) : S (E i) :=
    e.contMDiffOn_localFrame_baseSet (I := 𝓡 n) ∞ b i
  have hN (P Q : (y : M) → TangentSpace (𝓡 n) y)
      (hP : S P) (hQ : S Q) : S (N P Q) :=
    D.contMDiffOn_connection_apply e.open_baseSet P Q hP hQ
  letI : IsManifold (𝓡 n) (∞ + 1) M := by
    simpa using (inferInstance : IsManifold (𝓡 n) ∞ M)
  letI : IsManifold (𝓡 n) (minSmoothness ℝ 2) M :=
    IsManifold.of_le (n := ∞) (by
      simpa only [minSmoothness_of_isRCLikeNormedField] using
        (ENat.LEInfty.out (m := (2 : ℕ∞ω))))
  have hR (A B C : (y : M) → TangentSpace (𝓡 n) y)
      (hA : S A) (hB : S B) (hC : S C) : S (R A B C) := by
    have hbr : S (VectorField.mlieBracket (𝓡 n) A B) := by
      intro y hy
      exact ((hA.contMDiffAt (e.open_baseSet.mem_nhds hy)).mlieBracket_vectorField
        (hB.contMDiffAt (e.open_baseSet.mem_nhds hy)) (m := ⊤) (n := ⊤)
        (by simp)).contMDiffWithinAt
    exact ((hN A _ hA (hN B C hB hC)).sub_section
      (hN B _ hB (hN A C hA hC))).sub_section (hN _ C hbr hC)
  intro z hz d l j k m
  let x := c.symm z
  have hx : x ∈ e.baseSet := by
    simpa only [e, TangentBundle.trivializationAt_baseSet] using c.map_target hz
  obtain ⟨TR, hTR⟩ := exists_curvature_trilinearMap D x
  have heval (A B C : (y : M) → TangentSpace (𝓡 n) y)
      (hA : S A) (hB : S B) (hC : S C) : R A B C x = TR (A x) (B x) (C x) :=
    ((hTR (A x) (B x) (C x)).trans
      (curvature_eq_curvatureOnFields D e.open_baseSet A B C hA hB hC hx)).symm
  have hrec (Y : (y : M) → TangentSpace (𝓡 n) y) :
      Y x = ∑ p, theta p x (Y x) • E p x :=
    e.eq_sum_localFrameCoeff_smul (I := 𝓡 n) (b := b) hx
  have hin1 : theta l x (R (N (E d) (E j)) (E k) (E m) x) =
      ∑ p, Gamma x d j p * rho z l p k m := by
    rw [heval _ _ _ (hN _ _ (hE d) (hE j)) (hE k) (hE m), hrec (N (E d) (E j))]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro p _
    rw [← heval _ _ _ (hE p) (hE k) (hE m)]
  have hin2 : theta l x (R (E j) (N (E d) (E k)) (E m) x) =
      ∑ p, Gamma x d k p * rho z l j p m := by
    rw [heval _ _ _ (hE j) (hN _ _ (hE d) (hE k)) (hE m), hrec (N (E d) (E k))]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro p _
    rw [← heval _ _ _ (hE j) (hE p) (hE m)]
  have hin3 : theta l x (R (E j) (E k) (N (E d) (E m)) x) =
      ∑ p, Gamma x d m p * rho z l j k p := by
    rw [heval _ _ _ (hE j) (hE k) (hN _ _ (hE d) (hE m)), hrec (N (E d) (E m))]
    simp only [map_sum, map_smul, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro p _
    rw [← heval _ _ _ (hE j) (hE k) (hE p)]
  have hchart (f : M → ℝ) (hf : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f e.baseSet) :
      mvfderiv (𝓡 n) f x (E d x) =
        fderiv ℝ (fun w => f (c.symm w)) z (EuclideanSpace.single d 1) := by
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
    have hframe : E d x = e.symmL ℝ x (EuclideanSpace.single d 1) := by
      calc
        E d x = e.basisAt b hx d := e.localFrame_apply_of_mem_baseSet b hx
        _ = e.symm x (EuclideanSpace.single d 1) := by
          simp only [Trivialization.basisAt, Module.Basis.map_apply, b,
            OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
            Trivialization.linearEquivAt_symm_apply]
        _ = e.symmL ℝ x (EuclideanSpace.single d 1) := (e.symmL_apply hx _).symm
    have hfd : fderiv ℝ (fun w => f (c.symm w)) z (EuclideanSpace.single d 1) =
        mvfderiv (𝓡 n) f x (e.symmL ℝ x (EuclideanSpace.single d 1)) := by
      rw [← mfderiv_eq_fderiv]
      change mvfderiv 𝓘(ℝ, V) (f ∘ c.symm) z (EuclideanSpace.single d 1) = _
      have hff : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f (c.symm z) :=
        (hf.contMDiffAt (e.open_baseSet.mem_nhds hx)).mdifferentiableAt (by simp)
      rw [mvfderiv_comp_apply z hff hcs (EuclideanSpace.single d 1), ← he]
      rfl
    exact (congrArg (mvfderiv (𝓡 n) f x) hframe).trans hfd.symm
  have hout : theta l x (N (E d) (R (E j) (E k) (E m)) x) =
      fderiv ℝ (fun w => rho w l j k m) z (EuclideanSpace.single d 1) +
        ∑ p, Gamma x d p l * rho z p j k m := by
    have hh := localFrame_covariant_derivative_coordinate D x0 (R (E j) (E k) (E m))
      (hR _ _ _ (hE j) (hE k) (hE m)) hx d l
    change theta l x (N (E d) (R (E j) (E k) (E m)) x) =
      mvfderiv (𝓡 n) (fun y => theta l y (R (E j) (E k) (E m) y)) x (E d x) +
        ∑ p, Gamma x d p l * theta p x (R (E j) (E k) (E m) x) at hh
    exact hh.trans (congrArg (fun r : ℝ => r +
      ∑ p, Gamma x d p l * theta p x (R (E j) (E k) (E m) x))
        (hchart _ (contMDiffOn_localFrameCoeff b e.open_baseSet subset_rfl
          (hR _ _ _ (hE j) (hE k) (hE m)) l)))
  change theta l x (N (E d) (R (E j) (E k) (E m)) x -
    R (N (E d) (E j)) (E k) (E m) x - R (E j) (N (E d) (E k)) (E m) x -
    R (E j) (E k) (N (E d) (E m)) x) =
      fderiv ℝ (fun w => rho w l j k m) z (EuclideanSpace.single d 1) +
        ∑ p, (Gamma x d p l * rho z p j k m - Gamma x d j p * rho z l p k m -
          Gamma x d k p * rho z l j p m - Gamma x d m p * rho z l j k p)
  rw [map_sub, map_sub, map_sub, hout, hin1, hin2, hin3]
  simp only [Finset.sum_sub_distrib]
  ring

set_option synthInstance.maxHeartbeats 200000 in

theorem curvature_bundle_coordinate_expand
    {d : ℕ} :
    let V := EuclideanSpace ℝ (Fin n)
    letI : NormedAddCommGroup (V →L[ℝ] V) := inferInstance
    letI : NormedSpace ℝ (V →L[ℝ] V) := inferInstance
    letI : NormedAddCommGroup (V →L[ℝ] V →L[ℝ] V) := inferInstance
    letI : NormedSpace ℝ (V →L[ℝ] V →L[ℝ] V) := inferInstance
    ∀ (qS : (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) ≃L[ℝ]
        EuclideanSpace ℝ (Fin d)) (x0 : M),
    let V := EuclideanSpace ℝ (Fin n)
    let e := trivializationAt V (TangentSpace (𝓡 n)) x0
    let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    let E := e.localFrame b
    let theta := e.localFrameCoeff (𝓡 n) b
    let FS := V →L[ℝ] V →L[ℝ] V →L[ℝ] V
    let BS := fun x : M => TangentSpace (𝓡 n) x →L[ℝ]
      TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x
    let eS := trivializationAt FS BS x0
    let B : Fin n → Fin n → Fin n → Fin n → FS := fun l j k m => (EuclideanSpace.proj j).smulRight
      ((EuclideanSpace.proj k).smulRight ((EuclideanSpace.proj m).smulRight
        (EuclideanSpace.single l (1 : ℝ))))
    ∀ x ∈ e.baseSet, ∀ T : BS x, ∀ α : Fin d,
      qS ((eS (TotalSpace.mk' FS x T)).2) α =
        ∑ l, ∑ j, ∑ k, ∑ m, qS (B l j k m) α *
          theta l x (T (E j x) (E k x) (E m x)) := by
  classical
  let V := EuclideanSpace ℝ (Fin n)
  let : NormedAddCommGroup (V →L[ℝ] V) := inferInstance
  let : NormedSpace ℝ (V →L[ℝ] V) := inferInstance
  let : NormedAddCommGroup (V →L[ℝ] V →L[ℝ] V) := inferInstance
  let : NormedSpace ℝ (V →L[ℝ] V →L[ℝ] V) := inferInstance
  dsimp only
  intro qS x0
  let FS := V →L[ℝ] V →L[ℝ] V →L[ℝ] V
  let BS := fun x : M => TangentSpace (𝓡 n) x →L[ℝ]
    TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x
  let e := trivializationAt V (TangentSpace (𝓡 n)) x0
  let eS := trivializationAt FS BS x0
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let E := e.localFrame b
  let theta := e.localFrameCoeff (𝓡 n) b
  let B : Fin n → Fin n → Fin n → Fin n → FS := fun l j k m => (EuclideanSpace.proj j).smulRight
    ((EuclideanSpace.proj k).smulRight ((EuclideanSpace.proj m).smulRight
      (EuclideanSpace.single l (1 : ℝ))))
  intro x hx T α
  let T0 : FS := (eS (TotalSpace.mk' FS x T)).2
  have hBeval (l j k m : Fin n) (u v w : V) :
      B l j k m u v w = u j • v k • w m • EuclideanSpace.single l (1 : ℝ) := rfl
  have hTensor : T0 = ∑ l : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ m : Fin n,
      (T0 (EuclideanSpace.single j 1) (EuclideanSpace.single k 1)
        (EuclideanSpace.single m 1)) l • B l j k m := by
    apply ContinuousLinearMap.coe_injective
    apply b.ext
    intro j0
    apply ContinuousLinearMap.coe_injective
    apply b.ext
    intro k0
    apply ContinuousLinearMap.coe_injective
    apply b.ext
    intro m0
    ext l0
    change (EuclideanSpace.proj l0) (T0 (b j0) (b k0) (b m0)) = (EuclideanSpace.proj l0)
      ((∑ l : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ m : Fin n,
        (T0 (EuclideanSpace.single j 1) (EuclideanSpace.single k 1)
          (EuclideanSpace.single m 1)) l • B l j k m) (b j0) (b k0) (b m0))
    simp only [b, OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
      sum_apply, smul_apply, map_sum, map_smul, hBeval, smul_eq_mul]
    simp [EuclideanSpace.coe_proj, EuclideanSpace.single, PiLp.single_apply,
      mul_ite, ite_mul]
  have hmodel (u v w : V) : T0 u v w =
      e.linearMapAt ℝ x (T (e.symmL ℝ x u) (e.symmL ℝ x v) (e.symmL ℝ x w)) := by
    have hxhom : x ∈ (trivializationAt (V →L[ℝ] V)
        (fun y : M => TangentSpace (𝓡 n) y →L[ℝ] TangentSpace (𝓡 n) y) x0).baseSet := by
      rw [hom_trivializationAt_baseSet]
      exact ⟨hx, hx⟩
    dsimp only [T0, eS]
    rw [hom_trivializationAt_apply]
    rw [inCoordinates_apply_eq₂
      (F₁ := V) (F₂ := V) (F₃ := V →L[ℝ] V)
      (E₁ := TangentSpace (𝓡 n)) (E₂ := TangentSpace (𝓡 n))
      (E₃ := fun y : M => TangentSpace (𝓡 n) y →L[ℝ] TangentSpace (𝓡 n) y)
      hx hx hxhom]
    rw [Trivialization.linearMapAt_apply, if_pos hxhom, hom_trivializationAt_apply]
    change ContinuousLinearMap.inCoordinates V (TangentSpace (𝓡 n)) V
      (TangentSpace (𝓡 n)) x0 x x0 x (T (e.symm x u) (e.symm x v)) w = _
    simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply,
      Trivialization.continuousLinearMapAt_apply]
    rw [Trivialization.symmL_apply (R := ℝ) e hx u,
      Trivialization.symmL_apply (R := ℝ) e hx v,
      Trivialization.symmL_apply (R := ℝ) e hx w]
  have hframe (i : Fin n) : E i x = e.symmL ℝ x (EuclideanSpace.single i 1) := by
    calc
      E i x = e.basisAt b hx i := e.localFrame_apply_of_mem_baseSet b hx
      _ = e.symm x (EuclideanSpace.single i 1) := by
        simp only [Trivialization.basisAt, Module.Basis.map_apply, b,
          OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
          Trivialization.linearEquivAt_symm_apply]
      _ = e.symmL ℝ x (EuclideanSpace.single i 1) := (e.symmL_apply hx _).symm
  have htheta (i : Fin n) (v : TangentSpace (𝓡 n) x) :
      theta i x v = (e.linearMapAt ℝ x v) i := by
    have hh := e.localFrameCoeff_apply_of_mem_baseSet (I := 𝓡 n) b hx
      (FiberBundle.extend V v) i
    rw [FiberBundle.extend_apply_self] at hh
    change theta i x v = _ at hh
    rw [hh]
    simp only [Trivialization.basisAt, Module.Basis.map_repr, LinearEquiv.symm_symm,
      LinearEquiv.trans_apply, b, OrthonormalBasis.coe_toBasis_repr_apply,
      Trivialization.linearEquivAt_apply]
    rw [e.linearMapAt_def_of_mem hx]
    rfl
  change qS T0 α = ∑ l, ∑ j, ∑ k, ∑ m,
    qS (B l j k m) α * theta l x (T (E j x) (E k x) (E m x))
  have hq := congrArg (fun U : FS => (EuclideanSpace.proj α) (qS U)) hTensor
  simp only [map_sum, map_smul, smul_eq_mul, EuclideanSpace.coe_proj] at hq
  rw [hq]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro m _
  rw [hmodel, hframe j, hframe k, hframe m, htheta]
  exact mul_comm _ _

set_option synthInstance.maxHeartbeats 200000 in

theorem hasDerivAt_curvature_bundle_coordinate_of_frame
    {d : ℕ} :
    let V := EuclideanSpace ℝ (Fin n)
    letI : NormedAddCommGroup (V →L[ℝ] V) := inferInstance
    letI : NormedSpace ℝ (V →L[ℝ] V) := inferInstance
    letI : NormedAddCommGroup (V →L[ℝ] V →L[ℝ] V) := inferInstance
    letI : NormedSpace ℝ (V →L[ℝ] V →L[ℝ] V) := inferInstance
    ∀ (qS : (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) ≃L[ℝ]
        EuclideanSpace ℝ (Fin d)) (x0 : M),
    let V := EuclideanSpace ℝ (Fin n)
    let e := trivializationAt V (TangentSpace (𝓡 n)) x0
    let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    let E := e.localFrame b
    let theta := e.localFrameCoeff (𝓡 n) b
    let FS := V →L[ℝ] V →L[ℝ] V →L[ℝ] V
    let BS := fun x : M => TangentSpace (𝓡 n) x →L[ℝ]
      TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x
    let eS := trivializationAt FS BS x0
    let B : Fin n → Fin n → Fin n → Fin n → FS := fun l j k m => (EuclideanSpace.proj j).smulRight
      ((EuclideanSpace.proj k).smulRight ((EuclideanSpace.proj m).smulRight
        (EuclideanSpace.single l (1 : ℝ))))
    ∀ x ∈ e.baseSet, ∀ (T : ℝ → BS x) (t : ℝ) (rate : Fin n → Fin n → Fin n → Fin n → ℝ),
      (∀ l j k m, HasDerivAt
        (fun s => theta l x (T s (E j x) (E k x) (E m x))) (rate l j k m) t) →
      ∀ α : Fin d, HasDerivAt (fun s => qS ((eS (TotalSpace.mk' FS x (T s))).2) α)
        (∑ l, ∑ j, ∑ k, ∑ m, qS (B l j k m) α * rate l j k m) t := by
  classical
  let V := EuclideanSpace ℝ (Fin n)
  let : NormedAddCommGroup (V →L[ℝ] V) := inferInstance
  let : NormedSpace ℝ (V →L[ℝ] V) := inferInstance
  let : NormedAddCommGroup (V →L[ℝ] V →L[ℝ] V) := inferInstance
  let : NormedSpace ℝ (V →L[ℝ] V →L[ℝ] V) := inferInstance
  dsimp only
  intro qS x0
  let e := trivializationAt V (TangentSpace (𝓡 n)) x0
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let E := e.localFrame b
  let theta := e.localFrameCoeff (𝓡 n) b
  let FS := V →L[ℝ] V →L[ℝ] V →L[ℝ] V
  let BS := fun x : M => TangentSpace (𝓡 n) x →L[ℝ]
    TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x
  let eS := trivializationAt FS BS x0
  let B : Fin n → Fin n → Fin n → Fin n → FS := fun l j k m => (EuclideanSpace.proj j).smulRight
    ((EuclideanSpace.proj k).smulRight ((EuclideanSpace.proj m).smulRight
      (EuclideanSpace.single l (1 : ℝ))))
  intro x hx T t rate hrate α
  have hs := HasDerivAt.sum (u := Finset.univ) (fun l _ =>
    HasDerivAt.sum (u := Finset.univ) (fun j _ =>
      HasDerivAt.sum (u := Finset.univ) (fun k _ =>
        HasDerivAt.sum (u := Finset.univ) (fun m _ =>
          (hrate l j k m).const_mul (qS (B l j k m) α)))))
  have hsumfun :
      (fun s => ∑ l, ∑ j, ∑ k, ∑ m, qS (B l j k m) α *
        theta l x (T s (E j x) (E k x) (E m x))) =
      (∑ l, ∑ j, ∑ k, ∑ m, fun s => qS (B l j k m) α *
        theta l x (T s (E j x) (E k x) (E m x))) := by
    funext s
    simp only [Finset.sum_apply]
  rw [← hsumfun] at hs
  exact hs.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s =>
    curvature_bundle_coordinate_expand qS x0 x hx (T s) α)

end PoincareConjecture.Proofs.M03
